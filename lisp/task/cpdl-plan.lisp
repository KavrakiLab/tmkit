(in-package :tmsmt)

(defparameter +cpd-transition-name+ 'transition)

(declaim (ftype (function (constrained-domain list fixnum) string)
                cpd-mangle-fluent))
(defun cpd-mangle-fluent (cpd fluent i)
  "Name-mangle an expression into an unrolled variable at step i.
EXP: an s-expression
I: The step to unroll at"
  (let* ((fluent fluent)
         (mangle-cache (constrained-domain-mangle-cache cpd))
         (key (cons i fluent)))
    (declare (dynamic-extent key)
             (type list fluent))
    (or (gethash key mangle-cache)
        (let ((m (format nil "~{~A~^_~}_~D" fluent i))
              (key (copy-list key)))
          (setf (gethash key mangle-cache) m
                (gethash m (constrained-domain-unmangle-cache cpd)) key)
          m))))

(declaim (ftype (function (constrained-domain list fixnum) string)
                cpd-mangle-exp))
(defun cpd-mangle-exp (cpd exp i)
  (apply-rewrite-exp (lambda (exp) (cpd-mangle-fluent cpd exp i))
                     exp))

;; (defun cpd-mangle-exp (exp i)
;;   (apply-rewrite-exp (lambda (exp) (cpd-mangle-fluent cpd exp i))
;;                      exp))

(defun cpd-mangle-transition (cpd exp i)
  (flet ((mangle (thing)
           (destructuring-ecase thing
             ((now arg)
              (cpd-mangle-exp cpd arg i))
             ((next arg)
              (cpd-mangle-exp cpd arg (1+ i))))))
    (apply-rewrite-exp #'mangle exp)))

(defun cpd-unmangle (cpd mangled)
  "Un-mangle a mangled name back to the s-expression."
  (multiple-value-bind (sexp found)
      (gethash mangled (constrained-domain-unmangle-cache cpd))
    ;; We should never try to unmangle something we have not
    ;; previously mangled.
    (assert found)
    sexp))

  ;; (let ((list (ppcre:split "_" mangled)))
  ;;   (cons (parse-integer (lastcar list))
  ;;         (loop for x on list
  ;;            for a = (car x)
  ;;            when (cdr x)
  ;;            collect
;;            a))))

(defun cpd-plan-options (&key
                           (max-steps 10)
                           (trace nil) )
  "Construct options for constraint-based planner.

MAX-STEPS: maximum number of steps to plan over, i.e., the bound or horizon.
TRACE: Output stream to write generate SMTLib statements (for debugging)."
  `((:max-steps . ,max-steps)
    (:trace . ,trace)))

(defun cpd-plan-option (options thing)
  "Get a planner option."
  (cdr (assoc thing options)))

(defun cpd-define-transition (domain)
  (let* ((f (cons 'and (constrained-domain-transition-clauses domain)))
         (nows (map-cpd-fluent-types 'list (lambda (f type)
                                             `(,(fluent-now f)  ,type))
                                     domain))
         (nexts (map-cpd-fluent-types 'list (lambda (f type)
                                              `(,(fluent-next f) ,type))
                                      domain))
         (args (append nows nexts)))
    (values
     `(define-fun ,+cpd-transition-name+ ,args bool
                  ,f)
     args)))



;;; Encoding functions
(defun cpd-smt-encode-fluents (function domain step)
  "Encode the new fluents for STEP."
  (map-cpd-fluent-types nil
                        (lambda (name type)
                          (funcall function
                                   `(declare-const ,(cpd-mangle-fluent domain name step)
                                                   ,type)))
                        domain))

(defun cpd-smt-encode-start (function domain)
  "Encode the start state"
  (map-cpd-start nil
                 (lambda (name value)
                   (let ((name (cpd-mangle-fluent domain name 0)))
                     (funcall function
                              (case value
                                (true `(assert ,name))
                                (false `(assert (not ,name)))
                                (otherwise `(assert (= ,name ,value)))))))
                 domain))

(defun cpd-smt-encode-goal (function domain step)
  "Encode the goal state at STEP"
  (map-cpd-goals nil
                 (lambda (c)
                   (check-type c list)
                   (funcall function `(assert ,(cpd-mangle-exp domain c step))))
                 domain))

(defun cpd-smt-encode-transition (function domain args step)
  "Encode the call to transition function at STEP"
  (funcall function
           `(assert (transition ,@(map 'list (lambda (a)
                                               (cpd-mangle-transition domain (car a) step))
                                       args)))))

(defun cpd-smt-simple (domain steps)
  "Return the SMT encoding of the domain for STEPS count."
  (with-collected (add)
    ;; fluents
    (dotimes (i (1+ steps))
      (cpd-smt-encode-fluents #'add domain i))

    ;; start
    (cpd-smt-encode-start #'add domain)

    ;; goal
    (cpd-smt-encode-goal #'add domain steps)

    ;; transitions
    (multiple-value-bind (fun args)
        (cpd-define-transition domain)
      (add fun)
      (dotimes (i steps)
        (cpd-smt-encode-transition #'add domain args i)))

    ;; check
    (add `(check-sat))))

(defun cpd-actions (alist)
  (let* ((selected (loop for (a . b) in alist
                      when (smt-true-p b)
                      collect a))
         (sorted (sort selected #'< :key #'car)))
    (map 'list #'cdr sorted)))


(defun cpd-plan-result (domain solver steps)
  (let* ((symbols (with-collected (add)
                    (dotimes (i steps)
                      (map nil
                           (lambda (f)
                             (add (cpd-mangle-exp domain f i)))
                           (constrained-domain-outputs domain)))))
         (values (z3::smt-eval solver `(get-value ,symbols))))
    (loop for (a . b) in values
       collect (cons (cpd-unmangle domain a) b))))



(defun cpd-plan (domain &optional options)
  (let* ((options (or options (cpd-plan-options)))
         (max-steps (cpd-plan-option options :max-steps))
         (trace (cpd-plan-option options :trace)))
    (labels ((rec (steps)
               (format *error-output* "~&Unrolling for step ~D...~%" steps)
               (z3::with-solver (solver :trace trace)
                 (multiple-value-bind (is-sat solver)
                     (z3::smt-prog (cpd-smt-simple domain steps)
                                   :solver solver)
                   (cond
                     ((eq is-sat :sat)
                      (values
                       (cpd-plan-result domain solver steps)
                       t))
                     ((< steps max-steps)
                      (rec (1+ steps)))
                     (t (values nil nil)))))))
      (rec 1))))







;; (defstruct cpd-planner
;;   domain
;;   solver
;;   transition-args)

;; (defun cpd-smt-init (function domain &options options)
;;   (declare (ignore options))
;;   ;; State Space
;;   ;; Start
;;   ;; Transition Function

;;   )


;; (defun cpd-smt-step (function domain k &options options)
;;   ;; Declare Flents
;;   ;; Push
;;   ;; Assert Goal
;;   ;;
;;   )

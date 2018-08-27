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



(defun cpd-plan-simple (domain &optional options)
  "Driver function for a non-incremental planner."
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







(defstruct cpd-planner
  domain
  solver
  transition-args
  options
  eval-function
  k)

(defun cpd-planner-eval (planner stmt)
  (funcall (cpd-planner-eval-function planner) stmt))

(defun cpd-planner-max-steps (planner)
  (cpd-plan-option (cpd-planner-options planner) :max-steps))

(defun cpd-plan-init (domain solver &optional options)
  "Initialize the planner."
  (flet ((add (stmt)
           (z3::smt-eval solver stmt)))

    ;; Step 0 Fluents
    (cpd-smt-encode-fluents #'add domain 0)

    ;; Start
    (cpd-smt-encode-start #'add domain)

    ;; Transition Function
    (multiple-value-bind (fun args)
        (cpd-define-transition domain)
      (add fun)

      ;; Push and Assert Goal
      (funcall #'add '(push 1))
      (cpd-smt-encode-goal #'add domain 0)

      ;; Result
      (make-cpd-planner :domain domain
                        :solver solver
                        :transition-args args
                        :options options
                        :eval-function #'add
                        :k 0))))

(defun cpd-plan-next (planner)
  (let ((k (cpd-planner-k planner))
        (max-steps (cpd-planner-max-steps planner)))
    ;; Check Sat
    (let ((is-sat (cpd-planner-eval planner '(check-sat))))
      (cond
        ((eq is-sat :sat)
         ;; SAT, get result
         (values (cpd-plan-result (cpd-planner-domain planner)
                                  (cpd-planner-solver planner)
                                  k)
                 t
                 planner))
        ((< k max-steps)
         ;; UNSAT: Step
         (incf (cpd-planner-k planner))
         (cpd-plan-step planner))
        ;; Over max steps, fail
        (t (values nil nil planner))))))


(defun cpd-plan-step (planner)
  (let ((k (cpd-planner-k planner))
        (add (cpd-planner-eval-function planner))
        (domain (cpd-planner-domain planner))
        (args (cpd-planner-transition-args planner)))
    (format *error-output* "~&Unrolling at step ~D...~%" k)

    ;; Pop, declare fluents and assert transition
    (funcall add '(pop 1))
    (cpd-smt-encode-fluents add domain k)
    (cpd-smt-encode-transition add domain args (1- k))

    ;; Push and assert goal
    (funcall add '(push 1))
    (cpd-smt-encode-goal add domain k)

    ;; Recurse
    (cpd-plan-next planner)))


(defun cpd-plan (domain &optional options)
  (let* ((options (or options (cpd-plan-options)))
         (trace (cpd-plan-option options :trace)))
    (z3::with-solver (solver :trace trace)
      (let ((planner (cpd-plan-init domain solver options)))
        (cpd-plan-next planner)))))

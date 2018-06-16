(in-package :tmsmt)

(declaim (ftype (function (constrained-domain symbol fixnum) string)))
(defun cpd-mangle-fluent (cpd fluent i)
  "Name-mangle an expression into an unrolled variable at step i.
EXP: an s-expression
I: The step to unroll at"
  (let* ((fluent (ensure-list fluent))
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

(declaim (ftype (function (constrained-domain list fixnum) string)))
(defun cpd-mangle-exp (cpd exp i)
  (apply-rewrite-exp (lambda (exp) (cpd-mangle-fluent cpd exp i))
                     exp))

;; (defun cpd-mangle-exp (exp i)
;;   (apply-rewrite-exp (lambda (exp) (cpd-mangle-fluent cpd exp i))
;;                      exp))

(defun cpd-mangle-transition (cpd exp i)
  (flet ((mangle (thing)
           (destructuring-ecase (ensure-list thing)
             ((now arg)
              (cpd-mangle-exp cpd arg i))
             ((next arg)
              (cpd-mangle-exp cpd arg (1+ i))))))
    (apply-rewrite-exp #'mangle exp)))

(defun cpd-unmangle (cpd mangled)
  "Un-mangle a mangled name back to the s-expression."
  (gethash mangled (constrained-domain-unmangle-cache cpd)))
  ;; (let ((list (ppcre:split "_" mangled)))
  ;;   (cons (parse-integer (lastcar list))
  ;;         (loop for x on list
  ;;            for a = (car x)
  ;;            when (cdr x)
  ;;            collect
  ;;            a))))

(defun cpd-plan-options (&key (max-steps 10))
  `((:max-steps . ,max-steps)))

(defun cpd-define-transition (domain)
  (let* ((f (cons 'and (constrained-domain-transition-clauses domain)))
         (nows (map-cpd-fluents 'list (lambda (f type)
                                        `(,(fluent-now f)  ,type))
                                domain))
         (nexts (map-cpd-fluents 'list (lambda (f type)
                                         `(,(fluent-next f) ,type))
                                 domain))
         (args (append nows nexts)))
    (values
     `(define-fun transition ,args bool
                  ,f)
     args)))


(defun cpd-smt (domain steps)
  (with-collected (add)
    ;; fluents
    (dotimes (i (1+ steps))
      (map-cpd-fluents nil
                       (lambda (name type)
                         (add
                          `(declare-const ,(cpd-mangle-fluent domain name i) ,type)))
                       domain))


    ;; start
    (map-cpd-start nil
                   (lambda (name value)
                     (let ((name (cpd-mangle-fluent domain name 0)))
                       (case value
                         (true (add `(assert ,name)))
                         (false (add `(assert (not ,name))))
                         (otherwise (add `(assert (= ,name ,value)))))))
                   domain)

    ;; goal
    (map-cpd-goals nil
                   (lambda (c)
                     (check-type c list)
                     (add `(assert ,(cpd-mangle-exp domain c steps))))
                   domain)

    ;; transitions
    (multiple-value-bind (fun args)
        (cpd-define-transition domain)
      (add fun)
      (dotimes (i steps)
        (add `(assert (transition ,@(map 'list (lambda (a)
                                                 (cpd-mangle-transition domain (car a) i))
                                         args))))))

    ;; (let ((f (cons 'and (constrained-domain-transition-clauses domain))))
    ;;   (dotimes (i steps)
    ;;     (add `(assert ,(cpd-mangle-transition domain f i)))))

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
         (values (z3::smt-values solver symbols)))
    (loop for (a . b) in values
       collect (cons (cpd-unmangle domain a) b))))

(defun cpd-plan (domain &optional options)
  (let* ((options (or options (cpd-plan-options)))
         (max-steps (cdr (assoc :max-steps options))))
    (labels ((rec (steps)
               (format *error-output* "~&Unrolling for step ~D...~%" steps)
               (z3::with-solver (solver)
                 (multiple-value-bind (is-sat solver)
                     (z3::smt-prog (cpd-smt domain steps)
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

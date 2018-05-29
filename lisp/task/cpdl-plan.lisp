(in-package :tmsmt)

(defun cpd-mangle-fluent (fluent i)
  "Name-mangle an expression into an unrolled variable at step i.
EXP: an s-expression
I: The step to unroll at"
  (format nil "~{~A~^_~}_~D" fluent i))

(defun cpd-mangle-exp (exp i)
  (apply-rewrite-exp (lambda (exp) (cpd-mangle exp i))
                     exp))

(defun cpd-mangle-transition (exp i)
  (flet ((mangle (thing)
           (destructuring-ecase thing
             ((now arg)
              (cpd-mangle-exp arg i))
             ((next arg)
              (cpd-mangle-exp arg (1+ i))))))
    (apply-rewrite-exp #'mangle exp)))

(defun cpd-unmangle (mangled)
  "Un-mangle a mangled name back to the s-expression."
  (let ((list (ppcre:split "_" mangled)))
    (cons (parse-integer (lastcar list))
          (loop for x on list
             for a = (car x)
             when (cdr x)
             collect
             a))))

(defun cpd-plan-options (&key (max-steps 10))
  `((:max-steps . ,max-steps)))

(defun cpd-smt (domain steps)
  (with-collected (add)
    ;; fluents
    (dotimes (i (1+ steps))
      (map-cpd-fluents nil
                       (lambda (name type)
                         (add
                          `(declare-const ,(cpd-mangle name i) ,type)))
                       domain))


    ;; start
    (map-cpd-start nil
                   (lambda (name value)
                     (let ((name (cpd-mangle name 0)))
                       (case value
                         (true (add `(assert ,name)))
                         (false (add `(assert (not ,name))))
                         (otherwise (add `(assert (= ,name ,value)))))))
                   domain)

    ;; goal
    (map-cpd-goals nil
                   (lambda (c)
                     (add `(assert ,(cpd-mangle-exp c steps))))
                   domain)
    ;; transitions
    (let ((f (cons 'and (constrained-domain-transition-clauses domain))))
      (dotimes (i steps)
        (add `(assert ,(cpd-mangle-transition f i)))))
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
                             (add (cpd-mangle-fluent f i)))
                           (constrained-domain-outputs domain)))))
         (values (z3::smt-values solver symbols)))
    (loop for (a . b) in values
       collect (cons (cpd-unmangle a) b))))

(defun cpd-plan (domain &optional options)
  (let* ((options (or options (cpdl-plan-options)))
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
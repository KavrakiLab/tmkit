(in-package :tmsmt)

(defun rewrite-exp (exp step)
  (destructuring-case exp
    (((and or not) &rest rest)
     (cons (car exp)
           (loop for e in rest collect (rewrite-exp e step))))
    ((t &rest rest) (declare (ignore rest))
     (format-state-variable exp step))))

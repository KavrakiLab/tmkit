(in-package :tmsmt)

(defun pd-cvar (domain var &optional (array "x"))
  (if-let ((i (position var (ground-domain-variables domain) :test #'equal)))
    (rope-parenthesize (rope array "[" i "]"))
    (error "Invalid variable '~A'" var)))

(defun pd-cexp (domain pd-exp)
  (labels ((rec (pe)
             (destructuring-bind (op &rest rest) pe
               (case op
                 ((and or not = ==)
                  (cons op (map 'list #'rec rest)))
                 (otherwise
                  (pd-cvar domain pe))))))
    (rec pd-exp)))

(in-package :tmsmt)

(defun tm-plan-motion-plans (tm-plan)
  (loop for rest = tm-plan then (cddr rest)
     while rest
     collect (car rest)))

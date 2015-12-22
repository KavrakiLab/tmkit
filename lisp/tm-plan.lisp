(in-package :tmsmt)

(defun tm-plan-motion-plans (tm-plan)
  (loop for rest = tm-plan then (cddr rest)
     while rest
     collect (car rest)))

(defun tm-plan-endpoint (tm-plan)
  (loop
     for a = tm-plan then b
     for b = (cddr a)
     while b
     finally (return (motion-plan-endpoint-map (car a)))))

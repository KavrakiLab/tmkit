(in-package :tmsmt)

(defun apply-rewrite-exp (function exp)
  (declare (type function function))
  (etypecase exp
    (atom (funcall function exp))
    (list
     (destructuring-case exp
       (((and or not =) &rest rest)
        (cons (car exp)
              (loop for exp in rest collect (apply-rewrite-exp function exp))))
       ((t &rest rest) (declare (ignore rest))
        (funcall function exp))))))

(defun rewrite-exp (exp step)
  (apply-rewrite-exp (lambda (exp)
                       (format-state-variable exp step))
                     exp))

(defun exp-variable-compare (a b)
  (gsymbol-compare a b))

(defun exp-variables (exp &optional set)
  "Return the set of variables in `EXP'."
  (labels ((rec (vars exp)
             (etypecase exp
               (atom (sycamore:tree-set-insert vars exp))
               (list
                (destructuring-case exp
                  (((and or not) &rest rest)
                   (fold #'rec vars rest))
                  ((t &rest rest) (declare (ignore rest))
                   (sycamore:tree-set-insert vars exp)))))))
    (rec (or set
             (sycamore:make-tree-set #'exp-variable-compare))
         exp)))

(defun exp-list-variables (exps)
  (fold (lambda (set exp)
          (exp-variables exp set))
        (sycamore:make-tree-set #'exp-variable-compare)
        exps))

(defun exp-variables-list (exp)
  (tree-set-list (exp-variables exp)))

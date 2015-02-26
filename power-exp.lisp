(in-package :tmsmt)

(defun decode-exp-power-subsets (exps k assignments)
  (let ((subsets (make-array k :initial-element nil))
        (exps (make-array (length exps) :initial-contents exps)))
    (loop for ((e i j) value) in assignments
       do
         (assert (string= e "E"))
         (assert (>= i 0))
         (assert (< i (length exps)))
         (assert (>= j 0))
         (assert (< j k))
         (ecase value
           (true (push (aref exps i)
                       (aref subsets j)))
           (false)))
    (loop for subset across subsets
       collect
         (cons 'and subset))))



(defun exp-power-subsets (exps k)
  "Return the subsets of the power set of `EXPS' whose conjunction is
 satisfiable."
  (let ((vars (sycamore:tree-set-list (exp-list-variables exps)))
        (n (length exps))
        (code-vars)
        (statements))
    (labels ((stmt (x)
               (push x statements))
             (state-exp (i j)
               (smt-mangle 'e i j))
             (state-var (var j)
               (smt-mangle var j)))
      ;; subset inclusion vars
      (stmt (smt-comment "Subset Inclusion Variables"))
      (dotimes (i n)
        (dotimes (j k)
          (push (state-exp i j) code-vars)))
      (dolist (v code-vars)
        (stmt (smt-declare-fun v () 'bool)))
      ;; subset expression variables
      (stmt (smt-comment "Expression Variables"))
      (dotimes (j k)
        (dolist (var vars)
          (stmt (smt-declare-fun (state-var var j) () 'bool))))
      ;; unique subsets
      (stmt (smt-comment "Unique Subsets"))
      (dotimes (j-1 k)
        (loop for j-2 from (1+ j-1) below k
           do
             (stmt (smt-assert (apply #'smt-or
                                      (map 'list (lambda (var)
                                                   (smt-not (smt-= (state-var var j-1)
                                                                   (state-var var j-2))))
                                           vars))))))
      ;; Valued Subsets
      (stmt (smt-comment "Valued Subsets"))
      (dotimes (j k)
        (stmt (smt-assert (apply #'smt-or (loop for i below n
                                             collect (state-exp i j))))))

      ;; SAT subsets
      (stmt (smt-comment "SAT Subsets"))
      (dotimes (j k)
        (stmt (smt-assert (apply #'smt-and
                                 (loop
                                    for i from 0
                                    for e in exps
                                    collect
                                      (smt-or (smt-not (state-exp i j))
                                              (apply-rewrite-exp (lambda (v) (state-var v j))
                                                                 e)))))))
      )
    (make-smt-problem :statements (reverse statements)
                      :variables code-vars
                      :decode-function (lambda (assignments)
                                         (decode-exp-power-subsets exps k assignments)))))

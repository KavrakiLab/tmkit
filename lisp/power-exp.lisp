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

(defun exp-subset-bitwise-compare (e i j n)
  (let ((e-i (smt-mangle e n i))
        (e-j (smt-mangle e n j)))
    (if (= 0 n)
        (smt-and e-i (smt-not e-j))
        (smt-or  (smt-and e-i (smt-not e-j))
                 (smt-and (smt-= e-i e-j)
                          (exp-subset-bitwise-compare e i j (1- n)))))))

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

      ;; Ordered subsets
      (stmt (smt-comment "Ordered Subsets"))
      (loop
         for j-0 below (1- k)
         for j-1 = (1+ j-0)
         do
           (progn (assert (< j-1 k))
                  (stmt (smt-assert (exp-subset-bitwise-compare 'e j-0 j-1 (1- n))))))

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

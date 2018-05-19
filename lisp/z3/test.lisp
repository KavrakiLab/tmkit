(in-package :cl-user)

(defpackage z3/test
  (:use :cl :alexandria :cffi :smt-symbol :fiveam))


(in-package :z3/test)

(def-suite all-tests
    :description "The master suite of all quasiRPG tests.")

(in-suite all-tests)

(defun test-z3 ()
  (run! 'all-tests))



;;; From: The SMT-LIBv2 Language and Tools: A Tutorial

(defun smtlibtutorial-basic-boolean ()
  (z3::smt-prog
   '((declare-fun p () Bool)
     (assert (and p (not p)))
     (check-sat))))

(defun smtlibtutorial-integer-arithmetic ()
  (z3::smt-prog
   '((declare-fun x () Int)
     (declare-fun y () Int)
     (assert (= (+ x (* 2 y)) 20))
     (assert (= (- x y) 2))
     (check-sat))))

(defun smtlibtutorial-integer-arithmetic2 ()
  (z3::smt-prog
   '((declare-fun x () Int)
     (declare-fun y () Int)
     (assert (= (+ x (* 2 y)) 20))
     (assert (= (- x y) 3))
     (check-sat))))

(test smtlibtutorial-check-sat
  "Test SAT/UNSAT"
  (is (eq :unsat (smtlibtutorial-basic-boolean)))
  (is (eq :sat (smtlibtutorial-integer-arithmetic)))
  (is (eq :unsat (smtlibtutorial-integer-arithmetic2))))


(defun smtlibtutorial-values ()
  (z3::smt-prog
   '((declare-fun x () Int)
     (declare-fun y () Int)
     (assert (= (+ x (* 2 y)) 20))
     (assert (= (- x y) 2))
     (check-sat)
     (get-value (x y)))))

(test smtlibtutorial-get-values
  "Test get values"
  (is-true (let ((r (smtlibtutorial-values)))
             (and (= 8 (cdr (assoc 'x r)))
                  (= 6 (cdr (assoc 'y r)))))))

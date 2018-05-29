(in-package :cl-user)

(require :fiveam)

(defpackage z3/test
  (:use :cl :alexandria :cffi :smt-symbol :fiveam))


(in-package :z3/test)

(def-suite all-tests
    :description "Z3 test suite")

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

(defun smtlibtutorial-scope-0 ()
  (z3::smt-prog
   '((declare-fun x () Int)
     (declare-fun y () Int)
     (assert (= (+ x (* 2 y)) 20))
     (push 1)
     (assert (= (- x y) 2))
     (check-sat))))

(defun smtlibtutorial-scope-1 (solver)
  (z3::smt-prog
   '((pop 1)
     (push 1)
     (assert (= (- x y) 3))
     (check-sat))
   :solver solver))

(defun smtlibtutorial-scope ()
  (multiple-value-bind (result solver)
      (smtlibtutorial-scope-0)
    (print result)
    (smtlibtutorial-scope-1 solver)))

(test smtlibtutorial-scopetest
  "Test push and pop"
  (multiple-value-bind (result-0 solver)
      (smtlibtutorial-scope-0)
    (let ((result-1
           (smtlibtutorial-scope-1 solver)))
      (is (eq :sat result-0))
      (is (eq :unsat result-1)))))


;;; Rise4Fun
;;; https://rise4fun.com/z3/tutorial

(test rise4fun-enum
  (is (eq (z3::smt-prog
           '((declare-enum S a b c)
             (declare-const x S)
             (declare-const y S)
             (declare-const z S)
             (declare-const u S)
             (assert (distinct x y z))
             (check-sat)))
          :sat))
  (is (eq (z3::smt-prog
           '((declare-enum S a b c)
             (declare-const x S)
             (declare-const y S)
             (declare-const z S)
             (declare-const u S)
             (assert (distinct x y z u))
             (check-sat)))
          :unsat)))

(defun rise4fun-enum ()
  (z3::smt-prog
   '((declare-enum S a b c)
     (declare-const x S)
     (declare-const y S)
     (declare-const z S)
     (declare-const u S)
     (assert (distinct x y z u))
     (check-sat)
     ;(get-value (x y))
     )))

(defun rise4fun-predicate ()
  (z3::smt-prog
   `((declare-const a Int)
     (declare-fun f (Int Bool) Int)
     (assert (> a 10))
     (assert (< (f a true) 100))
     (check-sat)
     )))


(test rise4fun-predicate
  (is (eq (rise4fun-predicate)
          :sat)))


(defun rise4fun-define-fun ()
  (z3::smt-prog
   '((declare-const p Bool)
     (declare-const q Bool)
     (declare-const r Bool)
     (define-fun conjecture () Bool
      (=> (and (=> p q) (=> q r))
       (=> p r)))
     (assert (not conjecture))
     (check-sat))))

(defun rise4fun-define-fun-1 ()
  (z3::smt-prog
   '((declare-const p Bool)
     (declare-const q Bool)
     (declare-const r Bool)
     (define-fun conjecture () Bool
      (=> (and (=> p q) (=> q r))
       (=> p r)))
     (assert conjecture)
     (check-sat))))

(test rise4fun-define-fun
  (is (eq (rise4fun-define-fun)
          :unsat))
  (is (eq (rise4fun-define-fun-1)
          :sat)))


(defun rise4fun-demorgan ()
  (z3::smt-prog
   '((declare-const x Bool)
     (declare-const y Bool)
     (define-fun demorgan ((a Bool) (b Bool)) Bool
      (= (and a b) (not (or (not a) (not b)))))
     (assert (not (demorgan x y)))
     (check-sat))))

(defun rise4fun-demorgan-1 ()
  (z3::smt-prog
   '((declare-const x Bool)
     (declare-const y Bool)
     (define-fun demorgan ((a Bool) (b Bool)) Bool
      (= (and a b) (not (or (not a) (not b)))))
     (assert (demorgan x y))
     (check-sat))))

(test rise4fun-demorgan
  (is (eq (rise4fun-demorgan)
          :unsat))
  (is (eq (rise4fun-demorgan-1)
          :sat)))

;; (test rise4fun-define-fun
;;   (is (eq (z3::smt-prog
;;            '((declare-const p Bool)
;;              (declare-const q Bool)
;;              (declare-const r Bool)
;;              (define-fun conjecture () Bool
;;               (=> (and (=> p q) (=> q r))
;;                (=> p r)))
;;              (assert (not conjecture))
;;              (check-sat)))
;;           :unsat)


;; Misc
;; (defun misc ()
;;   (z3::smt-prog
;;    '((declare-const a bool)
;;      (declare-const b bool)
;;      (declare-const c bool)
;;      (assert a)
;;      (assert (distinct a b))
;;      (check-sat)
;;      (get-value (a b)))))

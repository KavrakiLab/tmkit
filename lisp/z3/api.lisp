(in-package :z3)

(defvar *context*)
(defvar *solver*)

(defun smt-normalize-id (key)
  (etypecase key
    (symbol (string key))
    (string key)
    (fixnum key)))

(defun smt-sort (name &optional (context *context*))
  (ecase name
    ((:bool bool |Bool|) (z3-mk-bool-sort context))
    (:int (z3-mk-int-sort context))
    (:real (z3-mk-real-sort context))))

(defun smt-declare (name sort &optional (context *context*))
  (let ((table (z3-context-symbols context))
        (key (smt-normalize-id name)))
    (assert (null (gethash key table)))
    (setf (gethash key table)
          (make-smt-symbol :name key
                           :sort (smt-sort sort context)
                           :object
                           (etypecase key
                             (string (z3-mk-string-symbol context key))
                             (fixnum (z3-mk-int-symbol context key)))))))

(defun smt-lookup (name &optional (context *context*))
  (gethash (smt-normalize-id name)
           (z3-context-symbols context)))

;; (defun smt-intern (key &optional (context *context*))
;;   (let ((table (z3-context-symbols context))
;;         (key (etypecase key
;;                  (symbol (string key))
;;                  (string key)
;;                  (fixnum key))))
;;     (multiple-value-bind (value contains)
;;         (gethash key table)
;;       (if contains
;;           value
;;           (setf (gethash key table)
;;                 (make-smt-symbol :name key
;;                 (etypecase key
;;                   (string (z3-mk-string-symbol context key))
;;                   (fixnum (z3-mk-int-symbol context key))))))))

(defun smt-error (e)
  (error "Malformed SMT Expression: ~A" e))

(defmacro with-ast-array ((var args context) &body body)
  (with-gensyms (i e)
    `(with-foreign-object (,var :pointer (length ,args))
       (loop
          for ,i from 0
          for ,e in ,args
          do (setf (mem-aref ,var :pointer ,i)
                   (z3-ast-pointer (smt->ast ,e ,context))))
       ,@body)))

(defmacro with-asts (lambda-list args context
                     &body body)
  (with-gensyms (e)
    `(destructuring-bind ,lambda-list
         (loop for ,e in ,args
            collect (smt->ast ,e ,context))
       ,@body)))


(defun smt->ast (e &optional (context *context*))
  (declare (type z3-context context))
  (if (consp e)
      ;; expression
      (destructuring-bind (op &rest args) e
        (ecase op
          (and (with-ast-array (a args context)
                 (z3-mk-and context (length args) a)))
          (or (with-ast-array (a args context)
                (z3-mk-or context (length args) a)))
          (=
           (with-asts (l r) args context
             (z3-mk-eq context l r)))
          (not
           (with-asts (arg) args context
             (z3-mk-not context arg)))
          (:ite)
          (:iff)
          (:implies)))
      ;; atom
      (case e
        ((t :true)
         (z3-mk-true context))
        ((nil :false)
         (z3-mk-false context))
        (otherwise
         (let ((e (smt-lookup e context)))
           (z3-mk-const context
                        (smt-symbol-object e)
                        (smt-symbol-sort e)))))))

(defun smt-assert (exp
                   &optional
                     (solver *solver*)
                     (context *context*))
  (z3-solver-assert context solver (smt->ast exp context)))

(defun smt-check  (&optional
                     (solver *solver*)
                     (context *context*))
  (ecase (z3-solver-check context solver)
    (:true :sat)
    (:undef :unknown)
    (:false :unsat)))

(defun smt-eval (stmt
                 &optional
                   (solver *solver*)
                   (context *context*))
  (destructuring-ecase stmt
    (((declare-fun |declare-fun| :declare-fun) name args type)
     (assert (null args)) ;; TODO: functions
     (smt-declare name type context))
    (((assert |assert| :assert) exp)
     (smt-assert exp solver context))
    (((check-sat |check-sat| :check-sat))
     (smt-check solver context))))


(defun smt-prog (stmts)
  (let* ((context (z3-mk-context (z3-mk-config)))
         (solver (z3-mk-solver context)))
    (labels ((rec (stmts)
               (let ((x (smt-eval (car stmts) solver context)))
                 (if (cdr stmts)
                     (rec (cdr stmts))
                     x))))
      (when stmts
        (rec stmts)))))

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
    ((:int int |Int|) (z3-mk-int-sort context))
    ((:real real |Real|) (z3-mk-real-sort context))))

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

(defun smt-exp-variables (exp)
  (let ((hash (make-hash-table :test #'equal)))
    (labels ((add (e)
               (setf (gethash e hash) t))
             (visit (e) ;; TODO: predicates
               (if (atom e)
                   (add e)
                   (case (car e)
                     ((=
                       and |and| :and
                       or |or| :or
                       not |not| :not
                       iff |iff| :iff
                       ite |ite| :ite
                       implies |implies| :implies)
                      (map nil #'visit (cdr e)))
                     (otherwise
                      (add e))))))
      (visit exp))
    (hash-table-keys hash)))

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


(defun smt-unop (context function args)
  (declare (type z3-context context)
           (type function function)
           (type list args))
  (unless (and args
               (null (cdr args)))
    (error "Wanted one argument: ~A" args) )
  (funcall function context (smt->ast (car args) context)))

(defun smt-binop (context function args)
  (declare (type z3-context context)
           (type function function)
           (type list args))
  (unless (and args
               (cdr args)
               (null (cddr args)))
    (error "Wanted two arguments: ~A" args) )
  (funcall function context
           (smt->ast (first args) context)
           (smt->ast (second args) context)))

(defun smt-nary-op (context function args)
  (declare (type z3-context context)
           (type function function)
           (type list args))
  (with-ast-array (a args context)
    (funcall function context (length args) a)))

(defun smt-sub (context args)
  (if (and args (null (cdr args)))
      ;; unary
      (smt-unop context #'z3-mk-unary-minus args)
      ;; n-ary
      (smt-nary-op context #'z3-mk-sub args)))

(defun smt-ite (context args)
  (declare (type z3-context context)
           (type list args))
  (unless (and args
               (cdr args)
               (cddr args)
               (null (cdddr args)))
    (error "Wanted three arguments: ~A" args) )
  (z3-mk-ite context
             (smt->ast (first args) context)
             (smt->ast (second args) context)
             (smt->ast (third args) context)))

(defmacro def-smt-op (&rest cases)
  `(defun smt-op (context e)
     (let ((op (car e))
           (args (cdr e)))
       (ecase op
         ,@(loop for (kw type function) in cases
              collect
                `(,kw
                  ,(case type
                    (:unary `(smt-unop context ,function args))
                    (:binary `(smt-binop context ,function args))
                    (:nary `(smt-nary-op context ,function args))
                    (otherwise `(,type context args)))))))))

(def-smt-op
    (= :binary #'z3-mk-eq)

    (not :unary #'z3-mk-not)
    (and :nary #'z3-mk-and)
    (or :nary #'z3-mk-or)
    (distinct :nary #'z3-mk-or)
    (implies :binary #'z3-mk-eq)
    (iff :binary #'z3-mk-eq)
    (xor :binary #'z3-mk-eq)
    (ite smt-ite)
    ;; TODO: if-then-else

    (+ :nary #'z3-mk-add)
    (* :nary #'z3-mk-add)
    (- smt-sub)
    (/ :binary #'z3-mk-div)
    (mod :binary #'z3-mk-mod)
    (rem :binary #'z3-mk-rem)
    (power :binary #'z3-mk-power)
    (< :binary #'z3-mk-lt)
    (<= :binary #'z3-mk-le)
    (> :binary #'z3-mk-gt)
    (>= :binary #'z3-mk-ge)

    )

(defun smt-atom (context e)
  (declare (type z3-context context))
  (etypecase e
    (fixnum
     (z3-mk-int context e (z3-mk-int-sort context)))
    (symbol
     (case e
       ((t :true)
        (z3-mk-true context))
       ((nil :false)
        (z3-mk-false context))
       (otherwise
        (let ((v (smt-lookup e context)))
          (unless v (error "Unbound: ~A" e))
          (z3-mk-const context
                       (smt-symbol-object v)
                       (smt-symbol-sort v))))))))

(defun smt->ast (e &optional (context *context*))
  (declare (type z3-context context))
  (if (consp e)
      (smt-op context e)
      (smt-atom context e)))

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

(defun model-value (context model thing)
  (let* ((ent  (smt-lookup thing context))
         (d  (z3-mk-func-decl context
                              (smt-symbol-object ent)
                              0 (null-pointer)
                              (smt-symbol-sort ent)))
         (a (z3-model-get-const-interp context model d)))
    (cond
      ((null-pointer-p (z3-ast-pointer a))
       :unknown)
      (t (z3-get-bool-value context a)))))


(defun smt-values (symbols &optional (solver *solver*) (context *context*))
  (let ((m (z3-solver-get-model context solver)))
  (loop
     for s in symbols
     for v = (model-value context m s)
     collect (cons s v))))

(defun smt-prog (stmts &key
                         context
                         solver)
  (let* ((context (or context
                      (z3-mk-context (z3-mk-config))))
         (solver (or solver
                     (z3-mk-solver context))))
    (labels ((rec (stmts)
               (let ((x (smt-eval (car stmts) solver context)))
                 (if (cdr stmts)
                     (rec (cdr stmts))
                     x))))
      (when stmts
        (rec stmts)))))

(defun check-sat (exp &key)
  (let* ((context (z3-mk-context (z3-mk-config)))
         (solver (z3-mk-solver context))
         (vars (smt-exp-variables exp))
         (stmts
          `(
            ;; declare variables
            ,@(loop for v in (smt-exp-variables exp)
                 collect `(declare-fun ,v () bool))
              ;; assert
              (assert ,exp)
              ;; check
              (check-sat))))
    (ecase (smt-prog stmts :context context :solver solver)
      (:sat (values t
                    (smt-values vars solver context)))
      (:unsat (values nil nil))
      (:unknown (error "Could not check: ~A" exp)))))

;; (defun check-sat (exp &key)
;;   (let* ((context (z3-mk-context (z3-mk-config)))
;;          (solver (z3-mk-solver context)))
;;     ;; declare variables
;;     (loop for v in (smt-exp-variables exp)
;;        do (smt-declare v :bool context))
;;     ;; assert
;;     (smt-assert exp solver context)
;;     ;; check
;;     (ecase (smt-check solver context)
;;       (:sat t)
;;       (:unsat nil)
;;       (:unknown (error "Could not check: ~A" exp)))) )

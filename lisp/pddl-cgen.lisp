(in-package :tmsmt)

(defvar *pd-cgen-state* "x")
(defvar *pd-cgen-state-type* "unsigned")


(defun pd-cvar (domain var &optional (array *pd-cgen-state*))
  (if-let ((i (position var (ground-domain-variables domain) :test #'equal)))
    (cgen-subscript array i)
    ;(rope-parenthesize (rope array "[" i "]"))
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

(defun pd-bind-exp (domain pexp cexp)
  (declare (ignore domain))
  (destructuring-bind (-and &rest terms) cexp
    (assert (eq 'and -and))
    (loop for term in terms
       for pterm in (cdr pexp)
       for op = (when (listp term) (car term))
       collect (list (cgen-comment (sexp-rope pterm))
                     (case op
                       ;; Todo: enum types
                       (not
                        (assert (= 2 (length term)))
                        (cgen-assign-stmt (second term) 0))
                       (otherwise
                        (cgen-assign-stmt term 1)))))))

(defun pd-action-pre-name (action)
  (cgen-identifier (rope "pre__"
                         (ground-action-name action)
                         "__"
                         (rope-split "_" (ground-action-actual-arguments action)))
                   :case :lower))

(defun pd-action-pre (domain action)
  (let* ((pexp (ground-action-precondition action))
         (cexp (pd-cexp domain pexp))
         (c (cgen-exp cexp)))
    (cgen-defun "static int"
                (pd-action-pre-name action)
                (rope "const " *pd-cgen-state-type* " *" *pd-cgen-state*)
                (list
                 (cgen-comment (sexp-rope pexp))
                 (cgen-return c)))))

(defun pd-cgen-action-pres (domain)
  (loop for a in (ground-domain-operators domain)
     collect (pd-action-pre domain a)))

(defun pd-action-eff-name (action)
  (cgen-identifier (rope "eff__"
                         (ground-action-name action)
                         "__"
                         (rope-split "_" (ground-action-actual-arguments action)))
                   :case :lower))

(defun pd-action-eff (domain action)
  (let* ((pexp (ground-action-effect action))
         (cexp (pd-cexp domain pexp))
         (c (pd-bind-exp domain pexp cexp)))
    (cgen-defun "static void"
                (pd-action-eff-name action)
                (rope *pd-cgen-state-type* " *" *pd-cgen-state*)
                (list
                 (cgen-comment (sexp-rope pexp))
                 c))))

(defun pd-cgen-action-effs (domain)
  (loop for a in (ground-domain-operators domain)
     collect (pd-action-eff domain a)))

(defun pd-cgen-struct (domain &key
                                (name "pddl_init"))
  (let ((struct "s")
        (type-objects (ground-domain-type-objects domain))
        (variable-type (ground-domain-variable-type domain))
        (type-indices (make-hash-table :test #'equal)))
    ;; index types
    (let ((i -1))
      (do-tree-map ((key value) type-objects)
        (declare (ignore value))
        (setf (gethash key type-indices)
              (incf i))))
    ;; construct c-code
    (labels ((field (field)
               (cgen-exp `(:-> ,struct ,field)))
             (field-assign (field value)
               (cgen-assign-stmt (field field)
                                 value))
             (init-array (type array-field values &optional size-field )
               (list
                (when size-field (field-assign size-field (length values)))
                (cgen-declare-array (rope "static const " type) array-field values)
                (field-assign array-field array-field)
               )))
      (cgen-defun "void" name
                  (rope "struct tmp_pd_pddl_struct *" struct)
                  (list
                   ;; type
                   (init-array "unsigned" "type"
                               (map-tree-map :inorder 'list
                                             (lambda (type object-set)
                                               (declare (ignore type))
                                               (tree-set-count object-set))
                                             type-objects)
                               "n_type")

                   ;; func
                   (init-array "unsigned" "func"
                               (map-tree-map :inorder 'list
                                             (lambda (variable type)
                                               (declare (ignore variable))
                                               (gethash type type-indices))
                                             variable-type)
                               "n_func")
                   ;; action_precon
                   (init-array "tmp_pd_action_precon" "action_precon"
                               (map 'list #'pd-action-pre-name (ground-domain-operators domain))
                               "n_action")
                   ;; action_effect
                   (init-array "tmp_pd_action_eff" "action_effect"
                               (map 'list #'pd-action-eff-name (ground-domain-operators domain)))
                   )))))


(defun pd-cgen (domain
                &key
                  ;output
                         )
  (let ((pres (pd-cgen-action-pres domain))
        (effs (pd-cgen-action-effs domain))
        (struct (pd-cgen-struct domain)))
    (rope pres effs struct)))

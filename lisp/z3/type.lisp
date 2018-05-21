(in-package :z3)

(define-foreign-type z3-string () ()
   (:actual-type :string)
   (:simple-parser z3-string))

(amino-ffi::def-foreign-container
    z3-config z3-config-type
  :destructor ("Z3_del_config" z3-del-config))

(defstruct smt-symbol
  name
  sort
  symbol
  func-decl
  ast
  )

;; (defstruct smt-sortdec
;;   name
;;   sort)

(amino-ffi::def-foreign-container
    z3-context z3-context-type
  :destructor ("Z3_del_context" z3-del-context)
  :slots ((symbols (make-hash-table :test #'equal))
          (sorts (make-hash-table :test #'equal))))

(amino-ffi::def-foreign-container
    z3-solver z3-solver-type
  :slots (context))

(amino-ffi::def-foreign-container
    z3-func-decl z3-func-decl-type)

(amino-ffi::def-foreign-container
    z3-func-interp z3-func-interp-type)

(amino-ffi::def-foreign-container
    z3-func-entry z3-func-entry-type)

(amino-ffi::def-foreign-container
    z3-ast z3-ast-type)

(amino-ffi::def-foreign-container
    z3-ast-vector z3-ast-vector-type)

(amino-ffi::def-foreign-container
    z3-symbol z3-symbol-type)

(amino-ffi::def-foreign-container
    z3-sort z3-sort-type)

(amino-ffi::def-foreign-container
    z3-model z3-model-type)

(amino-ffi::def-foreign-container
    z3-stats z3-stats-type)

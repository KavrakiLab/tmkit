(in-package :z3)

(amino-ffi::def-foreign-container
    z3-config z3-config-type
  :destructor ("Z3_del_config" z3-del-config))

(defstruct smt-symbol
  name
  sort
  object)


(amino-ffi::def-foreign-container
    z3-context z3-context-type
  :destructor ("Z3_del_context" z3-del-context)
  :slots ((symbols (make-hash-table :test #'equal))))

(amino-ffi::def-foreign-container
    z3-solver z3-solver-type)

(amino-ffi::def-foreign-container
    z3-ast z3-ast-type)

(amino-ffi::def-foreign-container
    z3-symbol z3-symbol-type)

(amino-ffi::def-foreign-container
    z3-sort z3-sort-type)

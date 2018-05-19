(in-package :z3)

(define-foreign-library libz3
  (t (:default "libz3")))

(use-foreign-library libz3)


(defcfun "Z3_get_full_version" :string)

;;; Config
(defcfun "Z3_mk_config" z3-config-type)

;;; Context
(defcfun "Z3_mk_context" z3-context-type
  (config z3-config-type))

;;; Solver
(defcfun "Z3_mk_solver" z3-solver-type
  (context z3-context-type))

(defcfun "Z3_solver_push" :void
  (context z3-context-type)
  (solver z3-solver-type))

(defcfun "Z3_solver_pop" :void
  (context z3-context-type)
  (solver z3-solver-type)
  (n :unsigned-int))

(defcfun "Z3_solver_assert" :void
  (context z3-context-type)
  (solver z3-solver-type)
  (ast z3-ast-type))

(defcfun "Z3_solver_check" z3-lbool
  (context z3-context-type)
  (solver z3-solver-type))

(defcfun "Z3_solver_get_model" z3-model-type
  (context z3-context-type)
  (solver z3-solver-type))


;;; Symbols
(defcfun "Z3_mk_int_symbol" z3-symbol-type
  (context z3-context-type)
  (i :int))

(defcfun "Z3_mk_string_symbol" z3-symbol-type
  (context z3-context-type)
  (s :string))

;;; Sorts
(defcfun "Z3_mk_bool_sort" z3-sort-type
  (context z3-context-type))

(defcfun "Z3_mk_int_sort" z3-sort-type
  (context z3-context-type))

(defcfun "Z3_mk_real_sort" z3-sort-type
  (context z3-context-type))

;;; AST - Boolean
(defmacro def-ast-unop (name)
  `(defcfun ,name z3-ast-type
     (context z3-context-type)
     (a z3-ast-type)))

(defmacro def-ast-binop (name)
  `(defcfun ,name z3-ast-type
     (context z3-context-type)
     (a z3-ast-type)
     (b z3-ast-type)))

(defmacro def-ast-nary (name)
  `(defcfun  ,name z3-ast-type
     (context z3-context-type)
     (n :unsigned-int)
     (args :pointer)))

(defmacro def-ast-ops (type &body names)
  `(progn
     ,@(loop for n in names
          collect `(,type ,n))))

(defcfun "Z3_mk_true" z3-ast-type
  (context z3-context-type))

(defcfun "Z3_mk_false" z3-ast-type
  (context z3-context-type))

(defcfun "Z3_mk_ite" z3-ast-type
  (context z3-context-type)
  (t1 z3-ast-type)
  (t2 z3-ast-type)
  (t3 z3-ast-type))

(def-ast-unop "Z3_mk_not")

(def-ast-ops def-ast-binop
  "Z3_mk_eq"
  "Z3_mk_iff"
  "Z3_mk_implies"
  "Z3_mk_xor")

(def-ast-ops def-ast-nary
  "Z3_mk_and"
  "Z3_mk_or"
  "Z3_mk_distinct")

;;; AST - Integer / Real
(def-ast-unop "Z3_mk_unary_minus")

(def-ast-ops def-ast-nary
  "Z3_mk_add"
  "Z3_mk_mul"
  "Z3_mk_sub")

(def-ast-ops def-ast-binop
  "Z3_mk_div"
  "Z3_mk_mod"
  "Z3_mk_rem"
  "Z3_mk_power"
  "Z3_mk_lt"
  "Z3_mk_le"
  "Z3_mk_gt"
  "Z3_mk_ge")

(def-ast-ops def-ast-unop
  "Z3_mk_int2real"
  "Z3_mk_real2int"
  "Z3_mk_is_int")


(defcfun "Z3_mk_const" z3-ast-type
  (context z3-context-type)
  (symbol z3-symbol-type)
  (sort z3-sort-type))

(defcfun "Z3_mk_func_decl" z3-func-decl-type
  (context z3-context-type)
  (symbol z3-symbol-type)
  (domain-size :unsigned-int)
  (domain :pointer) ;; array of sorts
  (range z3-sort-type))

;; String conversion
(defcfun "Z3_ast_to_string" :string
  (context z3-context-type)
  (a z3-ast-type))

(defcfun "Z3_model_to_string" :string
  (context z3-context-type)
  (m z3-model-type))

;;; Accessors

(defcfun "Z3_get_bool_value" z3-lbool
  (context z3-context-type)
  (a z3-ast-type))

;;; Model

(defcfun "Z3_model_get_func_interp" z3-func-interp-type
  (context z3-context-type)
  (model z3-model-type)
  (func-decl z3-func-decl-type))


(defcfun "Z3_model_get_const_interp" z3-ast-type
  (context z3-context-type)
  (model z3-model-type)
  (func-decl z3-func-decl-type))

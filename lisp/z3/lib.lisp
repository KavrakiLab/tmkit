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

;;; AST
(defcfun "Z3_mk_true" z3-ast-type
  (context z3-context-type))

(defcfun "Z3_mk_false" z3-ast-type
  (context z3-context-type))

(defcfun "Z3_mk_not" z3-ast-type
  (context z3-context-type)
  (a z3-ast-type))

(defmacro def-ast-binop (name)
  `(defcfun ,name z3-ast-type
     (context z3-context-type)
     (a z3-ast-type)
     (b z3-ast-type)))

(def-ast-binop "Z3_mk_eq")
(def-ast-binop "Z3_mk_iff")
(def-ast-binop "Z3_mk_ite")
(def-ast-binop "Z3_mk_implies")
(def-ast-binop "Z3_mk_xor")

(defcfun  "Z3_mk_and" z3-ast-type
  (context z3-context-type)
  (n :unsigned-int)
  (args :pointer))

(defcfun  "Z3_mk_or" z3-ast-type
  (context z3-context-type)
  (n :unsigned-int)
  (args :pointer))

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

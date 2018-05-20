(progn
  (in-package :z3)
  (include "z3.h")

  (cenum z3-lbool
         ((:false "Z3_L_FALSE"))
         ((:undef "Z3_L_UNDEF"))
         ((:true "Z3_L_TRUE")))

  (cenum z3-symbol-kind
         ((:int "Z3_INT_SYMBOL"))
         ((:string "Z3_STRING_SYMBOL")))

  (cenum z3-sort-kind
         ((:uninterpreted "Z3_UNINTERPRETED_SORT"))
         ((:bool "Z3_BOOL_SORT"))
         ((:int "Z3_INT_SORT"))
         ((:real "Z3_REAL_SORT"))
         ((:bv "Z3_BV_SORT"))
         ((:array "Z3_ARRAY_SORT"))
         ((:datatype "Z3_DATATYPE_SORT"))
         ((:relation "Z3_RELATION_SORT"))
         ((:finite-domain "Z3_FINITE_DOMAIN_SORT"))
         ((:floating-point "Z3_FLOATING_POINT_SORT"))
         ((:rounding-mode "Z3_ROUNDING_MODE_SORT"))
         ((:seq "Z3_SEQ_SORT"))
         ((:re "Z3_RE_SORT"))
         ((:unknown "Z3_UNKNOWN_SORT")))

  (cenum z3-error-code
         ((:OK "Z3_OK"))
         ((:SORT_ERROR "Z3_SORT_ERROR"))
         ((:IOB "Z3_IOB"))
         ((:INVALID_ARG "Z3_INVALID_ARG"))
         ((:PARSER_ERROR "Z3_PARSER_ERROR"))
         ((:NO_PARSER "Z3_NO_PARSER"))
         ((:INVALID_PATTERN "Z3_INVALID_PATTERN"))
         ((:MEMOUT_FAIL "Z3_MEMOUT_FAIL"))
         ((:FILE_ACCESS_ERROR "Z3_FILE_ACCESS_ERROR"))
         ((:INTERNAL_FATAL "Z3_INTERNAL_FATAL"))
         ((:INVALID_USAGE "Z3_INVALID_USAGE"))
         ((:DEC_REF_ERROR "Z3_DEC_REF_ERROR"))
         ((:EXCEPTION "Z3_EXCEPTION")))

  )

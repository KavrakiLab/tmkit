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

  )

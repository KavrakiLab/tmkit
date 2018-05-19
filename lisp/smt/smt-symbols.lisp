(defpackage smt-symbol
  (:use :cl)
  (:export

   :declare-fun
   :|declare-fun|

   :declare-const
   :|declare-const|

   :define-fun
   :|define-fun|

   :check-sat
   :|check-sat|

   :get-value
   :|get-value|

   :ite
   :|ite|

   :bool
   :|Bool|

   :let
   :|let|

   :|not|
   :|and|
   :|or|
   :|assert|

   :=>
   ))

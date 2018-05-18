(defpackage smt-symbol
  (:use :cl)
  (:export

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

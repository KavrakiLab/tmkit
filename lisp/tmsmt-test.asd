(cl:eval-when (:load-toplevel :execute)
    (asdf:operate 'asdf:load-op 'cffi-grovel))

(asdf:defsystem tmsmt-test
  :description "Tests for TMKit"
  :depends-on ("tmsmt" "fiveam")
  :components (
               (:file "z3/test")
               ))

(in-package :tmsmt)


(cffi:define-foreign-library libompl
  (:unix "/usr/local/lib/libompl.so")
  (t (:default "/usr/local/lib/libompl")))

(cffi:use-foreign-library libompl)

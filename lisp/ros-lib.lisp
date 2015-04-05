(in-package :tmsmt)

(cffi:define-foreign-library libtmsmt
    (:unix (:or #.(concatenate 'string (namestring (user-homedir-pathname))
                               "ros_ws/src/tmsmt/devel/lib/libtmsmt.so")
                "libtmsmt.so"))
  (t (:default "libtmsmt")))

(cffi:use-foreign-library libtmsmt)

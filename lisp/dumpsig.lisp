(require 'cffi)

(cffi:define-foreign-library libdumpsig
    (:unix (:or #.(concatenate 'string (namestring (user-homedir-pathname))
                               "ros_ws/src/tmsmt/devel/lib/libdumpsig.so")
                "libdumpsig.so"))
  (t (:default "libdumpsig")))

(cffi:use-foreign-library libdumpsig)

(cffi:defcfun dumpsig :void)
(cffi:defcfun unblock-sigpipe :void)

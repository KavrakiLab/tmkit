#-sbcl
(progn
  (format *error-output* "~&Only SBCL is supported; aborting build.~&")
  (abort)
  (error nil))

(require :asdf)

;; Add source directory to ASDF registry
(pushnew (pathname "./lisp/")
         asdf:*central-registry*
         :test #'equal)


(require :tmsmt)

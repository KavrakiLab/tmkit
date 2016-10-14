#-sbcl
(progn
  (format *error-output* "~&Only SBCL is supported; aborting build.~&")
  (abort)
  (error nil))

(require :asdf)

;; Add source directory to ASDF registry

(let* ((top-srcdir (pathname (concatenate 'string
                                          (uiop/os:getenv "top_builddir")
                                          "/")))
       (lispdir (merge-pathnames (make-pathname :directory '(:relative "lisp"))
                                 top-srcdir)))
  (pushnew lispdir
           asdf:*central-registry*
           :test #'equal))

(ql:quickload :tmsmt)

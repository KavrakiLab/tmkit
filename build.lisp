(let ((top-srcdir (concatenate 'string
                               (uiop/os:getenv "top_srcdir")
                               "/")))
  (load (merge-pathnames "load.lisp" top-srcdir)))


(let ((compression nil))
  #+sb-core-compression
  (setq compression t)
  (sb-ext:save-lisp-and-die "tmsmt.core"
                            :executable t
                            :compression compression))

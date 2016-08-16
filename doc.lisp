(let ((top-srcdir (concatenate 'string
                               (uiop/os:getenv "top_srcdir")
                               "/")))
  (load (merge-pathnames "load.lisp" top-srcdir)))

(require :ntdoc)
(ntdoc::markdown "tmsmtpy" :system :tmsmt :target "scriptapi.md" :title "Domain Script API (Python)")

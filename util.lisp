(in-package :tmsmt)

(defun load-sexp (filename)
  "Read a single s-expression from a file"
  (with-open-file (s filename :direction :input)
    (read s)))

(defun check-symbol (value required)
  "Check symbol name of `VALUE' is string= to symbol name of `REQUIRED'"
  (unless (string= (string value) (string required))
    (error "Symbol mismatch on ~A, required ~A" value required)))

;; (declaim (inline fold))
;; (defun fold (function initial-value sequence)
;;   (sycamore::fold function initial-value sequence))

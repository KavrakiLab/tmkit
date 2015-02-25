(defun smt-subst (stmts)
  "Replace upcased CL symbols with properly-cased SMT-Lib symbols"
  (sublis '((or     .  |or|)
            (not    .  |not|)
            (assert .  |assert|)
            (bool   .  |Bool|)
            (and    .  |and|))
          stmts))

(defun smt-print (stmts &optional (stream *standard-output*))
  ;; Use the lisp printer to pretty print the expressions, then fixup
  ;; the output with some regular expressions
  (let* ((cl-string (with-output-to-string (s)
                      (dolist (e (smt-subst stmts))
                        (print e s))))
         ;; eat CL case quotes
         (smt-string-0 (ppcre:regex-replace-all "\\|([\\w\\-]+)\\|"
                                                cl-string
                                                "\\1"))
         ;; eat string quotes
         (smt-string-1 (ppcre:regex-replace-all "\"([\\w\\-]+)\""
                                                smt-string-0
                                                "\\1"))
         ;; replace NILs with ()
         (smt-string-2 (ppcre:regex-replace-all "([\\s\\(\\)])NIL([\\s\\(\\)])"
                                                smt-string-1
                                                "\\1()\\2")))
    (princ smt-string-2 stream))
  nil)


(defun smt-assert (x)
  (list '|assert| x))

(defun smt-declare-fun (name args type)
  (list '|declare-fun| name args type))

(defun smt-not (x)
  (list 'not x))

(defun smt-or (&rest args)
  (cons 'or args))

(defun smt-and (&rest args)
  (cons 'and args))

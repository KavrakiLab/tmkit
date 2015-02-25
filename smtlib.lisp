(in-package :tmsmt)

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

(defun smt-parse-assignments (assignments)
  (let ((plan))
    (dolist (x assignments)
      (destructuring-bind (var value) x
        (when (eq 'true value)
          (push (unmangle-op (string var)) plan))))
    (sort plan (lambda (a b) (< (car a) (car b))))))

(defun smt-input (file)
  (multiple-value-bind (is-sat assignments)
      (with-open-file (s file :direction :input)
        (values (read s)
                (read s)))
    ;(print is-sat)
    (when (eq 'sat is-sat)
      (smt-parse-assignments assignments))))

(defun smt-run (statements variables
                &key
                  (smt-file "/tmp/tmsmt.smt2")
                  (result-file "/tmp/tmsmt2-result"))
  "Run the SMT solver on `statements' and return assignments to `variables'.
Returns -- (values is-satisfiabibly (list assignments))"
  ;; write statements
  (with-open-file (s smt-file :direction :output :if-exists :supersede)
    (smt-print statements s)
    (smt-print `((|check-sat|)
                 (|get-value| ,variables))
               s))
  (sb-ext:run-program "z3" (list "-smt2" smt-file)
                      :search t :wait t
                      :output result-file
                      :if-output-exists :supersede)
  ;; check-sat
  (multiple-value-bind (is-sat assignments)
      (with-open-file (s result-file :direction :input)
        (values (read s)
                (read s)))
    (if (eq 'sat is-sat)
        (values assignments t)
        (values nil nil))))

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
                        (destructuring-case e
                          ((comment x)
                           (format s "~&;; ~A" x))
                          ((t &rest ignore)
                           (declare (ignore ignore))
                           (print e s))))))
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

(defun smt-ident (thing)
  (etypecase thing
    (string thing)
    (list (smt-mangle-list thing))))

(defun smt-declare-fun (name args type)
  (list '|declare-fun| (smt-ident name) args type))

(defun smt-not (x)
  (list 'not x))

(defun smt-or (&rest args)
  (cons 'or args))

(defun smt-and (&rest args)
  (cons 'and args))

(defun smt-= (&rest args)
  (cons '= args))

(defun smt-comment (x)
  (list 'comment x))

(defparameter +smt-separator+ "__")
(defparameter +smt-left-paren+ "-LP-")
(defparameter +smt-right-paren+ "-RP-")

(defun smt-mangle-list (list)
  "Mangle arguments into an SMT identifier."
  (with-output-to-string (str)
    (labels ((rec (x)
               (etypecase x
                 (atom (format str "~A~A" +smt-separator+ x))
                 (list
                  (format str "~A~A" +smt-separator+ +smt-left-paren+)
                  (rec-list x)
                  (format str "~A~A" +smt-separator+ +smt-right-paren+))))
             (rec-list (args)
               (map nil #'rec args)))
      (rec-list list))))

(defun smt-mangle (&rest args)
  (smt-mangle-list args))

(defun smt-unmangle (mangled)
  "Unmangle SMT identifier into a list."
  (let ((list (ppcre:split +smt-separator+ mangled)))
    ;; mangled identifier split into tokens
    (labels ((parse (x)
               ;; parse atomic element
               (multiple-value-bind (i n)
                   (parse-integer x :junk-allowed t)
                 (if (and i (= n (length x)))
                     i
                     x)))
             (bad-ident ()
               (error "Bad identifier: ~A" mangled))
             (rec (list)
               ;; append elements from rest onto cons
               (when list
                 (destructuring-bind (first . rest) list
                   (cond
                     ((string= first +smt-left-paren+)
                      ;; parse sublist
                      (multiple-value-bind (car-1 rest-1)
                          (rec rest)
                        ;; check we got right parent
                        (unless (string= (car rest-1) +smt-right-paren+)
                          (bad-ident))
                        ;; parse remainder
                        (multiple-value-bind (cdr-2 rest-2)
                            (rec (cdr rest-1))
                          ;; result
                          (values (cons car-1 cdr-2)
                                  rest-2))))
                     ((string= first +smt-right-paren+)
                      (values nil list))
                     (t (multiple-value-bind (cdr rest)
                            (rec rest)
                          (values (cons (parse first)
                                        cdr)
                                  rest))))))))
      (multiple-value-bind (car rest)
          (rec (cdr list))
        (when rest
          (error "Bad identifier: ~A" mangled))
        car))))

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



(defstruct smt-problem
  statements ;; list of statements
  variables  ;; list of variables
  decode-function ;; VARIABLE-ASSIGNMENT => result
  )

(defun smt-problem-print (problem
                          &key
                            (stream *standard-output*))
  (smt-print (smt-problem-statements problem) stream)
  (smt-print `((|check-sat|)
               (|get-value| ,(smt-problem-variables problem)))
             stream))

(defun smt-run-problem (problem)
  (multiple-value-bind (assignments is-sat)
      (smt-run (smt-problem-statements problem)
               (smt-problem-variables problem))
    (if is-sat
        (let ((unmangled-variables
               (loop for (variable value) in assignments
                  collect (list (smt-unmangle (string variable)) value))))
          (values (funcall (smt-problem-decode-function problem)
                           unmangled-variables)
                  t))
        (values nil nil))))

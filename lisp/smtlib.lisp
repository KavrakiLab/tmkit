(in-package :tmsmt)

(defun smt-print-1 (stmt &optional (stream *standard-output*))
  (destructuring-case stmt
    ((comment x)
     (format stream "~&;; ~A" x))
    ((t &rest ignore)
     (declare (ignore ignore))
     (flet ((symbol-substitute (s)
              (if s
                  (case s
                    (or        '|or|)
                    (xor       '|xor|)
                    (let       '|let|)
                    (not       '|not|)
                    (ite       '|ite|)
                    (assert    '|assert|)
                    (bool      '|Bool|)
                    (and       '|and|)
                    (otherwise s))
                  '|()|)))
     (print-sexp stmt #'symbol-substitute stream)))))

(defun smt-print (stmts &optional (stream *standard-output*))
  (let ((str
         (with-output-to-string (stream)
           (dolist (s stmts)
             (smt-print-1 s stream)
             (terpri stream)))))
    (write-sequence str stream))
  nil)


(defun smt-set-option (option value)
  (list '|set-option|
        option
        value))

(defun smt-assert (x)
  (list '|assert| x))

(defun smt-ident (thing)
  (etypecase thing
    (string thing)
    (list (smt-mangle-list thing))))

(defun smt-declare-fun (name args type)
  (list '|declare-fun| (smt-ident name) args type))

(defun smt-define-fun (name args type exp)
  (list '|define-fun| (smt-ident name) args type
         exp))

(defun smt-not (x)
  (list 'not x))

(defun smt-or (&rest args)
  (cons 'or args))

(defun smt-xor (&rest args)
  (cons 'xor args))

(defun smt-and (&rest args)
  (cons 'and args))

(defun smt-= (&rest args)
  (cons '= args))

(defun smt-ite (test then else)
  (list 'ite test then else))

(defun smt-let* (bindings expr)
  (if bindings
      `(let (,(car bindings))
         ,(smt-let* (cdr bindings) expr))
      expr))

(defun smt-comment (x)
  (list 'comment x))

(defparameter +smt-separator+ "__")
(defparameter +smt-left-paren+ "-LP-")
(defparameter +smt-right-paren+ "-RP-")

(defun smt-mangle-list (list)
  "Mangle arguments into an SMT identifier."
  (with-output-to-string (str)
    (labels ((rec (rest)
               (when rest
                 (destructuring-bind (x &rest rest) rest
                   (let ((sep (if rest +smt-separator+ "")))
                     (etypecase x
                       ((or string symbol number) (format str "~A~A" x sep))
                       (list
                        (format str "~A~A" +smt-left-paren+ +smt-separator+)
                        (rec x)
                        (format str "~A~A~A" +smt-separator+ +smt-right-paren+ sep))))
                   (rec rest)))))
      (rec list))))

(defun smt-mangle (&rest args)
  (smt-mangle-list args))

(defun smt-unmangle (mangled)
  "Unmangle SMT identifier into a list."
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
        (let ((list (ppcre:split +smt-separator+ mangled)))
          (rec list))
      (when rest
        (error "Bad identifier: ~A" mangled))
      car)))

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

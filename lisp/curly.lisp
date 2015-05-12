(in-package :tmsmt)

(defun curly-eat-blank (string start)
  (loop for i from start below (length string)
     while (amino::char-isblank (aref string i))
     finally (return i)))

(defparameter +curly-regex-tokens+
  (list (list "{" #\{)
        (list "}" #\})
        (list "\\(" #\()
        (list "\\)" #\))
        (list "\\\"[^\\\"]*\\\"" :string
              (lambda (string start end)
                (subseq string (1+ start) (1- end))))
        (list "[a-zA-Z][a-zA-Z0-9_]*" :identifer
              #'subseq)
        (list "[0-9]+\\.[0-9]*" :float
              (lambda (string start end)
                (parse-float (subseq string start end))))
        (list "[0-9]+" :integer
              (lambda (string start end)
                (parse-integer string :start start :end end)))))

(defparameter +curly-scanners+
  (loop for thing in +curly-regex-tokens+
     for regex = (car thing)
     for rest = (cdr thing)
     collect (cons (ppcre:create-scanner (concatenate 'string "^" regex)) rest)))

(defun curly-next-token (string start)
  "Returns (VALUES TOKEN-VALUE TOKEN-TYPE END)"
  (let ((start (curly-eat-blank string start)))
    (loop for (scanner type value-function) in +curly-scanners+
       do (multiple-value-bind (start end)
              (ppcre:scan scanner string :start start)
            (when start
              (return (values type
                              (when value-function
                                (funcall value-function string start end))
                              end)))))))


(defun curly-parse (string)
  (let ((start 0))
    (labels ((next ()
               (multiple-value-bind (type token end)
                   (curly-next-token string start)
                 (format t "~&Token: ~A" (subseq string start end))
                 (setq start end)
                 (values type token)))
             (start ()
               (print 'start)
               (multiple-value-bind (type token) (next)
                 (when type
                   (cons token (body)))))
             (body ()
               (print 'body)
               (let ((type (next)))
                 (assert (eq #\{ type)))
               (body-first-item))
             (body-first-item ()
               (print 'body-first-item)
               (multiple-value-bind (type token) (next)
                 (if (eq type #\})
                     nil
                     (body-next-item token))))
             (body-next-item (head-token)
               (print (list 'body-next-item head-token))
               (multiple-value-bind (type token) (next)
                 (case type
                   (#\} (list head-token))
                   (#\{ (cons (cons head-token (body-first-item))
                              (body-first-item)))
                   (otherwise (cons head-token (body-next-item token)))))))

      (start))))

(in-package :tmsmt)

(defvar *smt-trace-command* nil)

(defstruct smt
  (runtime 0d0 :type double-float)
  process)

(defparameter *smt-readtable*
  (let ((r (copy-readtable nil)))
    (setf (readtable-case r) :preserve)
    r))


(defun smt-input (smt)
  (sb-ext:process-input (smt-process smt)))

(defun smt-output (smt)
  (sb-ext:process-output (smt-process smt)))

(defun smt-read (smt &optional (eof-error-p t) eof-value recursive-p)
  (let ((*readtable* *smt-readtable*))
    (read (smt-output smt) eof-error-p eof-value recursive-p)))

(define-condition smt-runtime-error (error)
  ((message :initarg :message
            :reader message)
   (expression :initarg :expression
               :reader expression)))

(defmethod print-object ((object smt-runtime-error) stream)
  (print-unreadable-object (object stream :type t)
    (with-slots (message expression) object
      (format stream "\"~A: '~A'\"" message expression))))

(defun smt-symbol-eq (symbol upcase downcase)
  (or (eq symbol upcase)
      (eq symbol downcase)))

(defun smt-eval (smt exp)
  (when (eq (car exp) 'comment)
    (return-from smt-eval t))
  ;; Write
  (labels ((command (stream)
             (smt-print-1 exp stream)
             (terpri stream)
             (finish-output stream)))
    ;; Maybe trace commands
    (when *smt-trace-command*
      (command *smt-trace-command*))
    ;; Read
    (let ((result
           (multiple-value-bind (result run-time real-time)
               (sycamore-util::with-timing
                 (command (smt-input smt))
                 (smt-read smt))
             (declare (ignore run-time))
             (incf (smt-runtime smt) real-time)
             result)))
      (cond
        ((smt-symbol-eq result 'unsupported '|unsupported|)
         (error 'smt-runtime-error
                :message "Unsupported expression"
                :expression exp))
        ((smt-symbol-eq result 'success '|success|)
         t)
        ((and (consp result)
              (or (smt-symbol-eq (car result) 'error  '|error|)))
         (error 'smt-runtime-error
                :message (second result)
                :expression exp))
        (t
         result)))))

(defparameter *smt-solver-z3*
  (list "z3" "-smt2" "-in"))

(defvar *smt*)
(defparameter *smt-solver* *smt-solver-z3*)

(defun smt-process-kill (process)
  (when process
    (when (sb-ext:process-alive-p process)
      (sb-ext:process-kill process 9))
    (sb-ext:process-wait process)
    (sb-ext:process-close process)))

(defun smt-start (&key (smt-solver *smt-solver*))
  (let ((process (sb-ext:run-program (car smt-solver)
                                     (cdr smt-solver)
                                     :search t
                                     :wait nil
                                     :input :stream
                                     :error t
                                     :output :stream
                                     ))
        (smt (make-smt)))
    (sb-ext:finalize smt (lambda () (smt-process-kill process)))
    (setf (smt-process smt) process)
    (smt-eval smt (smt-set-option ":print-success" '|true|))
    ;(smt-eval smt (smt-set-option ":produce-unsat-cores" '|true|))
    smt))

(defun smt-stop (smt)
  (smt-process-kill (smt-process smt))
  (setf (smt-process smt) nil))

(defmacro with-smt ((variable &key
                              (smt-solver '*smt-solver*)
                              (trace-command "/tmp/smt-command"))
                    &body body)
  `(let ((,variable (smt-start :smt-solver ,smt-solver)))
     (labels ((runit ()
                (unwind-protect
                     (progn ,@body)
                  (smt-stop ,variable))))
       ,(if trace-command
            `(progn
               (format *standard-output* "~&Tracing SMT to ~A~%" ,trace-command)
               (with-open-file (*smt-trace-command* ,trace-command :direction :output :if-exists :supersede)
                 (runit)))
            `(runit)))))

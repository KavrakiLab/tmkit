(in-package :tmsmt)

(defstruct smt
  process)

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
    smt))

(defun smt-input (smt)
  (sb-ext:process-input (smt-process smt)))

(defun smt-output (smt)
  (sb-ext:process-output (smt-process smt)))

(defun smt-stop (smt)
  (smt-process-kill (smt-process smt))
  (setf (smt-process smt) nil))

(define-condition smt-runtime-error (error)
  ((message :initarg :message
            :reader message)
   (expression :initarg :expression
               :reader expression)))

(defmethod print-object ((object smt-runtime-error) stream)
  (print-unreadable-object (object stream :type t)
    (with-slots (message expression) object
      (format stream "\"~A: '~A'\"" message expression))))

(defun smt-eval (smt exp)
  (let* ((process (smt-process smt))
         (input (sb-ext:process-input process)))
    ;; Write
    (smt-print-1 exp (sb-ext:process-input process))
    (terpri (sb-ext:process-input process))
    (finish-output input)
    ;; Read
    (let ((result (read (sb-ext:process-output process))))
      (case result
        (unsupported (error 'smt-runtime-error
                            :message "Unsupported expression"
                            :expression exp))
        (otherwise
         result)))))

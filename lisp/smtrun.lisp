(in-package :tmsmt)

(defstruct smt
  process)

(defparameter *smt-solver-z3*
  (list "z3" "-smt2" "-in"))

(defun smt-process-kill (process)
  (when process
    (when (sb-ext:process-alive-p process)
      (sb-ext:process-kill process 9))
    (sb-ext:process-wait process)
    (sb-ext:process-close process)))

(defun smt-start (&key (smt-solver *smt-solver-z3*))
  (let ((process (sb-ext:run-program (car smt-solver)
                                     (cdr smt-solver)
                                     :search t
                                     :wait nil
                                     :input :stream
                                     :output :stream))
        (smt (make-smt)))
    (sb-ext:finalize smt (lambda () (smt-process-kill process)))
    (setf (smt-process smt) process)
    smt))

(defun smt-stop (smt)
  (smt-process-kill (smt-process smt))
  (setf (smt-process smt) nil))

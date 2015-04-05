(in-package :tmsmt)

;;;;;;;;;;;;;;;;;;;;;;;;
;;; MOVEIT CONTAINER ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct foreign-container
  pointer)


(defun foreign-container-finalizer (object destructor)
  "Register finalizer to call DESTRUCTOR on OBJECT's pointer.
RETURNS: OBJECT"
  (let ((pointer (foreign-container-pointer object)))
    (sb-ext:finalize object (lambda () (funcall destructor pointer))))
  object)



(defmacro with-deferred-signals (&body body)
  `(progn
     (sb-thread::block-deferrable-signals)
     (unwind-protect (progn ,@body)
       (sb-unix::unblock-deferrable-signals))))

(defstruct (moveit-container (:include foreign-container)
                             (:constructor make-moveit-container (pointer))))

(cffi:define-foreign-type moveit-container-t ()
  ()
  (:simple-parser moveit-container-t)
  (:actual-type :pointer))

(defmethod cffi:expand-to-foreign (value (type moveit-container-t))
  `(moveit-container-pointer ,value))

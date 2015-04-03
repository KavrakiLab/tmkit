(in-package :tmsmt)

;;;;;;;;;;;;;;;;;;;;;;;;
;;; MOVEIT CONTAINER ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

(cffi:defcfun tms-container-create :pointer
  (node-handle :pointer)
  (robot-description :string))

(cffi:defcfun tms-container-destroy :void
  (pointer :pointer))

(defun container-create (node-handle
                         &key
                           (robot-description "robot_description"))
  (let ((pointer (with-deferred-signals
                   (tms-container-create (node-handle-pointer node-handle)
                                         robot-description))))
    (foreign-container-finalizer (make-moveit-container pointer)
                                 #'tms-container-destroy)))

(cffi:defcfun tms-container-variable-count :unsigned-long
  (container moveit-container-t))

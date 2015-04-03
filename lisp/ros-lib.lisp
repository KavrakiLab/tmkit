(in-package :tmsmt)

(cffi:define-foreign-library libtmsmt
    (:unix (:or #.(concatenate 'string (namestring (user-homedir-pathname))
                               "ros_ws/src/tmsmt/devel/lib/libtmsmt.so")
                "libtmsmt.so"))
  (t (:default "libtmsmt")))

(cffi:use-foreign-library libtmsmt)


(defstruct foreign-container
  pointer)


(defun foreign-container-finalizer (object destructor)
  "Register finalizer to call DESTRUCTOR on OBJECT's pointer.
RETURNS: OBJECT"
  (let ((pointer (foreign-container-pointer object)))
    (sb-ext:finalize object (lambda () (funcall destructor pointer))))
  object)


;;;;;;;;;;;
;;; ROS ;;;
;;;;;;;;;;;

(cffi:defcfun cros-init :void
  (argc :int)
  (argv :pointer)
  (name :string))

(cffi:defcfun getenv :string
  (key :string))

(defun ros-init (&key (name "lisp"))
  (unless (getenv "ROS_MASTER_URI")
    (error "cannot initialize: Undefined ROS_MASTER_URI variable"))
  (cros-init 0 (cffi::null-pointer) name))

(defstruct (node-handle (:include foreign-container)
                        (:constructor make-node-handle (pointer))))

(cffi:defcfun cros-node-handle-create :pointer
  (name :string))

(cffi:defcfun cros-node-handle-destroy :void
  (pointer :pointer))

(defun node-handle-create (name)
  (foreign-container-finalizer (make-node-handle (cros-node-handle-create name))
                               #'cros-node-handle-destroy))


;;;;;;;;;;;;;;;;;;;;;;;;
;;; MOVEIT CONTAINER ;;;
;;;;;;;;;;;;;;;;;;;;;;;;

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

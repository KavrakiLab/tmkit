(in-package :tmsmt)

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

(cffi:defcfun cros-node-handle-create :pointer
  (name :string))

(cffi:defcfun cros-node-handle-destroy :void
  (pointer :pointer))

(defun node-handle-create (name)
  (foreign-container-finalizer (make-node-handle (cros-node-handle-create name))
                               #'cros-node-handle-destroy))

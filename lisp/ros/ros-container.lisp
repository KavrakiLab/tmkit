(in-package :tmsmt)

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

(cffi:defcfun ("tms_container_variable_count" container-variable-count) :unsigned-long
  (container moveit-container-t))

(defun check-tms-result (result datum &rest arguments)
  (unless (zerop result)
    (apply #'error datum arguments)))

(cffi:defcfun tms-container-set-start :int
  (container moveit-container-t)
  (n-all amino::size-t)
  (q-all :pointer))

(defun container-set-start (container q-all)
  (let ((result (amino::with-dynamic-vector-foreign (q-all n-all) q-all
                  (tms-container-set-start container n-all q-all))))
    (check-tms-result result "set-start")))

(cffi:defcfun tms-container-set-group :int
  (container moveit-container-t)
  (group :string))

(defun container-set-group (container group)
  (let ((result (tms-container-set-group container group)))
    (check-tms-result result "set-group")))

(cffi:defcfun tms-container-goal-clear :int
  (container moveit-container-t))

(defun container-goal-clear (container)
  (let ((result (tms-container-goal-clear container)))
    (check-tms-result result "goal-clear")))

(cffi:defcfun tms-container-set-ws-goal :int
  (container moveit-container-t)
  (link :string)
  (quat amino::quaternion-t)
  (vec amino::vector-3-t)
  (tolerance-position :double)
  (tolerance-angle :double))

(defun container-set-ws-goal (container link tf &key
                                                 (position-tolerance .5d-2)
                                                 (angle-tolerance (* 1 (/ pi 180))))
  (let ((result (tms-container-set-ws-goal container link
                                           (amino:rotation tf)
                                           (amino:translation tf)
                                           position-tolerance
                                           angle-tolerance)))
    (check-tms-result result "set-ws-goal")))


(cffi:defcfun tms-container-group-fk :int
  (container moveit-container-t)
  (group :string)
  (n-group amino::size-t)
  (q-group :pointer)
  (quat amino::quaternion-t)
  (vec amino::vector-3-t))

(defun container-group-fk (container group q-group &optional tf)
  (let ((tf (if tf tf (amino:quaternion-translation nil))))
    (let ((result (amino::with-dynamic-vector-foreign (q-group n-group) q-group
                    (tms-container-group-fk container group n-group q-group
                                            (amino::quaternion-translation-quaternion tf)
                                            (amino::quaternion-translation-translation tf)))))
      (check-tms-result result "group-fk"))
    tf))

(cffi:defcfun tms-container-link-fk :int
  (container moveit-container-t)
  (link :string)
  (n-link amino::size-t)
  (q-link :pointer)
  (quat amino::quaternion-t)
  (vec amino::vector-3-t))

(defun container-link-fk (container link q-link &optional tf)
  (let ((tf (if tf tf (amino:quaternion-translation nil))))
    (let ((result (amino::with-dynamic-vector-foreign (q-link n-link) q-link
                    (tms-container-link-fk container link n-link q-link
                                            (amino::quaternion-translation-quaternion tf)
                                            (amino::quaternion-translation-translation tf)))))
      (check-tms-result result "link-fk"))
    tf))

(cffi:defcfun ("tms_container_group_endlink" container-group-endlink) :string
  (container moveit-container-t)
  (group :string))

(cffi:defcfun tms-container-plan :int
  (container moveit-container-t))

(defun container-plan (container)
  (tms-container-plan container))

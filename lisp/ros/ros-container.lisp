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
  (let ((result (amino-ffi:with-foreign-simple-vector (q-all n-all) q-all :input
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
    (let ((result (amino-ffi:with-foreign-simple-vector (q-group n-group) q-group :input
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
    (let ((result (amino-ffi:with-foreign-simple-vector (q-link n-link) q-link :input
                    (tms-container-link-fk container link n-link q-link
                                            (amino::quaternion-translation-quaternion tf)
                                            (amino::quaternion-translation-translation tf)))))
      (check-tms-result result "link-fk"))
    tf))

(cffi:defcfun ("tms_container_group_endlink" container-group-endlink) :string
  (container moveit-container-t)
  (group :string))

(cffi:defcfun ("tms_container_group_joint_count" container-group-joint-count) amino-ffi:size-t
  (container moveit-container-t)
  (group :string))

(cffi:defcfun ("tms_container_group_joint_name" container-group-joint-name) :string
  (container moveit-container-t)
  (group :string)
  (i amino-ffi:size-t))


(defun container-group-configuration-map (container group q-group)
  (let ((map (make-tree-map #'string-compare)))
    (dotimes (i (length q-group))
      (tree-map-insertf map
                        (container-group-joint-name container group i)
                        (vecref q-group i)))
    map))

(cffi:defcfun tms-container-plan :int
  (container moveit-container-t)
  (n-vars :pointer)
  (n-points :pointer)
  (points :pointer))

(cffi:defcfun tms-container-merge-group :int
  (container moveit-container-t)
  (group :string)
  (n-group amino-ffi:size-t)
  (q-group :pointer)
  (n-all amino-ffi:size-t)
  (q-all :pointer))

(defun container-merge-group (container group-name q-group q-all)
  (let ((q-all (copy-seq q-all)))
    (check-type q-group (simple-array double-float (*)))
    (check-type q-all (simple-array double-float (*)))
    (amino-ffi:with-foreign-simple-vector (q-all n-all) q-all :output
      (amino-ffi:with-foreign-simple-vector (q-group n-group) q-group :input
        (tms-container-merge-group container group-name
                                   n-group q-group
                                   n-all q-all)))))

(defun container-plan (container)
  (cffi:with-foreign-objects ((n-vars 'amino-ffi:size-t)
                              (n-points 'amino-ffi::size-t)
                              (points :pointer))
    (let ((result (tms-container-plan container n-vars n-points points)))
      (if (< result 0)
          (progn
            (format t "~&CL: Planning failed: ~D~%" result)
             nil)
          (let ((n-vars (cffi:mem-ref n-vars 'amino-ffi:size-t))
                (n-points (cffi:mem-ref n-points 'amino-ffi:size-t))
                (points (cffi:mem-ref points :pointer)))
            (when points
              (prog1
                  (loop for i below n-points
                     for vec = (make-vec n-vars)
                     collect
                       (cffi:with-pointer-to-vector-data (ptr vec)
                         (amino-ffi:libc-memcpy ptr
                                                (cffi:inc-pointer points
                                                                  (* 8 i n-vars))
                                                (* 8 n-vars))
                         vec))
                (amino-ffi:libc-free points))))))))

(defun container-plan-endpoint (plan)
  (car (last plan)))

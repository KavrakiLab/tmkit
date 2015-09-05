(in-package :tmsmt)


(cffi:defcfun syn-handle-create :pointer
  (n-obj amino-ffi:size-t)
  (obj-location in-array-size-t)
  (n-location amino-ffi:size-t)
  (n-label in-array-size-t)
  (labels-array :pointer))

(cffi:defcfun syn-handle-destroy :void
  (handle :pointer))

(cffi:defcfun syn-handle-goal :void
  (handle syn-handle-t)
  (n-goal-obj amino-ffi:size-t)
  (obj-index in-array-size-t)
  (obj-label in-array-size-t))


(cffi:defcfun syn-handle-plan :void
  (handle syn-handle-t)
  (plan :pointer))

(cffi:defcfun syn-handle-update-weight :void
  (handle syn-handle-t)
  (failed-step amino-ffi:size-t)
  (substep :int))

(cffi:defcstruct syn-plan
  (n-step amino-ffi:size-t)
  (src-object :pointer)
  (dst-location :pointer))

(defstruct syn-data
  location-names
  object-names
  label-names
  object-locations
  location-labels
  goal-objects
  goal-labels)

(defun syn-state-location-indices (state locations)
  (map 'list (lambda (x)
               (destructuring-bind (name parent i j)
                   x
                 (declare (ignore name))
                 (position (itmp-encode-location parent i j)
                           locations :test #'equal)))
       state))

(defun syn-data (init-scene goal-scene &key
                                         max-locations
                                         (resolution *resolution*))
  (let* ((locations (scene-locations init-scene resolution :max-count max-locations))
         (moveable-frames (scene-collect-type init-scene "moveable"))
         (moveable-objects (map 'list #'robray::scene-frame-name moveable-frames))
         (state (scene-state-pairs init-scene :resolution resolution))
         (goal-state (scene-state-pairs goal-scene :resolution resolution)))
    (make-syn-data :location-names locations
                   :object-names moveable-objects
                   :label-names locations
                   :object-locations (syn-state-location-indices state locations)
                   :location-labels (loop for x in locations
                                       for i from 0
                                       collect (list i))
                   :goal-objects (map 'list (lambda (x)
                                              (position (car x) moveable-objects
                                                        :test #'equal))
                                      goal-state)
                   :goal-labels (syn-state-location-indices goal-state locations))))

(defun syn-destroy (container)
  (syn-handle-destroy container))

(defun syn-create (data)
  (let ((n-obj (length (syn-data-object-names data)))
        (n-loc (length (syn-data-location-names data)))
        (n-goal (length (syn-data-goal-objects data))))
    (assert (= n-goal (length (syn-data-goal-labels data))))
    (cffi:with-foreign-object (lbls :pointer n-loc)
      ;; fill location labels
      (loop for i below n-loc
         for lbl in (syn-data-location-labels data)
         for n = (length lbl)
         ;; alloc label array
         for array = (cffi:foreign-alloc 'amino-ffi:size-t :count n)
         do (progn
              ;; set label count and alloc array
              (setf (cffi:mem-aref lbls :pointer i) array)
              ;; fill label array
              (loop for j below n
                 for k in lbl
                 do (setf (cffi:mem-aref array 'amino-ffi:size-t j)
                          k))))
      (let* ((pointer (syn-handle-create n-obj (syn-data-object-locations data)
                                         n-loc (map 'list #'length (syn-data-location-labels data))
                                         lbls))
             ;; finalizer
             (container (foreign-container-finalizer (make-syn-container :pointer pointer)
                                                     #'syn-destroy)))
        ;; free
        (loop for i below n-loc
           for lbl in (syn-data-location-labels data)
           for n = (length lbl)
           do ;; free label array
             (cffi:foreign-free (cffi:mem-aref lbls :pointer i)))
        ;; goal
        (syn-handle-goal container n-goal
                         (syn-data-goal-objects data)
                         (syn-data-goal-labels data))
        ;; result
        container))))

(defun syn-plan (container data)
  (cffi:with-foreign-object (plan '(:struct syn-plan))
    (print 'calling-plan)
    (syn-handle-plan container plan)
    (print 'finished-plan)
    (let ((src-obj (cffi:foreign-slot-value plan '(:struct syn-plan) 'src-object))
          (dst-loc (cffi:foreign-slot-value plan '(:struct syn-plan) 'dst-location))
          (n-step (cffi:foreign-slot-value plan '(:struct syn-plan) 'n-step)))
      (prog1
          (loop for i below n-step
             for i-obj = (cffi:mem-aref src-obj 'amino-ffi:size-t i)
             for i-dst = (cffi:mem-aref dst-loc 'amino-ffi:size-t i)
             collect (list* "TRANSFER"
                           (elt (syn-data-object-names data) i-obj)
                           (smt-unmangle (elt (syn-data-location-names data) i-dst))))
        (cffi:foreign-free src-obj)
        (cffi:foreign-free dst-loc)))))

(defun syn-update-weight (container step substep)
  (syn-handle-update-weight container step substep))

(defun itmp-syn (init-graph goal-graph
                 &key
                   (encoding :linear)
                   ;(action-encoding :boolean)
                   max-locations
                   (resolution 0.2d0)
                   (plan-context *plan-context*)
                   (frame "right_endpoint") ;; FIXME
                   (link *link*)
                   (group *group*))
  (let* ((time-0 (get-internal-real-time))
         (cache (make-hash-table :test #'equal))
         (motion-time 0)
         (task-time 0)
         (init-graph (scene-graph init-graph))
         (goal-graph (scene-graph goal-graph))
         (data (syn-data init-graph goal-graph
                         :max-locations max-locations
                         :resolution resolution))
         (handle (syn-create data))
         (plan-steps))
    (setq *itmp-cache* cache)
    (labels ((next ()
               (itmp-abort)
               (setq plan-steps nil)
               (multiple-value-bind (plan run-time)
                   (sycamore-util:with-timing (syn-plan handle data))
                 (incf task-time run-time)
                 (print plan)
                 (cache plan)))
             (cache (plan)
               (let* ((prefixes (reverse (loop
                                            for trail on (reverse plan)
                                            collect trail)))
                      (prefix
                       (loop for p in prefixes
                          for n in (cdr prefixes)
                          for has-p = (gethash p cache)
                          for has-n = (gethash n cache)
                          until (not has-n)
                          finally (return p))))
                 (if (gethash prefix cache)
                     (let ((c (gethash prefix cache)))
                       (format t "~&prefix: ~A" prefix)
                       (setq plan-steps (first c))
                       (rec (subseq plan (length prefix))
                            (car plan-steps)
                            (second c)
                            prefix
                            *q-all-start*))
                     (progn
                       (format t "~&prefix: none")
                       (reify plan
                              init-graph *q-all-start*
                              nil)))))
             ;; Find a prefix
             (rec (task-plan plan graph trail start)
               (let* ((group-start (container-plan-endpoint (third plan)))
                      (all-start (container-merge-group *moveit-container* *group*
                                                        group-start start)))
                 (reify task-plan graph all-start trail)))
             (reify (task-plan graph start trail)
               (declare (type list task-plan)
                        (type robray::scene-graph graph))
               (itmp-abort)
               (when task-plan
                 (let* ((op (car task-plan))
                        (task-plan (cdr task-plan))
                        (trail (cons op trail)))
                   (cond
                     ((equal (car op) "NO-OP")
                      (push :no-op plan-steps))
                     (t
                      (format t "~&Reify: ~A..." op)
                      (multiple-value-bind (plan graph)
                          (multiple-value-bind (result run-time)
                              (sycamore-util:with-timing
                                (multiple-value-list
                                 (itmp-transfer-action graph op
                                                       :encoding encoding
                                                       :resolution resolution
                                                       :plan-context plan-context
                                                       :link link
                                                       :frame frame
                                                       :group group
                                                       :q-all-start start)))
                            (incf motion-time run-time)
                            (apply #'values result))
                        (declare (type list plan)
                                 (type robray::scene-graph graph))
                        (if plan
                            (progn
                              (format t "success.~%")
                              (push plan plan-steps)
                              (setf (gethash trail cache)
                                    (list plan-steps graph))
                              (rec task-plan plan graph trail start))
                            (progn
                              (format t "failure.~%")
                              (abort))))))))))
      (next))
    (setq *itmp-task-time* task-time
          *itmp-motion-time* motion-time
          *itmp-total-time* (coerce (/ (- (get-internal-real-time) time-0)
                                         internal-time-units-per-second)
                                      'double-float))
    (setq *itmp-int-time* (max (- *itmp-total-time*
                                  (+ *itmp-task-time* *itmp-motion-time*))
                               0))
    (format t "~&IDITMP -- total time:  ~,3F~&" *itmp-total-time*)
    (format t "~&IDITMP -- task time:   ~,3F~&" *itmp-task-time*)
    (format t "~&IDITMP -- motion time: ~,3F~&" *itmp-motion-time*)
    (format t "~&IDITMP -- int. time:   ~,3F~&" *itmp-int-time*)
    (apply #'append (reverse plan-steps))))

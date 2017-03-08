(in-package :tmsmt)

(define-condition planning-failure (error)
  ((operator :initarg :operator)
   (value :initarg :value)
   (scene-graph :initarg :scene-graph)
   (planner :initarg :planner)))


(defstruct tm-op
  "Abstract type for a task-motion operator"
  initial-scene-graph
  initial-config
  final-scene-graph
  final-config)

(deftype tm-op-maybe ()
  `(or null tm-op))


(defstruct (tm-op-nop (:include tm-op))
  "Operator type for a No-Op.")

(defun tm-op-nop (scene config)
  "Construct a no-op."
  (make-tm-op-nop :initial-scene-graph scene
                  :initial-config config
                  :final-scene-graph scene
                  :final-config config))

(defstruct (tm-op-action (:include tm-op))
  "Operator type for a task action."
  action)

(defun tm-op-action (action scene-graph config)
  "Construct an operator for a task action."
  (make-tm-op-action :initial-scene-graph scene-graph
                     :initial-config config
                     :final-scene-graph scene-graph
                     :final-config config
                     :action action))



(defstruct (tm-op-reparent (:include tm-op))
  "Operator type for a reparent."
  frame
  new-parent)

(defun tm-op-reparent (scenegraph new-parent frame &key
                                                     configuration-map)
  "Construct an operator for a reparent."
  (make-tm-op-reparent :frame frame
                       :new-parent new-parent
                       :initial-config configuration-map
                       :final-config configuration-map
                       :initial-scene-graph scenegraph
                       :final-scene-graph (scene-graph-reparent scenegraph new-parent frame
                                                                :configuration-map configuration-map)))


(defstruct (tm-op-motion (:include tm-op))
  "Operator type for a motion plan."
  motion-plan)

(defun tm-op-motion (motion-plan)
  "Construct a TM-OP for a motion plan."
  (make-tm-op-motion :motion-plan motion-plan
                     :final-config (robray::motion-plan-endpoint-map motion-plan)
                     :initial-scene-graph (robray::motion-plan-scene-graph motion-plan)
                     :final-scene-graph (robray::motion-plan-scene-graph motion-plan)))

(defstruct (tm-plan (:include tm-op))
  "Container for a task-motion-plan."
  ops)

(defun tm-plan-list (ops)
  (labels ((rec (ops)
             (etypecase ops
               (tm-plan
                (rec (tm-plan-ops ops)))
               (tm-op-nop
                nil)
               (list
                (loop for op in ops
                   nconc (rec op)))
               (vector
                (loop for op across ops
                   nconc (rec op)))
               (tm-op (list ops)))))
    (let* ((ops (rec ops))
           (first (first ops))
           (last (car (last ops))))
      (declare (type tm-op first last))
      (make-tm-plan :ops ops
                    :initial-scene-graph (tm-op-initial-scene-graph first)
                    :initial-config (tm-op-initial-config first)
                    :final-scene-graph (tm-op-final-scene-graph last)
                    :final-config (tm-op-final-config last)))))

(defun tm-plan (&rest ops)
  "Construct a TM-PLAN for the given operators."
  (tm-plan-list ops))

(defun tm-plan-motion-plans (tm-plan)
  "Return a list of the motion plans contained in tm-plan."
  (loop for op in (tm-plan-ops tm-plan)
     when (tm-op-motion-p op)
     collect (tm-op-motion-motion-plan op)))

(defun tm-plan-endpoint (tm-plan)
  "Return the final configuration in TM-PLAN."
  (loop
     for a = tm-plan then b
     for b = (cddr a)
     while b
     finally (return (motion-plan-endpoint-map (car a)))))

(defmethod object-rope ((object tm-op-action))
  (format nil "a ~{~A~^ ~}~%" (ensure-list (tm-op-action-action object))))

(defmethod object-rope ((object tm-op-reparent))
  (format nil "r ~A ~A~%"
          (tm-op-reparent-frame object)
          (tm-op-reparent-new-parent object)))

(defmethod object-rope ((object tm-op-motion))
  (let* ((mp (tm-op-motion-motion-plan object))
         (names (robray::motion-plan-config-names-list mp))
         (path-list (robray::motion-plan-path-list mp)))
    ;; Check lengths
    (loop
       with m = (length names)
       for point in path-list
       do (assert (= m
                     (length point))))
    ;; Result
    (rope
     (format nil "~&m ~{~A ~}~%" names)
     (format nil "~{p ~{~F	~}~%~}"
             path-list))))

(defmethod configuration-map-string (config)
  (with-output-to-string (s)
    (let* ((keys (tree-map-keys config))
           (values  (map 'list (lambda (k) (tree-map-find config k)) keys)))
      (format s "m ~{~A~^ ~}~%" keys)
      (format s "p ~{~F~^ ~}~%" values))))

(defmethod object-rope ((object tm-plan))
  (rope (configuration-map-string (tm-plan-initial-config object))
        (tm-plan-ops object)))


(defun tm-op-tf-abs (op frame)
  (robray::scene-graph-tf-absolute (tm-op-final-scene-graph op)
                                   frame
                                   :configuration-map (tm-op-final-config op)))

(defun tm-op-tf-rel (op parent child)
  (robray::scene-graph-tf-relative (tm-op-final-scene-graph op)
                                    parent child
                                    :configuration-map (tm-op-final-config op)))

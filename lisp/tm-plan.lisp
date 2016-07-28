(in-package :tmsmt)

(defstruct tm-op
  initial-scene-graph
  initial-config
  final-scene-graph
  final-config)

(deftype tm-op-maybe ()
  `(or null tm-op))


(defstruct (tm-op-action (:include tm-op))
  action)

(defun tm-op-action (action scene-graph config)
  (make-tm-op-action :initial-scene-graph scene-graph
                     :initial-config config
                     :final-scene-graph scene-graph
                     :final-config config
                     :action action))



(defstruct (tm-op-reparent (:include tm-op))
  frame
  new-parent)

(defun tm-op-reparent (scenegraph new-parent frame &key
                                                    configuration-map)
  (make-tm-op-reparent :frame frame
                       :new-parent new-parent
                       :initial-config configuration-map
                       :final-config configuration-map
                       :initial-scene-graph scenegraph
                       :final-scene-graph (scene-graph-reparent scenegraph new-parent frame
                                                                :configuration-map configuration-map)))


(defstruct (tm-op-motion (:include tm-op))
  motion-plan)

(defun tm-op-motion (motion-plan)
  (make-tm-op-motion :motion-plan motion-plan
                     :final-config (robray::motion-plan-endpoint-map motion-plan)
                     :initial-scene-graph (robray::motion-plan-scene-graph motion-plan)
                     :final-scene-graph (robray::motion-plan-scene-graph motion-plan)))

(defstruct (tm-plan (:include tm-op))
  ops)

(defun tm-plan-list (ops)
  (declare (type list ops))
  (let* ((ops (loop for op in ops ; flatten subplans
                 when op
                 nconc (if (tm-plan-p op)
                           (tm-plan-ops op)
                           (list op))))
         (first (first ops))
         (last (car (last ops))))
    (declare (type tm-op first last))
    (make-tm-plan :ops ops
                  :initial-scene-graph (tm-op-initial-scene-graph first)
                  :initial-config (tm-op-initial-config first)
                  :final-scene-graph (tm-op-final-scene-graph last)
                  :final-config (tm-op-final-config last))))

(defun tm-plan (&rest ops)
  (tm-plan-list ops))

(defun tm-plan-motion-plans (tm-plan)
  (loop for op in (tm-plan-ops tm-plan)
     when (tm-op-motion-p op)
     collect (tm-op-motion-motion-plan op)))

(defun tm-plan-endpoint (tm-plan)
  (loop
     for a = tm-plan then b
     for b = (cddr a)
     while b
     finally (return (motion-plan-endpoint-map (car a)))))

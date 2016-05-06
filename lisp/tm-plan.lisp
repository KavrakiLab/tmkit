(in-package :tmsmt)


(defstruct tm-op-reparent
  frame
  new-parent
  new-scene-graph)



(defun tm-op-reparent (scenegraph new-parent frame &key
                                                     configuration-map)
  (make-tm-op-reparent :frame frame
                       :new-parent new-parent
                       :new-scene-graph (scene-graph-reparent scenegraph new-parent frame
                                                              :configuration-map configuration-map)))


(defstruct (tm-op-motion (:include robray::motion-plan)))

(defun tm-op-motion-scene-graph (op)
  (robray::motion-plan-scene-graph op))

(defstruct tm-op
  action
  ops)

(defstruct tm-plan
  scene-graph
  ops)


(defun tm-plan-motion-plans (tm-plan)
  (loop for rest = tm-plan then (cddr rest)
     while rest
     collect (car rest)))

(defun tm-plan-endpoint (tm-plan)
  (loop
     for a = tm-plan then b
     for b = (cddr a)
     while b
     finally (return (motion-plan-endpoint-map (car a)))))

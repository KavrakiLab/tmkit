(in-package :tmsmt)

(defun point-config-map (container group point)
  (let ((map (make-tree-map #'robray::frame-name-compare)))
    (loop
       for q across point
       for i from 0
       do (tree-map-insertf map
                            (container-group-joint-name container group i)
                            q))
    map))


(defun render-group-plan (context group plan)
  (let* ((container (plan-context-moveit-container context))
         (config-map-list
          (loop for points in plan
             collect (point-config-map container group points)))
         (scene-graph (robray::scene-graph-merge (plan-context-robot-graph context)
                                                 (plan-context-object-graph context))))
    (flet ((frame-config-fun (frame)
             (if (< frame (length config-map-list))
                 (elt config-map-list frame)
                 nil)))
      (robray::scene-graph-frame-animate #'frame-config-fun
                                         :include "baxter.inc"
                                         :scene-graph scene-graph))))

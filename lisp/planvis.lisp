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


(defun render-group-plan (container group plan)
  (let ((config-map-list
         (loop for points in plan
            collect (point-config-map container group points))))
    (flet ((frame-config-fun (frame)
             (if (< frame (length config-map-list))
                 (elt config-map-list frame)
                 nil)))
      ;; TODO: store scene-graph in container
      (robray::scene-graph-frame-animate #'frame-config-fun
                                         :include "baxter.inc"))))

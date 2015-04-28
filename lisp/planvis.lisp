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


(defun render-group-plan (context group plan
                          &key
                            (width robray::*width*)
                            (height robray::*height*)
                            (frames-per-second robray::*frames-per-second*))
  (let* ((container (plan-context-moveit-container context))
         (config-map-list
          (loop
             for rest on plan
             for points = (first rest)
             for next = (second rest)
             append
               (append (list (point-config-map container group points))
                       (when next
                             (list (point-config-map container group (g* 0.5 (g+ points next))))))))
         (scene-graph (robray::scene-graph-merge (plan-context-robot-graph context)
                                                 (plan-context-object-graph context))))
    (flet ((frame-config-fun (frame)
             (if (< frame (length config-map-list))
                 (elt config-map-list frame)
                 nil)))
      (robray::scene-graph-frame-animate #'frame-config-fun
                                         :height height
                                         :width width
                                         :frames-per-second frames-per-second
                                         :include "baxter.inc" ;; TODO: fix this
                                         :scene-graph scene-graph))))



(defun render-group-config (context group config)
  (let* ((container (plan-context-moveit-container context))
         (config-map (point-config-map container group config))
         (scene-graph (robray::scene-graph-merge (plan-context-robot-graph context)
                                                 (plan-context-object-graph context))))
    (robray::pov-render (robray::scene-graph-pov-frame scene-graph
                                                       :configuration-map config-map
                                                       :include "baxter.inc" ;; TODO: fix this
                                                       )
                        :directory "/tmp/robray/"
                        :file "tmsmt.pov"
                        :output "tmsmt.png")))

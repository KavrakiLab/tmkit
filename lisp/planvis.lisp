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


(defun render-group-itmp (context group itmp
                          &key
                            frame-name
                            scene-graph
                            (output-directory robray::*robray-tmp-directory*)
                            (width robray::*width*)
                            (height robray::*height*)
                            (quality robray::*quality*)
                            (render-frames t)
                            (encode-video t)
                            (frames-per-second robray::*frames-per-second*))
  (map nil #'delete-file (robray::frame-files output-directory))
  (labels ((motion-action-p (action)
             (arrayp (elt action 0))))
    (loop
       with container = (plan-context-moveit-container context)
       with config-map
       with frame-number = 0
       for action in itmp
       do
         (if (motion-action-p action)
              (flet ((frame-config-fun (n)
                       (let ((i (- n frame-number)))
                         (if (< i (length action))
                             (setq config-map (point-config-map container group (elt action i)))
                             nil))))
                (robray::scene-graph-frame-animate #'frame-config-fun
                                                   :height height
                                                   :width width
                                                   :append t
                                                   :render-frames nil
                                                   :frames-per-second frames-per-second
                                                   :include "baxter.inc" ;; TODO: fix this
                                                   :scene-graph scene-graph)
                (incf frame-number (length action)))
              (destructuring-ecase action
                ((:pick object)
                 (setq scene-graph (robray::scene-graph-reparent scene-graph frame-name object
                                                                 :configuration-map config-map)))
                ((:place object)
                 (setq scene-graph (robray::scene-graph-reparent scene-graph nil object
                                                                 :configuration-map config-map)))))))
  ;; Render
  (when render-frames
    (robray::net-render :height height
                        :width width
                        :quality quality)
    ;; Encode Video
    (when encode-video
      (robray::animate-encode :frames-per-second frames-per-second))))

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

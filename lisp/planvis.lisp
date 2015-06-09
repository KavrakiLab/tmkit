(in-package :tmsmt)

(defun point-config-map (container group point)
  (let ((map (make-tree-map #'robray::frame-name-compare)))
    (loop
       for q across point
       for i from 0
       for name = (container-group-joint-name container group i)
       do (setf (tree-map-find map name) q))
    map))


(defun render-group-plan (context group plan
                          &key
                            (render-options robray::*render-options*))
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
         (scene-graph (robray::scene-graph (plan-context-robot-graph context)
                                           (plan-context-object-graph context))))
    (flet ((frame-config-fun (frame)
             (if (< frame (length config-map-list))
                 (elt config-map-list frame)
                 nil)))
      (robray::scene-graph-frame-animate #'frame-config-fun
                                         :options render-options
                                         :include "baxter.inc" ;; TODO: fix this
                                         :scene-graph scene-graph))))

(defun plan-interpolate (plan)
  (loop
     for rest on plan
     for points = (first rest)
     for next = (second rest)
     nconc
       (nconc (list points)
              (when next
                (list (g* 0.5 (g+ points next)))))))

(defun render-group-itmp (context group itmp
                          &key
                            frame-name
                            scene-graph
                            (output-directory robray::*robray-tmp-directory*)
                            (render-options robray::*render-options*))
  (map nil #'delete-file (robray::frame-files output-directory))
  (labels ((motion-action-p (action)
             (arrayp (elt action 0))))
    (loop
       with fps = (get-render-option render-options :frames-per-second)
       with container = (plan-context-moveit-container context)
       with config-map
       with frame-number = 0
       for action in itmp
       do
         (if (motion-action-p action)
             (let* ((action (if (> fps 15)
                                (plan-interpolate action)
                                action)))
               (flet ((frame-config-fun (n)
                        (let ((i (- n frame-number)))
                          (if (< i (length action))
                              (setq config-map (point-config-map container group (elt action i)))
                              nil))))
                 (robray::scene-graph-frame-animate #'frame-config-fun
                                                    :options render-options
                                                    :append t
                                                    :render-frames nil
                                                    :include "baxter.inc" ;; TODO: fix this
                                                    :scene-graph scene-graph))
                (incf frame-number (length action)))
              (destructuring-ecase action
                ((:pick object)
                 (setq scene-graph (robray::scene-graph-reparent scene-graph frame-name object
                                                                 :configuration-map config-map)))
                ((:place object)
                 (setq scene-graph (robray::scene-graph-reparent scene-graph nil object
                                                                 :configuration-map config-map)))))))
  ;; Render
  (when (robray::get-render-option render-options :render-frames)
    (robray::net-render :directory output-directory
                        :options render-options)
    ;; Encode Video
    (when (robray::get-render-option render-options :encode-video)
      (robray::animate-encode :options render-options))))

(defun render-group-config (context group config &key
                                                   (options (render-options-medium)))
  (let* ((container (plan-context-moveit-container context))
         (config-map (point-config-map container group config))
         (scene-graph (robray::scene-graph (plan-context-robot-graph context)
                                           (plan-context-object-graph context))))
    (robray::pov-render (robray::scene-graph-pov-frame scene-graph
                                                       :options options
                                                       :configuration-map config-map
                                                       :include "baxter.inc" ;; TODO: fix this
                                                       )
                        :options options
                        :directory "/tmp/robray/"
                        :file "tmsmt.pov"
                        :output "tmsmt.png")))

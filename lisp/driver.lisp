(in-package :tmsmt)


;; FIXME: where does this go?
(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .075)))

(defun tmp-driver (&key
                     task-domain
                     start-scene
                     goal-scene
                     gui
                     verbose
                     (max-steps 3)
                     (resolution .15)
                     ;; FIXME:
                     output
                     (encoding :linear)
                     (frame "right_endpoint")
                     (start (robray::alist-configuration-map `(("right_s0" . ,(/ pi 5)))))
                     )

  (when verbose
    (format t "~&Start scene files: ~{~A~^, ~}~%" (ensure-list start-scene))
    (format t "~&Goal scene files:  ~{~A~^, ~}~%" (ensure-list goal-scene)))
  ;; Check parameters
  (unless start-scene
    (error "TMSMT: No start scene specified."))
  (unless goal-scene
    (error "TMSMT: No goal scene specified."))
  (unless task-domain
    (error "TMSMT: No task domain specified."))
  (unless frame
    (error "TMSMT: No frame specified."))
  ;; gen scenes
  (let ((start-scene-graph (robray::load-scene-files start-scene))
        (goal-scene-graph (robray::load-scene-files goal-scene))
        (output (or output *standard-output*)))
    (finish-output *standard-output*)
    ;; Maybe display scene
    (when gui
      (robray::win-set-scene-graph start-scene-graph)
      (robray::win-set-config start))
    ;;(break)
    ;; Now plan!
    (let ((plan (itmp-rec start-scene-graph goal-scene-graph
                          task-domain
                          :q-all-start start
                          :frame frame
                          :encoding encoding
                          :max-steps max-steps
                          :resolution resolution)))
      ;; Maybe display scene
      (when (and plan gui)
        (robray::win-display-motion-plan-sequence (tm-plan-motion-plans plan)))

      (if plan
          (output-rope (rope (loop for scene in start-scene
                                collect (rope "# Start Scene: " scene #\Newline))
                             (rope "# Task Domain: " task-domain #\Newline)
                             (loop for scene in goal-scene
                                collect (rope "# Goal Scene: " scene #\Newline))
                             (object-rope plan))
                       output :if-exists :supersede)
          (format *error-output* "~&ERROR: no plan found.~&"))
      plan)))

;; TODO: start configuration

(defun tmp-command ()
  (let* ((scene-files (read-from-string (concatenate 'string "("
                                                     (uiop/os:getenv "TMSMT_SCENE_FILES")
                                                     ")")))
         (goal-files (read-from-string (concatenate 'string "("
                                                    (uiop/os:getenv "TMSMT_GOAL_FILES")
                                                    ")")))
         (max-steps (if-let ((s (uiop/os:getenv "TMSMT_MAX_STEPS")))
                      (parse-integer s)
                      5))
         (resolution (if-let ((s (uiop/os:getenv "TMSMT_RESOLUTION")))
                       (parse-float s)
                       .1))
         (plan-file (uiop/os:getenv "TMSMT_INPUT"))
         (gui (or (uiop/os:getenv "TMSMT_GUI")
                  plan-file)))
    (when gui
      (robray::win-create :title "TMSMT"
                          :stop-on-quit t))
    (if plan-file
        ;; Load and display plan
        (display-tm-plan-file scene-files nil plan-file)
        ;; Find the plan
        (tmp-driver :start-scene scene-files
                    :goal-scene goal-files
                    :task-domain (uiop/os:getenv "TMSMT_TASK_DOMAIN")
                    :max-steps max-steps
                    :resolution resolution
                    :gui gui
                    :output (uiop/os:getenv "TMSMT_OUTPUT")
                    :verbose (uiop/os:getenv "TMSMT_VERBOSE")))
    ;; Join the window thread
    (when gui
      (robray::win-join))))

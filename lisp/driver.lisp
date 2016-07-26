(in-package :tmsmt)



(defun tmp-driver (&key
                     task-domain
                     start-scene
                     goal-scene
                     gui
                     verbose
                     ;; FIXME:
                     (frame "right_endpoint")
                     (start (robray::alist-configuration-map `(("right_s0" . ,(/ pi 5)))))
                     (encoding :linear)
                     (max-steps 3)
                     (resolution .15)
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
  ;; gen scenes
  (let ((start-scene-graph (robray::load-scene-files start-scene))
        (goal-scene-graph (robray::load-scene-files goal-scene)))
    (finish-output *standard-output*)
    ;; Maybe display scene
    (when gui
      (robray::win-set-scene-graph start-scene-graph)
      (robray::win-set-config start))
    ;;(break)
    ;; Now plan!
    (let ((plan (itmp-rec start-scene goal-scene
                          task-domain
                          :q-all-start start
                          :frame frame
                          :encoding encoding
                          :max-steps max-steps
                          :resolution resolution)))
      ;; Maybe display scene
      (when (and plan gui)
        (robray::win-display-motion-plan-sequence (tm-plan-motion-plans plan)))

      (unless plan
        (format *error-output* "~&ERROR: no plan found.~&"))
      )

    (values)))


(defun tmp-command ()
  (let ((gui (uiop/os:getenv "TMSMT_GUI"))
        (scene-files (read-from-string (concatenate 'string "("
                                                    (uiop/os:getenv "TMSMT_SCENE_FILES")
                                                    ")")))
        (goal-files (read-from-string (concatenate 'string "("
                                                   (uiop/os:getenv "TMSMT_GOAL_FILES")
                                                   ")"))))


    (when gui
      (robray::win-create :title "TMSMT"
                          :stop-on-quit t))
    (tmp-driver :start-scene scene-files
                :goal-scene goal-files
                :gui gui
                :verbose (uiop/os:getenv "TMSMT_VERBOSE"))
    (when (uiop/os:getenv "TMSMT_PAUSE")
      (format t "~&Press enter to continue.~&")
      (read-line *standard-input* nil nil)
      (robray::win-stop))
    ;; Join the window thread
    (when gui
      (robray::win-join)))
)
(in-package :tmsmt)


;; FIXME: where does this go?
(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .075)))

(defun tmp-script (pathname)
  (let* ((pathname (pathname pathname))
         (type (string-downcase (pathname-type pathname))))
    (cond
      ;; CLPython Script
      ((string= type "py")
       (clpython:run pathname))
      ;; Lisp Script
      ((find type '("lisp" "l") :test #'string=)
       (load pathname))
      (t (error "Unrecognized file type `~A' of file `~A'"
                type pathname)))))


(defun tmp-driver (&key
                     task-domain
                     start-scene
                     goal-scene
                     task-facts
                     gui
                     scripts
                     verbose
                     (max-steps 10)
                     ;; FIXME:
                     output
                     write-facts
                     (start (robray::alist-configuration-map `(("right_s0" . ,(/ pi 5)))))
                     )

  (when verbose
    (format t "~&Start scene files: ~{~A~^, ~}~%" (ensure-list start-scene))
    (format t "~&Goal scene files:  ~{~A~^, ~}~%" (ensure-list goal-scene)))

  ;; Load Scripts
  (map nil #'tmp-script scripts)

  ;; Load scenes
  (let ((start-scene-graph (robray::load-scene-files start-scene))
        (goal-scene-graph (robray::load-scene-files goal-scene))
        (output (or output *standard-output*)))
    (finish-output *standard-output*)

    ;; Maybe write facts
    (when write-facts
      (format t "~&Write Facts: ~A~%" write-facts)
      (output-rope (pddl-exp-rope (scene-facts start-scene-graph goal-scene-graph
                                               :configuration start))
                   write-facts
                   :if-exists :supersede))

    ;; Maybe display scene
    (when (and gui start-scene)
      (robray::win-set-scene-graph start-scene-graph)
      (robray::win-set-config start))

    ;; Now plan!
    (cond

      ;; Task-Motion Planning
      ((and start-scene task-domain)
       (if-let ((plan (itmp-rec start-scene-graph goal-scene-graph
                                task-domain
                                :q-all-start start
                                :max-steps max-steps)))
         (progn
           ;; Maybe display scene
           (when gui
             (robray::win-display-motion-plan-sequence (tm-plan-motion-plans plan)))
           ;; output plan
           (output-rope (rope (loop for scene in start-scene
                                 collect (rope "# Start Scene: " scene #\Newline))
                              (rope "# Task Domain: " task-domain #\Newline)
                              (loop for scene in goal-scene
                                 collect (rope "# Goal Scene: " scene #\Newline))
                              (object-rope plan))
                        output :if-exists :supersede)
           plan)
         ;; no plan
         (format *error-output* "~&ERROR: no plan found.~&")))

      ;; Task plan only
      ((and task-domain task-facts)
       (if-let ((plan (smt-plan task-domain task-facts :max-steps max-steps)))
         (output-rope (rope (rope "# Task Domain: " task-domain #\Newline)
                            (rope "# Task Facts: "  task-facts #\Newline)
                            (loop for op in plan collect (tm-op-action op nil nil)))
                      output :if-exists :supersede)
         (format *error-output* "~&ERROR: no plan found.~&")))

      ;; Unknowm mode
      (t
       (format *error-output* "~&ERROR: invalid parameters.~&")))))

;; TODO: start configuration

(defun env-list (varname)
  (read-from-string (concatenate 'string "("
                                 (uiop/os:getenv varname)
                                 ")")))

(defun tmp-command ()
  (let* ((scene-files (env-list "TMSMT_SCENE_FILES"))
         (goal-files (env-list "TMSMT_GOAL_FILES"))
         (script-files (env-list "TMSMT_SCRIPT_FILES"))
         (max-steps (if-let ((s (uiop/os:getenv "TMSMT_MAX_STEPS")))
                      (parse-integer s)
                      10))
         (plan-file (uiop/os:getenv "TMSMT_INPUT"))
         (gui (or (uiop/os:getenv "TMSMT_GUI")
                  plan-file)))
    (when gui
      (robray::win-create :title "TMSMT"
                          :stop-on-quit t))
    (cond
      ((uiop/os:getenv "TMSMT_PYTHON_SHELL")
       (clpython:repl))
      (plan-file
       ;; Load and display plan
       (display-tm-plan-file scene-files nil plan-file))
      (t
       ;; Find the plan
       (tmp-driver :start-scene scene-files
                   :goal-scene goal-files
                   :scripts script-files
                   :task-domain (uiop/os:getenv "TMSMT_TASK_DOMAIN")
                   :task-facts (uiop/os:getenv "TMSMT_TASK_FACTS")
                   :max-steps max-steps
                   :gui gui
                   :write-facts (uiop/os:getenv "TMSMT_WRITE_FACTS")
                   :output (uiop/os:getenv "TMSMT_OUTPUT")
                   :verbose (uiop/os:getenv "TMSMT_VERBOSE"))))
    ;; Join the window thread
    (when gui
      (robray::win-join))))

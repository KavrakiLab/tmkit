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
                     start-scene
                     goal-scene
                     pddl
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

  ;; Load scenes
  (let* ((scripts (let ((s (ensure-list scripts)))
                    (map nil #'tmp-script s)
                    s))
         domain-exp
         facts-exp
         (start-scene (ensure-list start-scene))
         (gui (and gui start-scene))
         (goal-scene (ensure-list goal-scene))
         (start-scene-graph (robray::load-scene-files start-scene))
         (goal-scene-graph (robray::load-scene-files goal-scene))
         (output (or output *standard-output*)))
    (finish-output *standard-output*)

    (labels ((header-line (text list)
               (loop for elt in list
                  collect (rope text elt #\Newline)))
             (plan-header ()
               (rope (header-line "# Script" scripts)
                     (loop for p in pddl
                        collect
                          (rope "# Task Domain: "
                                (etypecase p
                                  ((or pathname rope) p)
                                  (t nil))
                                #\Newline))
                     (header-line "# Start Scene" start-scene)
                     (header-line "# Goal Scene" goal-scene))))

      ;; Load PDDL
      (dolist (x (ensure-list pddl))
        (multiple-value-bind (sexp type) (load-pddl-sexp x)
          (ecase type
            (:domain
             (unless (null domain-exp)
               (error "Multiple PDDL domains."))
             (setq domain-exp sexp))
            (:problem
             (setq facts-exp (merge-facts facts-exp sexp))))))

      (print domain-exp)

      ;; Maybe write facts
      (when write-facts
        (format t "~&Write Facts: ~A~%" write-facts)
        (let* ((scene-facts (scene-facts start-scene-graph goal-scene-graph :configuration start))
               (all-facts (merge-facts facts-exp scene-facts))
               (rope (pddl-exp-rope all-facts)))
          (output-rope rope write-facts :if-exists :supersede)))

      ;; Maybe display scene
      (when gui
        (robray::win-set-scene-graph start-scene-graph)
        (robray::win-set-config start))

      ;; Now plan!
      (let ((plan (cond
                    ;; Task-Motion Planning
                    ((and start-scene domain-exp)
                     (itmp-rec start-scene-graph goal-scene-graph
                               domain-exp
                               :facts facts-exp
                               :q-all-start start
                               :max-steps max-steps))
                    ;; Task plan only
                    ((and domain-exp facts-exp)
                     (smt-plan domain-exp facts-exp :max-steps max-steps))
                    ;; Unknown mode
                    (t
                     (format *error-output* "~&ERROR: invalid parameters.~&")))))

        ;; Maybe display plan
        (when (and gui plan)
          (robray::win-display-motion-plan-sequence (tm-plan-motion-plans plan)))

        ;; Output Plan
        (if plan
            (output-rope (rope (plan-header) plan)
                         output :if-exists :supersede)
            (format *error-output* "~&ERROR: no plan found.~&"))))))


;; TODO: start configuration

(defun env-list (varname)
  (read-from-string (concatenate 'string "("
                                 (uiop/os:getenv varname)
                                 ")")))

(defun tmp-command ()
  (let* ((scene-files (env-list "TMSMT_SCENE_FILES"))
         (goal-files (env-list "TMSMT_GOAL_FILES"))
         (pddl-files (env-list "TMSMT_PDDL_FILES"))
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
                   :pddl pddl-files
                   :max-steps max-steps
                   :gui gui
                   :write-facts (uiop/os:getenv "TMSMT_WRITE_FACTS")
                   :output (uiop/os:getenv "TMSMT_OUTPUT")
                   :verbose (uiop/os:getenv "TMSMT_VERBOSE"))))
    ;; Join the window thread
    (when gui
      (robray::win-join))))

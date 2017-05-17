(in-package :tmsmt)


;; FIXME: where does this go?
(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .075)))

(defun tmp-script (pathname)
  (let* ((pathname (pathname pathname))
         (type (string-downcase (pathname-type pathname))))
    (cond
      ;; CLPython Script
      ((string= type "py")
       ;; Workaround mixed-case issue in CL-Python
       ;;(clpython:run pathname)
       (clpython:run (read-file-into-string  pathname)))
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
                     (motion-timeout *motion-timeout*)
                     start-plan
                     start
                     (prefix-cache t)
                     (constraints :state))
  "High-level frontend for the Task-Motion Planner.

START-SCENE: The initial scene graph (or list of scene graphs).
Passed directly to SCENE-GRAPH, so files will be automatically loaded.

GOAL-SCENE: The goal scene graph (or list of scene graphs).
Passed directly to SCENE-GRAPH, so files will be automatically loaded.

PDDL: List of PDDL files to load.  Only a single domain file may be
provided, but multiple (or zero) facts files may be given, all of
which will be merged together.

GUI: Whether to visualize the result via a GUI.

SCRIPTS: Domain semantics scripts to load.

MAX-STEPS: Maximum number of task steps to consider for bounded task
planning.

WRITE-FACTS: If not nil, a file to which the initial facts will be written.

OUTPUT: A stream or filename to output the computed plan.

MOTION-TIMEOUT: The initial motion planning timeout.

START-PLAN: Plan file to give the initial configuration.

START: Initial configurtion

PREFIX-CACHE: Whether to use the prefix cache

CONSTRAINTS: What type of incremental constraints to use to generate alternate plans.
"

  (when verbose
    (format t "~&Start scene files: ~{~A~^, ~}~%" (ensure-list start-scene))
    (format t "~&Goal scene files:  ~{~A~^, ~}~%" (ensure-list goal-scene)))

  ;; Load Scripts

  ;; Load scenes
  (let* ((*motion-timeout* (or motion-timeout *motion-timeout*))
         (scripts (let ((s (ensure-list scripts)))
                    (map nil #'tmp-script s)
                    s))
         domain-exp
         facts-exp
         (start-scene (ensure-list start-scene))
         (gui (and gui start-scene))
         (goal-scene (ensure-list goal-scene))
         (pddl (ensure-list pddl))
         (start-scene-graph (scene-graph start-scene))
         (start (or start
                    (when start-plan
                      (parse-tmplan start-scene-graph start-plan))
                    (robray::make-configuration-map)))
         (goal-scene-graph (scene-graph goal-scene))
         (output (or output *standard-output*)))
    (finish-output *standard-output*)

    (labels ((header-line (text list)
               (loop for elt in list
                  collect (rope text (typecase elt
                                       (rope elt)
                                       (otherwise "N/A"))
                                #\Newline)))
             (plan-header ()
               (rope (header-line "# Semantics: " scripts)
                     (loop for p in pddl
                        collect
                          (rope "# Task Domain: "
                                (etypecase p
                                  ((or pathname rope) p)
                                  (t nil))
                                #\Newline))
                     (header-line "# Start Scene: " start-scene)
                     (header-line "# Goal Scene: " goal-scene))))

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

      ;; Maybe write facts
      (when write-facts
        (format t "~&Write Facts: ~A~%" write-facts)
        (let* ((scene-facts (scene-facts start-scene-graph goal-scene-graph
                                         :configuration start
                                         :operators (parse-operators domain-exp)))
               (all-facts (merge-facts facts-exp scene-facts))
               (rope (pddl-exp-rope all-facts)))
          (output-rope rope write-facts :if-exists :supersede)))

      ;; Maybe display scene
      (when gui
        (robray::win-set-scene-graph start-scene-graph :configuration-map start))

      ;; Now plan!
      (let ((plan (cond
                    ;; Task-Motion Planning
                    ((and start-scene domain-exp)
                     (itmp-rec start-scene-graph goal-scene-graph
                               domain-exp
                               :prefix-cache prefix-cache
                               :constraints constraints
                               :facts facts-exp
                               :q-all-start start
                               :max-steps max-steps))
                    ;; Task plan only
                    ((and domain-exp facts-exp)
                     (map 'list (lambda (a)
                                  (tm-op-action a nil nil))
                          (smt-plan domain-exp facts-exp :max-steps max-steps)))
                    ;; Unknown mode
                    (t
                     (format *error-output* "~&ERROR: invalid parameters~%")
                     (format *error-output* "~&see `tmsmt --help' for usage~%")
                     (quit-system -1)))))

        ;; Maybe display plan
        (when (and gui plan)
          (robray::win-display-motion-plan-sequence (tm-plan-motion-plans plan)))

        ;; Output Plan
        (if plan
            (output-rope (rope (plan-header) plan)
                         output :if-exists :supersede)
            (progn (format *error-output* "~&ERROR: no plan found.~&")
                   (quit-system 1)))))))


(defparameter +copying+
  (read-file-into-string (merge-pathnames "COPYING"
                                          *abs-srcdir*)))

(defun tmp-version (&optional (stream *standard-output*))
  (format stream
          "tmsmt ~A

~A

Written by Neil T. Dantam
"
          +version+
          +copying+
          ))

(defun tmp-version-man (&optional (stream *standard-output*))
  (format stream "~A"
          (ppcre:regex-replace-all (ppcre:create-scanner  "^[ \\*]*" :multi-line-mode t)
                                   (tmp-version nil) "")))

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
    (flet ((helper ()
             (cond
               ((uiop/os:getenv "TMSMT_VERSION")
                (tmp-version))
               ((uiop/os:getenv "TMSMT_VERSION_MAN")
                (tmp-version-man))
               ((uiop/os:getenv "TMSMT_PYTHON_SHELL")
                (clpython:repl))
               (plan-file
                ;; Load and display plan
                (display-tm-plan-file scene-files plan-file))
               (t
                ;; Find the plan
                (tmp-driver :start-scene scene-files
                            :goal-scene goal-files
                            :start-plan (uiop/os:getenv "TMSMT_INITIAL_PLAN")
                            :scripts script-files
                            :pddl pddl-files
                            :max-steps max-steps
                            :gui gui
                            :motion-timeout (if-let ((x (uiop/os:getenv "TMSMT_MOTION_TIMEOUT")))
                                              (max (amino::parse-float x)
                                                   0.1))
                            :write-facts (uiop/os:getenv "TMSMT_WRITE_FACTS")
                            :output (uiop/os:getenv "TMSMT_OUTPUT")
                            :verbose (uiop/os:getenv "TMSMT_VERBOSE"))))))
      (if gui
          (progn
            (robray::win-create :title "TMSMT"
                                :stop-on-quit t)
            (sb-thread:make-thread #'helper)
            (robray::win-run :synchronous t))
          (helper)))))

(require :tmsmt)

(in-package :robray)

(setq *urdf-package-alist*
      `(("baxter_description" . ,(concatenate 'string (namestring (user-homedir-pathname))
                                              "ros_ws/src/baxter_common/baxter_description"))))
(setq *render-host-alist*
      '(("localhost"  ; 4 core (HT), 3.6GHz
         :jobs 8 :threads 1 :nice 0)
        ("dione"      ; 12 core, 1.4GHz
         :jobs 6 :threads 2 :nice 0)
        ("zeus"       ; 16 core, 2.4GHz
         :jobs 8 :threads 2 :nice 1 :povray "/home/ndantam/local/bin/povray")
        ))

(in-package :tmsmt)


(defparameter *scene-directory*
  (concatenate 'string
               (namestring (asdf:system-source-directory :tmsmt))
               "../scene/"))

(moveit-init "/home/ntd/ros_ws/src/baxter_common/baxter_description/urdf/baxter.urdf")

(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *moveit-container* *group*))
(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))

(context-remove-object *plan-context* "block_a")

(context-remove-object *plan-context* "block_b")

(context-remove-all-objects *plan-context*)

(container-set-group *moveit-container* *group*)

(defparameter *object-graph*
  (load-scene-file (concatenate 'string *scene-directory* "scene.robray")))


(defparameter *object-goal*
  (load-scene-file (concatenate 'string *scene-directory* "goal1.robray")))

(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .10)))

(defvar *plan*)

(setq *plan*
      (itmp-rec *object-graph* *object-goal* "/home/ntd/git/tmsmt/pddl/itmp/itmp-blocks-domain.pddl"
                :max-steps 3 :resolution .2))

(render-group-itmp *plan-context* *group*
                     *plan*
                     :render-options  (render-options-default :use-collision nil
                                                              :options (render-options-fast))
                     :scene-graph (robray::scene-graph-merge (plan-context-robot-graph *plan-context*)
                                                             *object-graph*)
                     :frame-name "right_endpoint")

;; (render-group-config *plan-context* *group* (container-plan-endpoint (third *plan*))
;;                      :options (render-options-medium))

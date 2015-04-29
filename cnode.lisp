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
         :jobs 7 :threads 2 :nice 1 :povray "/home/ndantam/local/bin/povray")
        ))
(in-package :tmsmt)


(moveit-init "/home/ntd/ros_ws/src/baxter_common/baxter_description/urdf/baxter.urdf")

(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *moveit-container* *group*))

(format t "~&GROUP: ~A~&LINK: ~A" *group* *link*)


(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))

(format t "~&Vars: ~A~%" (length *q-all-start*))

(moveit-scene-exp-eval '(:clear))

(moveit-scene-file "/home/ntd/git/tmsmt/scene/scene.se")

(context-add-frame-marker *plan-context* "right_w2"
                          :length .25 :width .025)

(context-add-frame-marker *plan-context* "left_w2"
                          :length .25 :width .025)

(container-set-start *moveit-container* *q-all-start*)
(container-set-group *moveit-container* *group*)

;(container-scene-set-color *moveit-cx* "block" 1.0 0.0 0.0 1.0)

;; (container-scene-add-box *moveit-cx* "table" (amino:vec3* 1 2 .01)
;;                          (amino:tf nil (amino:vec3* -.75 0 0)))

;; (container-scene-add-box *moveit-cx* "table2" (amino:vec3* 1 2 .01)
;;                          (amino:tf nil (amino:vec3* .75 0 0)))

;(container-scene-clear *moveit-cx*)

(container-scene-send *moveit-container*)

(defvar *plan*)

(context-add-frame *plan-context* "block-b"
                   (tf* (y-angle (* 1 pi))
                        (vec3* 0 0 .10))
                   "grasp-target")

;; (context-add-frame-marker *plan-context* "grasp-target"
;;                           :length .20 :width .025)

(progn
  (defparameter *e-goal* (context-object-tf *plan-context* "grasp-target"))

  (container-goal-clear *moveit-container*)
  (container-set-ws-goal *moveit-container* *link* *e-goal*))


(progn
  (setq *plan* (container-plan *moveit-container*))
  (container-group-fk *moveit-container* *group* (car (last *plan*))))

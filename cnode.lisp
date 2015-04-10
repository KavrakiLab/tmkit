(require :tmsmt)

(in-package :tmsmt)

(moveit-init)

(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *moveit-container* *group*))

(format t "~&GROUP: ~A~&LINK: ~A" *group* *link*)


(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))

(format t "~&Vars: ~A~%" (length *q-all-start*))

(moveit-scene-exp-eval '(:clear))

(moveit-scene-file "/home/ntd/git/tmsmt/scene/scene.se")

(container-set-start *moveit-container* *q-all-start*)
(container-set-group *moveit-container* *group*)

;(container-scene-set-color *moveit-cx* "block" 1.0 0.0 0.0 1.0)

;; (container-scene-add-box *moveit-cx* "table" (amino:vec3* 1 2 .01)
;;                          (amino:tf nil (amino:vec3* -.75 0 0)))

;; (container-scene-add-box *moveit-cx* "table2" (amino:vec3* 1 2 .01)
;;                          (amino:tf nil (amino:vec3* .75 0 0)))

;(container-scene-clear *moveit-cx*)

(container-scene-send *moveit-container*)

(defparameter *e-goal* (amino:tf (amino:axis-angle (amino:y-angle (* .5 pi)))
                                 (amino:vec3* 0.788372  -0.383374  0.345540)))

(container-set-ws-goal *moveit-container* *link* *e-goal*)

(container-plan *moveit-container*)

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

(defvar *q-grasp*
  (vec 0.117322 0.301443 2.149954 0.907906 -2.171226 1.811191 0.080579))

;; (setq *q-all-start*
;;       (container-merge-group *moveit-container* *group* *q-grasp* *q-all-start*))

(format t "~&Vars: ~A~%" (length *q-all-start*))

(moveit-scene-exp-eval '(:clear))

(moveit-scene-file "/home/ntd/git/tmsmt/scene/scene.se")

(context-add-frame-marker *plan-context* "right_endpoint")

(context-add-frame-marker *plan-context* "left_endpoint")

(container-scene-rm *moveit-container* "block-b")

;(container-scene-rm *moveit-container* "block-a")


(context-add-frame *plan-context* "block-b"
                   (tf* (y-angle (* 1 pi))
                        (vec3* .00 .25 .15))
                   "grasp-pick")

(context-add-frame *plan-context* "grasp-pick"
                   (tf* nil
                        (vec3* .00 -.05 .00))
                   "grasp-place")

(context-add-frame-marker *plan-context* "grasp-pick")
(context-add-frame-marker *plan-context* "grasp-place")

(defparameter *e-pick* (context-object-tf *plan-context* "grasp-pick"))
(defparameter *e-place* (context-object-tf *plan-context* "grasp-place"))

(container-set-group *moveit-container* *group*)

;; PICK ;;

;; (defvar *plan*)


;; (container-set-start *moveit-container* *q-all-start*)


;; (progn
;;   (container-goal-clear *moveit-container*)
;;   (container-set-ws-goal *moveit-container* *link* *e-pick*))


;; (container-scene-send *moveit-container*)

;; (progn
;;   (setq *plan* (container-plan *moveit-container*)))

;; PLACE ;;
(defparameter *q-grasp* (vec 0.8921887533975497d0 -0.7577635932222542d0 -0.04866383109478782d0
                             0.9953607016244341d0 0.04254853481160224d0 1.3359037004119487d0
                             0.0461604074055537d0))

(container-set-start *moveit-container*
                     (container-merge-group *moveit-container* *group*
                                            *q-grasp*
                                            *q-all-start*))

(context-attach-object *plan-context* *group* *q-grasp* "right_endpoint" *link* "block-a")

(container-set-start *moveit-container*
                     (container-merge-group *moveit-container* *group*
                                            *q-grasp*
                                            *q-all-start*))


(container-scene-send *moveit-container*)

(progn
  (container-goal-clear *moveit-container*)
  (container-set-ws-goal *moveit-container* *link* *e-place*))



(container-plan *moveit-container*)

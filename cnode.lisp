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

(moveit-scene-exp-eval '(:rm "block-a"))
(moveit-scene-exp-eval '(:rm "block-b"))
(moveit-scene-exp-eval '(:clear))

(moveit-scene-file "/home/ntd/git/tmsmt/scene/scene.se")

(context-add-frame-marker *plan-context* "right_endpoint")
(context-add-frame-marker *plan-context* "left_endpoint")

(moveit-scene-exp-eval '(:rm "block-b"))

(defparameter *scene-graph* (robray::scene-graph-merge (plan-context-robot-graph *plan-context*)
                                                       (plan-context-object-graph *plan-context*)))


(context-draw *plan-context* "block-a" "grasp-pick"
              :tf (tf* (y-angle (* 1 pi))
                       (vec3* .00 .00 .10))
              :actual-parent nil)

(context-draw *plan-context* "grasp-pick" "grasp-place"
              :tf (tf* nil
                       (vec3* .40 -.65 .00))
              :actual-parent nil)

(context-add-frame-marker *plan-context* "grasp-pick")
(context-add-frame-marker *plan-context* "grasp-place")

(defparameter *e-pick* (context-object-tf *plan-context* "grasp-pick"))
(defparameter *e-place* (context-object-tf *plan-context* "grasp-place"))

(container-set-group *moveit-container* *group*)

;; PICK ;;



(container-set-start *moveit-container* *q-all-start*)


(progn
  (container-goal-clear *moveit-container*)
  (container-set-ws-goal *moveit-container* *link* *e-pick*))


(container-scene-send *moveit-container*)

(defvar *plan-pick*)
(setq *plan-pick* (container-plan *moveit-container*))

;; PLACE ;;
(defparameter *q-grasp* (container-plan-endpoint *plan-pick*))

(context-attach-object *plan-context* *group* *q-grasp* "right_endpoint" *link* "block-a")

(container-set-start *moveit-container*
                     (container-merge-group *moveit-container* *group*
                                            *q-grasp*
                                            *q-all-start*))


(container-scene-send *moveit-container*)

(progn
  (container-goal-clear *moveit-container*)
  (container-set-ws-goal *moveit-container* *link* *e-place*))


(defvar *plan-place*)
(setq *plan-place* (container-plan *moveit-container*))


;; RETURN ;;
(defparameter *q-place* (container-plan-endpoint *plan-place*))

(context-dettach-object *plan-context* *group* *q-place* "block-a")

(progn
  (container-goal-clear *moveit-container*)
  (container-set-js-goal *moveit-container* *group* *q-all-start*))

(container-scene-send *moveit-container*)

(container-set-start *moveit-container*
                     (container-merge-group *moveit-container* *group*
                                            *q-place*
                                            *q-all-start*))

(defvar *plan-return*)
(setq *plan-return* (container-plan *moveit-container*))

(time (render-group-itmp *plan-context* *group*
                   (list *plan-pick*
                         '(:pick "block-a")
                         *plan-place*
                         '(:place "block-a")
                         *plan-return*
                         )
                   :render-options (merge-render-options (render-options :use-collision t)
                                                         (render-options-full-hd))
                   :scene-graph *scene-graph*
                   :frame-name "right_endpoint"))

;(render-group-config *plan-context* *group* (container-plan-endpoint *plan-place*))

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
                        (vec3* .15 -.25 .00))
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

(defvar *attach-tf*)

;; (setq *attach-tf*
;;       (robray::scene-graph-tf-absolute (robray::scene-graph-merge  (plan-context-robot-graph *plan-context*)
;;                                                                    (plan-context-object-graph *plan-context*))
;;                                        "grasp-pick"
;;                                        :configuration-map
;;                                        (container-group-configuration-map *moveit-container* *group*
;;                                                                           (container-plan-endpoint *plan*))
;;                                        :default-configuration 0d0))


(defun attach-object (context group q-group frame link object)
  ;; moveit seems to attach objects at current state that defaults zero
  ;; Objects are NOT attached relative to the start state of the plan
  ;;       Find global_TF_obj
  ;;       Find ee_TF_obj
  ;;       Find object absolute TF as when EE: global_TF_ee(obj)(q=0) * ee_TF_obj
  (let* ((container (plan-context-moveit-container context))
         (g_TF_obj (context-object-tf context object))
         (g_TF_ee (robray::scene-graph-tf-absolute (plan-context-robot-graph *plan-context*)
                                                   frame
                                                   :configuration-map
                                                   (container-group-configuration-map container group q-group)
                                                   :default-configuration 0d0))
         (ee_tf_obj (g* (inverse g_TF_ee) g_TF_obj))
         (g_TF_ee_0 (robray::scene-graph-tf-absolute (plan-context-robot-graph *plan-context*)
                                                     frame
                                                     :configuration-map
                                                     (make-tree-map #'string-compare)
                                                     :default-configuration 0d0)))

    (container-scene-rm container object)
    (container-scene-attach-box container link object (vec .1 .1 .1)
                                (g* g_tf_ee_0 ee_tf_obj))))


(context-add-frame *plan-context* "right_endpoint"
                   (tf* nil (vec3* 0 0 .02))
                   "object-attach")

(setq *attach-tf*
      (robray::scene-graph-tf-absolute (robray::scene-graph-merge  (plan-context-robot-graph *plan-context*)
                                                                   (plan-context-object-graph *plan-context*))
                                       "object-attach"
                                       :configuration-map
                                       (container-group-configuration-map *moveit-container* *group*
                                                                          (loop for i below 7 collect 0d0))
                                       :default-configuration 0d0))


;(setq *attach-tf* (tf* nil '(0 0 0)))
;(setq *attach-tf* (context-object-tf *plan-context* "block-a"))

(container-set-start *moveit-container*
                     (container-merge-group *moveit-container* *group*
                                            *q-grasp*
                                            *q-all-start*))

(container-scene-rm *moveit-container* "block-a")

(container-scene-rm *moveit-container* "block-a-1")

;(container-scene-attach-box *moveit-container* *link* "block-a-1" (vec .01 .01 .01)  *attach-tf*)
(attach-object *plan-context* *group* *q-grasp* "right_endpoint" *link* "block-a")

(container-set-start *moveit-container*
                     (container-merge-group *moveit-container* *group*
                                            *q-grasp*
                                            *q-all-start*))


(container-scene-send *moveit-container*)

(progn
  (container-goal-clear *moveit-container*)
  (container-set-ws-goal *moveit-container* *link* *e-place*))



(container-plan *moveit-container*)

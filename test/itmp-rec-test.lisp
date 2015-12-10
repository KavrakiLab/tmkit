(require :tmsmt)
(in-package :tmsmt)

(sb-posix:setenv "ROS_PACKAGE_PATH" "/opt/ros/indigo/share/" 1)

(defparameter  *robot-graph* (load-scene-file "package://baxter_description/urdf/baxter.urdf"))



(defparameter *baxter-source-directory*
  (concatenate 'string
               (namestring (asdf:system-source-directory :amino))
               "../demo/baxter-raytrace/"))
(uiop/stream:copy-file (robray::output-file "baxter.inc" *baxter-source-directory*)
                       (robray::output-file "baxter.inc" robray::*robray-tmp-directory*))

(defparameter *scene-directory*
  (rope *tmsmt-root* "/scene/"))

;(defparameter *group* "right_arm")
;(defparameter *link* (container-group-endlink *moveit-container* *group*))
;(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))

(defparameter *object-graph*
  (load-scene-file (rope *scene-directory* "scene.robray")))

(defparameter *object-goal*
  (load-scene-file (rope *scene-directory* "goal1.robray")))

(defparameter *all-graph*
  (scene-graph *robot-graph* *object-graph*))

(defparameter *ssg* (robray::scene-graph-chain *all-graph* nil "right_endpoint"))

(robray::win-set-scene-graph *all-graph*)

(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .25)))

(defvar *plan*)

(defparameter *start* (robray::alist-configuration-map `(("right_s0" . ,(/ pi 5)))))


(robray::win-set-config (robray::scene-graph-ik *all-graph* :frame "right_endpoint"
                                                :tf (g* (scene-graph-tf-absolute *all-graph* "block_a")
                                                        *tf-grasp-rel*)))

(time
 (progn
   (setq *plan*
         (itmp-rec *all-graph* *object-goal*
                   (rope *tmsmt-root* "pddl/itmp/itmp-blocks-linear.pddl")
                   :frame "right_endpoint"
                   :encoding :linear
                   :max-steps 3 :resolution .2))
   nil))

;; (render-group-itmp *plan-context* *group*
;;                      *plan*
;;                      :render-options  (render-options-default :use-collision nil
;;                                                               :options (render-options-fast))
;;                      :scene-graph (scene-graph (plan-context-robot-graph *plan-context*)
;;                                                *object-graph*)
;;                      :frame-name "right_endpoint")


;; (context-apply-scene *plan-context* *object-graph*)
;; (render-group-config *plan-context* *group*
;;                      ;(container-plan-endpoint (third *plan*))
;;                      *q-all-start*
;;                      :options (render-options-medium))

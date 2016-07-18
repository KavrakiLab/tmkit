(require :tmsmt)
(in-package :tmsmt)

;;; Load Robot ;;;
(sb-posix:setenv "ROS_PACKAGE_PATH" "/opt/ros/indigo/share/" 1)
(defparameter *robot-graph* (load-scene-file "package://baxter_description/urdf/baxter.urdf"))


;;; Allow Collisions ;;;
(defparameter *allowed-collision*
  '(("right_w0_fixed" . "right_wrist-collision")))

(defparameter *config-names*
  '("right_s0" "right_s1"
    "right_e0" "right_e1"
    "right_w0" "right_w1" "right_w2"))
(defun joint-config (values)
  (robray::configuration-map-pairs *config-names* values))

(setq *robot-graph*
      (fold #'robray::scene-graph-allow-configuration *robot-graph*
            (list nil
                  (joint-config '(0.375973 -1.44985 0.555649
                                  2.54396 -0.133194 0.498291 0.260089)))))

(setq *robot-graph* (scene-graph-allow-collisions *robot-graph*
                                                  *allowed-collision*))


;; Povray Setup ;;
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

;;; Object Setup ;;;
(defparameter *object-graph*
  (load-scene-file (rope *scene-directory* "scene.robray")))

(defparameter *object-goal*
  (load-scene-file (rope *scene-directory* "goal1.robray")))

(defparameter *all-graph*
  (scene-graph *robot-graph* *object-graph*))

(robray::win-set-scene-graph *object-graph*)

(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .075)))

(defvar *plan*)

(defparameter *start* (robray::alist-configuration-map `(("right_s0" . ,(/ pi 5)))))


(robray::win-set-config  (robray::make-configuration-map))



;; (robray::scene-graph-ik *all-graph* :frame "right_endpoint"
;;                         :tf (tf* (quaternion* 0.0d0 1.0d0 0.0d0 0)
;;                                  (vec3* .8 -.25 .3051)))

;; (let* ((frame "right_endpoint")
;;        (tf (tf (vec 0.0d0 1.0d0 0.0d0 6.123233995736766d-17 0.8d0 -0.25d0 0.2051d0)))
;;        (ik (robray::scene-graph-ik *all-graph* :frame frame :tf tf))
;;        (g-tf-e (scene-graph-tf-absolute *all-graph* frame :configuration-map ik))
;;        (g-tf-w2 (scene-graph-tf-absolute *all-graph* "right_w2" :configuration-map ik))
;;        )
;;   (robray::win-set-config ik)
;;   (print (g* (tf-inverse g-tf-e) tf))
;;   (print (g* (tf-inverse g-tf-e) g-tf-w2 ))
;;   ik)



;; (defparameter *mp*
;;   (motion-plan *ssg* *start*
;;                ;;:jointspace-goal *goal*
;;                :workspace-goal (tf* (quaternion* 0.0d0 1.0d0 0.0d0 0)
;;                                     (vec3* .8 -.25 .3051))))

(time
 (progn
   (setq *plan*
         (itmp-rec *all-graph* *object-goal*
                   (rope *tmsmt-root* "pddl/itmp/itmp-blocks-linear.pddl")
                   :q-all-start *start*
                   :frame "right_endpoint"
                   :encoding :linear
                   :max-steps 3 :resolution .1))
   nil))


(when *plan*
  (robray::win-display-motion-plan-sequence (tm-plan-motion-plans *plan*)))

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

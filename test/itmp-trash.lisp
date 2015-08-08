(require :tmsmt)
(in-package :tmsmt)

(defparameter *baxter-source-directory*
  (concatenate 'string
               (namestring (asdf:system-source-directory :robray))
               "/demo/baxter/"))
(uiop/stream:copy-file (robray::output-file "baxter.inc" *baxter-source-directory*)
                       (robray::output-file "baxter.inc" robray::*robray-tmp-directory*))

(defparameter *scene-directory*
  (rope *tmsmt-root* "/scene/lab/"))


(defparameter *robot*
  (load-scene-file (robray::urdf-resolve-file "package://baxter_description/urdf/baxter.urdf")
                   :reload-meshes nil))

(defparameter *object-graph*
  (load-scene-file (rope *scene-directory* "labscene_place.robray")))


(defparameter *object-goal*
  (load-scene-file (rope *scene-directory* "labscene_goal.robray")))

(defparameter *tf-grasp-top* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .10)))

(defparameter *tf-grasp-back* (tf* (y-angle (* .5 pi)) (vec3* -.10 .00 .025)))

(defparameter *tf-grasp-rel* *tf-grasp-back*)

(defparameter *draw-scene*
  (scene-graph *robot* *object-graph*
               (scene-frame-fixed "block_a" "block_a_grasp" :tf *tf-grasp-back*)
               ;(scene-frame-fixed "block_a" "block_a_grasp" :tf *tf-grasp-top*)
               ;; (robray::item-frame-marker "block_a_grasp" (robray::draw-subframe "block_a" "marker")
               ;;                            :length .15
               ;;                            :width .015
               ;;                            :options (robray::draw-options :no-shadow t :alpha .5
               ;;                                                           :visual t :collision nil))

               (robray::item-frame-marker "right_endpoint" (robray::draw-subframe "right_endpoint" "marker")
                                          :length .15
                                          :width .015
                                          :options (robray::draw-options :no-shadow t :alpha .5
                                                                         :visual t :collision nil))
               ))

(robray::scene-graph-pov-frame
 *draw-scene*
 :configuration-map
 (alist-tree-map `(("right_s0" . ,(* .25 pi))
                   ("right_s1" . ,(* -0.25 pi))
                   ("right_e0" . ,(* 0.0 pi))
                   ("right_e1" . ,(* 0.25 pi))
                   ("right_w0" . ,(* 0.0 pi))
                   ("right_w1" . ,(* 0.5 pi))
                   ("right_w2" . ,(* 0.0 pi)))
                 #'string-compare)
 :include "baxter.inc"
 :render t
 :options (render-options-default :use-collision nil
                                  :options (render-options-medium))
 :output "robray.pov")







(moveit-init (robray::urdf-resolve-file "package://baxter_description/urdf/baxter.urdf"))
(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *moveit-container* *group*))
(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))
(container-set-group *moveit-container* *group*)



(time
 (progn
   (setq *plan*
         (itmp-rec *object-graph* *object-goal*
                   (rope *tmsmt-root* "pddl/itmp/itmp-blocks-linear.pddl")
                   :encoding :linear
                   :max-steps 1 :resolution .2d0))
   nil))

(render-group-itmp *plan-context* *group*
                     *plan*
                     :render-options  (render-options-default :use-collision nil
                                                              :options (render-options-fast))
                     :scene-graph *draw-scene*
                     :frame-name "right_endpoint")

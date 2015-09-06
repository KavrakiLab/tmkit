(require :tmsmt)
(in-package :tmsmt)

(defparameter *table-dim* (vec3* .3 .3 .01))
(defparameter *box-dim* .040)
(defparameter *resolution* .07)
(defparameter *z* (/ (+ .02 (vec-z *table-dim*) *box-dim*)
                     2))
(defparameter *box* (scene-box (vec3* *box-dim* *box-dim* *box-dim*)))
(defparameter *box-marker* (scene-box (g* 1.01 (vec3* *box-dim* *box-dim* *box-dim*))))
(defparameter *geometry* (robray::scene-geometry *box*
                                                 (draw-options-default :color '(1 0 0)
                                                                       :type "moveable"
                                                                       :visual t
                                                                       :collision t)))


(setq *scene-directory*
      (fad:merge-pathnames-as-directory *tmsmt-root*
                                        (make-pathname :directory '(:relative "scene"))))

;(defparameter *robot* (robray::urdf-resolve-file "package://baxter_description/urdf/baxter.urdf"))
(defparameter *robot* "/home/ntd/git/mochi/robot/baxter/baxter-gripper.urdf")
;(defparameter *robot* "/home/ntd/git/mochi/robot/baxter/baxter_urdf_with_grippers.xml")
(defparameter *sg-table*
  (scene-graph (scene-frame-fixed nil "table-base"
                                  :tf (tf* (z-angle (* -45 (/ pi 180)))
                                           (vec3* .1 -.3 0)))
               (scene-frame-fixed "table-base" "front_table"
                                  :tf (tf* nil ;(z-angle (* -30 (/ pi 180)))
                                           '(.6 0 0))
                                  :geometry (robray::scene-geometry (scene-box *table-dim*)
                                                                    (draw-options-default :color '(.5 .5 .5)
                                                                                          :type "stackable"
                                                                                          :visual t
                                                                                           :collision t)))))




(defparameter *obj* (loop for i to 7 collect i))
(defparameter *goal-obj* (append (cdr *obj*)
                                 (list (car *obj*))))

(defparameter *sg-block*  (genscene-repeat *sg-table* "block"
                                           *box*
                                           :objects *obj*
                                           :max-locations (1+ (length *obj*))
                                           :resolution *resolution*
                                           :randomize nil
                                           :z *z*
                                           :options (draw-options-default :color '(1 0 0)
                                                                          :specular .5
                                                                          :type "moveable"
                                                                          :visual t
                                                                          :collision t)))
(defparameter *sg-goal*  (genscene-repeat *sg-table* "block"
                                          *box*
                                          :objects *goal-obj*
                                          :randomize nil
                                          :max-locations (1+ (length *obj*))
                                          :resolution *resolution*
                                          :z *z*
                                          :options (draw-options-default :color '(1 0 0)
                                                                         :specular .5
                                                                         :type "moveable"
                                                                         :visual t
                                                                         :collision t)))



(defparameter *sg-marker*
  (apply #'scene-graph
         (loop for i in *obj*
            for c in '((1 0 0)
                       (0 1 0)
                       (0 0 1)
                       (1 1 0)
                       (1 0 1)
                       (0 1 1)
                       (0 .5 1)
                       (.5 0 1))
              collect
              (scene-frame-fixed (format nil "block-~D" i)
                                 (format nil "block-~D-marker" i)
                                 :tf (tf* nil nil)
                                 :geometry (robray::scene-geometry *box-marker*
                                                                   (draw-options-default :color c
                                                                                         :visual t
                                                                                         :collision nil)))
   )))


(uiop/stream:copy-file (robray::output-file "baxter.inc" (rope *tmsmt-root* "/test/"))
                       (robray::output-file "baxter.inc" robray::*robray-tmp-directory*))



(robray::scene-graph-pov-frame
 (scene-graph *robot* *sg-goal* *sg-table* *sg-marker*)
 :configuration-map
 (alist-tree-map `(("right_s0" . ,(* .05 pi))
                   ("right_s1" . ,(* -0.25 pi))
                   ("right_e0" . ,(* 0.0 pi))
                   ("right_e1" . ,(* 0.25 pi))
                   ("right_w0" . ,(* 0.0 pi))
                   ("right_w1" . ,(* 0.5 pi))
                   ("right_w2" . ,(* 0.0 pi))
                   ("left_s0" . ,(* -.15 pi))
                   ("left_s1" . ,(* -0.25 pi))
                   ("left_e0" . ,(* 0.0 pi))
                   ("left_e1" . ,(* 0.25 pi))
                   ("left_w0" . ,(* 0.0 pi))
                   ("left_w1" . ,(* 0.5 pi))
                   ("left_w2" . ,(* 0.0 pi))
                   )
                 #'string-compare)
 :include "baxter.inc"
 :render t
 :options (render-options-default :use-collision nil
                                  :options (render-options-full-hd))
 :output "robray.pov")

(moveit-init (robray::urdf-resolve-file "package://baxter_description/urdf/baxter.urdf"))

(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *moveit-container* *group*))
(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))

(context-remove-object *plan-context* "block_a")

(context-remove-object *plan-context* "block_b")

(context-remove-all-objects *plan-context*)

(container-set-group *moveit-container* *group*)


(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .10)))




(defvar *plan*)


(loop for n from 0 to -1
   for i = 0
   for obj = (loop for i below n collect i)
   for goal-obj = (append (cdr obj) (list (car obj)))
   for block = (genscene-repeat *sg-table* "block"
                                *box*
                                :objects obj
                                :max-locations n
                                :resolution *resolution*
                                :randomize nil
                                :z *z*
                                :options (draw-options-default :color '(1 0 0)
                                                               :specular .5
                                                               :type "moveable"
                                                               :visual t
                                                               :collision t))
   for goal = (genscene-repeat *sg-table* "block"
                               *box*
                               :objects goal-obj
                               :randomize nil
                               :max-locations n
                               :resolution *resolution*
                               :z *z*
                               :options (draw-options-default :color '(1 0 0)
                                                              :specular .5
                                                              :type "moveable"
                                                              :visual t
                                                              :collision t))
   do
     (loop
        while (< i 5)
        do
          (incf i)
        ;; plan
          ;; (setq *plan*
          ;;       (itmp-rec (scene-graph *sg-table* block) goal
          ;;                 (rope *tmsmt-root* "pddl/itmp/itmp-blocks-linear.pddl")
          ;;                 :encoding :linear
          ;;                 :action-encoding :enum
          ;;                 :max-locations (+ n 1)
          ;;                 :max-steps (+ n 2) :resolution *resolution*))
          (setq *plan*
                (itmp-syn (scene-graph *sg-table* block) goal
                           :encoding :linear
                           :max-locations (+ n 1)
                           :resolution *resolution*))

        ;;(print *plan*)
        ;; write output
          (output-timing (1+ n) "syn-deep")))


;; (time
;;  (progn
;;    (setq *plan*
;;          (itmp-rec (scene-graph *sg-block* *sg-table*)
;;                    *sg-goal*
;;                    (rope *tmsmt-root* "pddl/itmp/itmp-blocks-linear.pddl")
;;                    :encoding :linear
;;                    :action-encoding :enum
;;                    :max-steps 12 :resolution *resolution*))
;;    nil))


;; (time
;;  (progn
;;    (setq *plan*
;;          (itmp-syn (scene-graph *sg-table* *sg-block*) *sg-goal*
;;                    :encoding :linear
;;                    :max-locations (1+ (length *obj*))
;;                    :resolution *resolution*))
;;    nil))

;; (render-group-itmp *plan-context* *group*
;;                    *plan*
;;                    :render-options  (render-options-default :use-collision nil
;;                                                             :options (render-options-fast))
;;                    :scene-graph (scene-graph ;(plan-context-robot-graph *plan-context*)
;;                                              *robot* *sg-start* *sg-marker*)
;;                    :frame-name "right_endpoint")


;; (context-apply-scene *plan-context* *object-graph*)
;; (render-group-config *plan-context* *group*
;;                      ;(container-plan-endpoint (third *plan*))
;;                      *q-all-start*
;;                      :options (render-options-medium))

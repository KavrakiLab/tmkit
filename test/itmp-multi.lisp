(require :tmsmt)
(in-package :tmsmt)

(defparameter *table-dim* (vec3* .4 .4 .01))
(defparameter *box-dim* .050)
(defparameter *resolution* .08)
(defparameter *z* (/ (+ .02 (vec-z *table-dim*) *box-dim*)
                     2))
(defparameter *box* (scene-box (vec3* *box-dim* *box-dim* *box-dim*)))
(defparameter *geometry* (robray::scene-geometry *box*
                                                 (draw-options-default :color '(1 0 0)
                                                                       :type "moveable"
                                                                       :visual t
                                                                       :collision t)))


(setq *scene-directory*
      (fad:merge-pathnames-as-directory *tmsmt-root*
                                        (make-pathname :directory '(:relative "scene"))))

(defparameter *robot* (robray::urdf-resolve-file "package://baxter_description/urdf/baxter.urdf"))

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



;; (defparameter *sg-block*  (genscene-repeat *sg-table* "block"
;;                                            *box*
;;                                            :count 30
;;                                            :max-locations 31
;;                                            :resolution *resolution*
;;                                            :z *z*
;;                                            :options (draw-options-default :color '(1 0 0)
;;                                                                           :specular .5
;;                                                                           :type "moveable"
;;                                                                           :visual t
;;                                                                           :collision t)))




(defparameter *sg-goal*
  (scene-frame-fixed "front_table" "block-0"
                     :tf (tf* nil
                              (vec3* 0 0 *z*))
                     :geometry *geometry*))

(defparameter *sg-marker*
  (scene-graph
   (scene-frame-fixed "front_table" "table-marker"
                      :tf (tf* (x-angle 0)
                               (list 0 0 (+ .15 (/ *box-dim* 1))))
                      :geometry (robray::scene-geometry (scene-sphere .1)
                                                        (draw-options-default :color '(0 1 0)
                                                                              ;:specular .3
                                                                              :visual nil
                                                                              :collision nil)))
   (robray::item-arrow-axis "table-marker" "table-arrow"
                            :axis  (vec3* 0 0 -1)
                            :length .1
                            :width .025
                            :end-arrow t
                            :options (draw-options-default :color '(0 1 0)
                                                           :alpha .5
                                                           :no-shadow t
                                                           :visual t
                                                           :collision nil))

   (scene-frame-fixed "block-0" "block-0-marker"
                      :tf (tf* (x-angle 0)
                               '(0 0 .15))
                      :geometry (robray::scene-geometry (scene-sphere .1)
                                                        (draw-options-default :color '(0 0 1)
                                                                              :visual nil
                                                                              :collision nil)))
   (robray::item-arrow-axis "block-0-marker" "block-0-arrow"
                            :axis  (vec3* 0 0 -1)
                            :length .1
                            :width .025
                            :end-arrow t
                            :options (draw-options-default :color '(0 0 1)
                                                           :alpha .5
                                                           :no-shadow t
                                                           :visual t
                                                           :collision nil))
   ))

(uiop/stream:copy-file (robray::output-file "baxter.inc" (rope *tmsmt-root* "/test/"))
                       (robray::output-file "baxter.inc" robray::*robray-tmp-directory*))


;; (let ((frame (robray::scene-graph-lookup *sg-block* "block-0"))
;;       (blocks (scene-graph-remove-frame *sg-block* "block-0")))

;;   (robray::scene-graph-pov-frame
;;    (scene-graph *robot* *sg-table* *sg-marker* blocks
;;                 (scene-frame-fixed "front_table" "block-0"
;;                                    :geometry (robray::scene-geometry *box*
;;                                                                      (draw-options-default :color '(0 0 1)
;;                                                                                            :specular .3
;;                                                                                            :type "moveable"
;;                                                                                            :visual t
;;                                                                                            :collision t))
;;                                    :tf (robray::scene-frame-tf frame)))
;;    :configuration-map
;;    (alist-tree-map `(;("right_s0" . ,(* .25 pi))
;;                                         ;("right_s1" . ,(* -0.25 pi))
;;                                         ;("right_e0" . ,(* 0.0 pi))
;;                                         ;("right_e1" . ,(* 0.25 pi))
;;                                         ;("right_w0" . ,(* 0.0 pi))
;;                                         ;("right_w1" . ,(* 0.5 pi))
;;                                         ;("right_w2" . ,(* 0.0 pi))
;;                      )
;;                    #'string-compare)
;;    :include "baxter.inc"
;;    :render t
;;    :options (render-options-default :use-collision nil
;;                                                  :options (render-options-full-hd))
;;  :output "robray.pov")
  ;; )

(moveit-init (robray::urdf-resolve-file "package://baxter_description/urdf/baxter.urdf"))

(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *moveit-container* *group*))
(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))

(context-remove-object *plan-context* "block_a")

(context-remove-object *plan-context* "block_b")

(context-remove-all-objects *plan-context*)
(container-set-group *moveit-container* *group*)

;(tms-container-set-planner *moveit-container* "KPIECEkConfigDefault")
;; (tms-container-set-planner *moveit-container*
;;                            ;"SBLkConfigDefault"
;;                            ;"LBKPIECEkConfigDefault"
;;                            ;"RRTkConfigDefault"
;;                            "RRTConnectkConfigDefault"
;;                            ;"LazyRRTkConfigDefault"
;;                            ;"ESTkConfigDefault"
;;                            ;"KPIECEkConfigDefault"
;;                            ;"RRTStarkConfigDefault"
;;                            ;"BKPIECEkConfigDefault"
;;                            )

(tms-container-set-volume *moveit-container*
                          (vec3* -2 -2 -2)
                          (vec3* 2 2 2)
                          )

(defparameter *tf-grasp-top* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 (+ .04 (/ *box-dim* 2)))))
(defparameter *tf-grasp-back* (tf* (y-angle (* .5 pi)) (vec3* (- (+ .04 (/ *box-dim* 2)))  .00 .070)))
(defparameter *tf-grasp-rel* *tf-grasp-back*)

(defvar *plan*)

(loop for n-obj from 6 to 6
   for i = 0
   do
     (loop
        while (< i 5)
        ;; create domain
        for blocks = (genscene-repeat *sg-table* "block"
                                      *box*
                                      :count n-obj
                                      :max-locations (1+ n-obj)
                                      :resolution *resolution*
                                      :z *z*
                                      :options (draw-options-default :color '(1 0 0)
                                                                     :type "moveable"
                                                                     :visual t
                                                                     :collision t))
        for v = (tf-translation (robray::scene-frame-tf (robray::scene-graph-lookup blocks "block-0")))
        unless (and (zerop (vec-x v))
                    (zerop (vec-y v)))
        do
          (progn
            (incf i)
            ;; plan
            (print 'informed-idtmp)
            (itmp-rec (scene-graph *sg-table* blocks) *sg-goal*
                      (rope *tmsmt-root* "pddl/itmp/itmp-blocks-linear.pddl")
                      :naive nil
                      :encoding :linear
                      :action-encoding :enum
                      :max-steps n-obj :resolution *resolution*)
            (output-timing n-obj "idtmp-side")

            ;; (print 'naive-idtmp)
            (itmp-rec (scene-graph *sg-table* blocks) *sg-goal*
                      (rope *tmsmt-root* "pddl/itmp/itmp-blocks-linear.pddl")
                      :naive t
                      :encoding :linear
                      :action-encoding :enum
                      :max-steps n-obj :resolution *resolution*)
            (output-timing n-obj "n-idtmp-side")
          )))

;; (render-group-itmp *plan-context* *group*
;;                    *plan*
;;                    :render-options  (render-options-default :use-collision nil
;;                                                             :options (render-options-fast))
;;                    :scene-graph (scene-graph ;(plan-context-robot-graph *plan-context*)
;;                                              *robot* *sg-block* *sg-table* *sg-marker*)
;;                    :frame-name "right_endpoint")


;; (context-apply-scene *plan-context* *object-graph*)
;; (render-group-config *plan-context* *group*
;;                      ;(container-plan-endpoint (third *plan*))
;;                      *q-all-start*
;;                      :options (render-options-medium))

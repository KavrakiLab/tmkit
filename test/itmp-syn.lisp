(require :tmsmt)
(in-package :tmsmt)

(defparameter *table-dim* (vec3* .4 .4 .01))
(defparameter *box-dim* .04)
(defparameter *resolution* .05)
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


;; (defparameter *sg-block*  (genscene-repeat-table "front_table" "block"
;;                                                  *box*
;;                                                  3
;;                                                  (- (vec-x *table-dim*) *resolution*)
;;                                                  (- (vec-y *table-dim*) *resolution*)
;;                                                  :resolution *resolution*
;;                                                  :z *z*
;;                                                  :options (draw-options-default :color '(1 0 0)
;;                                                                                 :type "moveable"
;;                                                                                 :visual t
;;                                                                                 :collision t)))

;; (defparameter *sg-block*
;;   (scene-frame-fixed "front_table" "block-0"
;;                      :tf (tf* nil
;;                               (vec3* 0 .2 *z*))
;;                      :geometry *geometry*))


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

(defparameter *sg-goal*
  (scene-frame-fixed "front_table" "block-0"
                     :tf (tf* nil
                              (vec3* 0 0 *z*))
                     :geometry *geometry*))

(defparameter *sg-marker*
  (scene-graph
   (scene-frame-fixed "block-0" "block-0-marker"
                      :tf (tf* (x-angle 0)
                               '(0 0 .15))
                      :geometry (robray::scene-geometry (scene-sphere .1)
                                                        (draw-options-default :color '(0 1 0)
                                                                              :visual nil
                                                                              :collision nil)))
   (robray::item-arrow-axis "block-0-marker" "block-0-arrow"
                            :axis  (vec3* 0 0 -1)
                            :length .1
                            :width .025
                            :end-arrow t
                            :options (draw-options-default :color '(0 1 0)
                                                           :alpha .5
                                                           :no-shadow t
                                                           :visual t
                                                           :collision nil))))

(uiop/stream:copy-file (robray::output-file "baxter.inc" (rope *tmsmt-root* "/test/"))
                       (robray::output-file "baxter.inc" robray::*robray-tmp-directory*))



;; (robray::scene-graph-pov-frame
;;  (scene-graph *robot* *sg-table* *sg-block* *sg-marker*)
;;  :configuration-map
;;  (alist-tree-map `(;("right_s0" . ,(* .25 pi))
;;                                         ;("right_s1" . ,(* -0.25 pi))
;;                                         ;("right_e0" . ,(* 0.0 pi))
;;                                         ;("right_e1" . ,(* 0.25 pi))
;;                                         ;("right_w0" . ,(* 0.0 pi))
;;                                         ;("right_w1" . ,(* 0.5 pi))
;;                                         ;("right_w2" . ,(* 0.0 pi))
;;                    )
;;                  #'string-compare)
;;  :include "baxter.inc"
;;  :render t
;;  :options (render-options-default :use-collision nil
;;                                   :options (render-options-medium))
;;  :output "robray.pov")

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

;; (tms-container-set-volume *moveit-container*
;;                           (vec3* -2 -2 -2)
;;                           (vec3* 2 2 2)
;;                           )



(defparameter *tf-grasp-top* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .10)))
(defparameter *tf-grasp-back* (tf* (y-angle (* .5 pi)) (vec3* -.10 .00 .035)))
(defparameter *tf-grasp-rel* *tf-grasp-top*)

;; (defparameter *syn-data*
;;   (syn-data (scene-graph *sg-block* *sg-table*) *sg-goal*))

;(print *syn-data*)
;(finish-output *standard-output*)

(defvar *plan*)

(loop for n-obj from 1 to 5
   for i = 0
   do
     (loop
        while (< i 5)
        ;; create domain
        for blocks = (genscene-repeat *sg-table* "block"
                                      *box*
                                      n-obj
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
          (incf i)
        ;; plan
          (setq *plan*
                (itmp-syn (scene-graph *sg-table* blocks) *sg-goal*
                          :encoding :linear
                          :max-locations (1+ n-obj)
                          :resolution *resolution*))
        ;;(print *plan*)
          ;; write output
          (output-timing n-obj "syn")
          ))

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

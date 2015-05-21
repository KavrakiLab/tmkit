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
         :jobs 8 :threads 2 :nice 1 :povray "/home/ndantam/local/bin/povray")
        ))

(in-package :tmsmt)

(moveit-init "/home/ntd/ros_ws/src/baxter_common/baxter_description/urdf/baxter.urdf")

(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *moveit-container* *group*))
(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))

(context-remove-object *plan-context* "block_a")
(context-remove-object *plan-context* "block_b")
(context-remove-all-objects *plan-context*)
(container-set-group *moveit-container* *group*)

(defparameter *object-graph*
  (load-scene-file "/home/ntd/git/robray/test/scene.robray"))


(defparameter *object-goal*
  (load-scene-file "/home/ntd/git/tmsmt/scene/goal1.robray"))

(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .10)))
(defparameter *tf-tmp* (tf* nil (vec3* -.20 -.40 .0551)))


(defparameter *tf-a* (robray::scene-graph-tf-relative *object-graph*
                                                      "front_table" "block_a"))
(defparameter *tf-b* (robray::scene-graph-tf-relative *object-graph*
                                                      "front_table" "block_b"))

;; A to TMP

(context-apply-scene *plan-context* *object-graph*)
(context-apply-scene *plan-context* *object-graph*)
(defvar *plan-0*)
(defvar *graph-0*)
(multiple-value-setq (*plan-0* *graph-0*)
  (act-transfer-tf *plan-context* *group* *q-all-start* "right_endpoint" *link*
                   "block_a" *tf-grasp-rel* "front_table"  *tf-tmp*))

(assert *plan-0*)

;; B to A
(context-apply-scene *plan-context* *graph-0*)
(defvar *plan-1*)
(defvar *graph-1*)
(multiple-value-setq (*plan-1* *graph-1*)
  (act-transfer-tf *plan-context* *group*
                   (container-merge-group *moveit-container* *group*
                                          (container-plan-endpoint (third *plan-0*))
                                          *q-all-start* )
                   "right_endpoint" *link*
                   "block_b" *tf-grasp-rel* "front_table"  *tf-a*))

(assert *plan-1*)

;; A to B
(context-apply-scene *plan-context* *graph-1*)
(defvar *plan-2*)
(defvar *graph-2*)
(multiple-value-setq (*plan-2* *graph-2*)
  (act-transfer-tf *plan-context* *group*
                   (container-merge-group *moveit-container* *group*
                                          (container-plan-endpoint (third *plan-1*))
                                          *q-all-start* )
                   "right_endpoint" *link*
                   "block_a" *tf-grasp-rel* "front_table"
                   ;;(g* *tf-tmp* (tf* nil (vec3* .05 0 0)))
                   *tf-b* ))
(assert *plan-2*)


;; (time (render-group-itmp *plan-context* *group*
;;                          ;*plan-0*
;;                          (append *plan-0*
;;                                  *plan-1*
;;                                  *plan-2*)
;;                          :render-options  (render-options-default :use-collision t
;;                                                                   :options (render-options-fast))
;;                          :scene-graph (robray::scene-graph-merge (plan-context-robot-graph *plan-context*)
;;                                                                  *object-graph*)
;;                          :frame-name "right_endpoint"))

;; (render-group-config *plan-context* *group* (container-plan-endpoint *plan-place*)
;;                      :options (render-options-fast))

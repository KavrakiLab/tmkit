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

(format t "~&GROUP: ~A~&LINK: ~A" *group* *link*)


(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-container*)))

(format t "~&Vars: ~A~%" (length *q-all-start*))

(context-remove-object *plan-context* "block_a")
(context-remove-object *plan-context* "block_b")

(context-remove-all-objects *plan-context*)


(defparameter *object-graph*
  (load-scene-file "/home/ntd/git/robray/test/scene.robray"))

(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .10)))
(defparameter *tf-tmp* (tf* nil (vec3* -.20 -.40 .0551)))


(container-set-group *moveit-container* *group*)
(context-apply-scene *plan-context* *object-graph*)

;; PICK ;;

;; (setq *plan-pick* (act-pick-tf *plan-context* *q-all-start* *link* "block-a" *tf-grasp-rel*))

;; ;; PLACE ;;
;; (context-attach-object *plan-context* *group* *q-grasp* "right_endpoint" *link* "block-a")

;; (setq *plan-place* (act-place-tf *plan-context*
;;                                  (container-merge-group *moveit-container* *group*
;;                                                         (container-plan-endpoint *plan-pick*)
;;                                                         *q-all-start*)
;;                                  *link*
;;                                  "front-table"

;;                                  "block-a"))

;; A to TMP

(context-apply-scene *plan-context* *object-graph*)
(defvar *plan-0*)
(defvar *graph-0*)
(multiple-value-setq (*plan-0* *graph-0*)
  (act-transfer-tf *plan-context* *group* *q-all-start* "right_endpoint" *link*
                   "block_a" *tf-grasp-rel* "front_table"  *tf-tmp*))

(assert *plan-0*)

;; ;; B to A
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

;; ;; A(tmp) to B

;; ;; (defvar *plan-pick-2*)
;; ;; (defvar *plan-place-2*)

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

;; (multiple-value-setq (*plan-pick-2* *plan-place-2*)
;;   (act-transfer-tf *plan-context* *group* *q-all-start* "right_endpoint" *link*
;;                    "block-a" *tf-grasp-rel* "front-table"  *tf-b*))


;; (assert (and *plan-pick-2* *plan-place-2*))

;; (container-set-start *moveit-container*
;;                      (container-merge-group *moveit-container* *group*
;;                                             *q-grasp*
;;                                             *q-all-start*))


;; (container-scene-send *moveit-container*)

;; (progn
;;   (container-goal-clear *moveit-container*)
;;   (container-set-ws-goal *moveit-container* *link* *e-place*))


;; (defvar *plan-place*)
;; (setq *plan-place* (container-plan *moveit-container*))


;; ;; RETURN ;;
;; (defparameter *q-place* (container-plan-endpoint *plan-place*))

;; (context-dettach-object *plan-context* *group* *q-place* "block-a")

;; (progn
;;   (container-goal-clear *moveit-container*)
;;   (container-set-js-goal *moveit-container* *group* *q-all-start*))

;; (container-scene-send *moveit-container*)

;; (container-set-start *moveit-container*
;;                      (container-merge-group *moveit-container* *group*
;;                                             *q-place*
;;                                             *q-all-start*))

;; (defvar *plan-return*)
;; (setq *plan-return* (container-plan *moveit-container*))

(time (render-group-itmp *plan-context* *group*
                         ;*plan-0*
                         (append *plan-0*
                                 *plan-1*
                                 *plan-2*)
                         :render-options  (render-options-default :use-collision t
                                                                  :options (render-options-fast))
                         :scene-graph (robray::scene-graph-merge (plan-context-robot-graph *plan-context*)
                                                                 *object-graph*)
                         :frame-name "right_endpoint"))

;; (render-group-config *plan-context* *group* (container-plan-endpoint *plan-place*)
;;                      :options (render-options-fast))

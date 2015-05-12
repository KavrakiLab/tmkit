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

(format t "~&Vars: ~A~%" (length *q-all-start*))

(moveit-scene-exp-eval '(:rm "block-a"))
(moveit-scene-exp-eval '(:rm "block-b"))
(moveit-scene-exp-eval '(:clear))
(moveit-scene-file "/home/ntd/git/tmsmt/scene/scene.se")

(context-add-frame-marker *plan-context* "right_endpoint")
(context-add-frame-marker *plan-context* "left_endpoint")

(defparameter *scene-graph* (robray::scene-graph-merge (plan-context-robot-graph *plan-context*)
                                                       (plan-context-object-graph *plan-context*)))



(container-set-group *moveit-container* *group*)


(defparameter *tf-a* (robray::scene-graph-tf-relative (plan-context-object-graph *plan-context*)
                                                      "front-table" "block-a"))
(defparameter *tf-b* (robray::scene-graph-tf-relative (plan-context-object-graph *plan-context*)
                                                      "front-table" "block-b"))

(defparameter *tf-grasp-rel* (tf* (y-angle (* 1 pi)) (vec3* .00 .00 .10)))
(defparameter *tf-tmp* (tf* nil (vec3* -.20 -.40 .0551)))

(defvar *plan-pick*)
(defvar *plan-place*)

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
(defparameter *plan-0*
  (act-transfer-tf *plan-context* *group* *q-all-start* "right_endpoint" *link*
                   "block-a" *tf-grasp-rel* "front-table"  *tf-tmp*))

(assert *plan-0*)

;; B to A
(defparameter *plan-1*
  (multiple-value-setq (*plan-pick-1* *plan-place-1*)
    (act-transfer-tf *plan-context* *group*
                     (container-merge-group *moveit-container* *group*
                                            (container-plan-endpoint (third *plan-0*))
                                            *q-all-start* )
                     "right_endpoint" *link*
                     "block-b" *tf-grasp-rel* "front-table"  *tf-a*)))

(assert *plan-1*)

;; A(tmp) to B

;; (defvar *plan-pick-2*)
;; (defvar *plan-place-2*)

(defparameter *plan-2*
  (multiple-value-setq (*plan-pick-1* *plan-place-1*)
    (act-transfer-tf *plan-context* *group*
                     (container-merge-group *moveit-container* *group*
                                            (container-plan-endpoint (third *plan-1*))
                                            *q-all-start* )
                     "right_endpoint" *link*
                     "block-a" *tf-grasp-rel* "front-table"
                     ;(g* *tf-tmp* (tf* nil (vec3* .05 0 0)))
                     *tf-b* )))
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
                         (append *plan-0*
                                 *plan-1*
                                 *plan-2*)
                         :render-options  (render-options-default :options (render-options-full-hd))
                         :scene-graph *scene-graph*
                         :frame-name "right_endpoint"))

;; (render-group-config *plan-context* *group* (container-plan-endpoint *plan-place*)
;;                      :options (render-options-fast))

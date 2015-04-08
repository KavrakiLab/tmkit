(require :tmsmt)

(in-package :tmsmt)

(moveit-init)

(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *moveit-cx* *group*))

(format t "~&GROUP: ~A~&LINK: ~A" *group* *link*)


(defparameter *q-all-start* (amino:make-vec (container-variable-count *moveit-cx*)))

(format t "~&Vars: ~A~%" (length *q-all-start*))

(moveit-scene-exp-eval `(:seq (:clear)
                              (:box "back-table"
                                    :dimension (1 2 .01)
                                    :translation (-.80 0 0))
                              (:box "front-table"
                                    :dimension (1 2 .01)
                                    :translation (.80 -.4 0))
                              (:box "block"
                                    :dimension (.1 .1 .1)
                                    :translation (0 0 .05)
                                    :parent "front-table")
                              ))

(container-set-start *moveit-cx* *q-all-start*)
(container-set-group *moveit-cx* *group*)

;; (container-scene-add-box *moveit-cx* "table" (amino:vec3* 1 2 .01)
;;                          (amino:tf nil (amino:vec3* -.75 0 0)))

;; (container-scene-add-box *moveit-cx* "table2" (amino:vec3* 1 2 .01)
;;                          (amino:tf nil (amino:vec3* .75 0 0)))

;(container-scene-clear *moveit-cx*)

(container-scene-send *moveit-cx*)

(defparameter *e-goal* (amino:tf (amino:axis-angle (amino:y-angle (* .5 pi)))
                                 (amino:vec3* 0.788372  -0.383374  0.345540)))

(container-set-ws-goal *moveit-cx* *link* *e-goal*)

(container-plan *moveit-cx*)

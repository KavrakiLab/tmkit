(require :tmsmt)

(in-package :tmsmt)

(ros-init :name "lisp")

(format t "ROS initialized~%")

(defparameter *node-handle* (node-handle-create "lisp"))

(format t "Node Handle Created~%")

(defparameter *container* (container-create *node-handle*))
(format t "Container loaded~%")

(defparameter *group* "right_arm")
(defparameter *link* (container-group-endlink *container* *group*))

(format t "~&GROUP: ~A~&LINK: ~A" *group* *link*)


(defparameter *q-all-start* (amino:make-vec (container-variable-count *container*)))

(format t "~&Vars: ~A~%" (length *q-all-start*))

(container-set-start *container* *q-all-start*)
(container-set-group *container* *group*)

(container-scene-add-box *container* "table" (amino:vec3* 1 2 .01)
                         (amino:tf nil (amino:vec3* .75 0 0)))

(container-scene-send *container*)

(defparameter *e-goal* (amino:tf (amino:axis-angle (amino:y-angle (* .5 pi)))
                                 (amino:vec3* 0.788372  -0.383374  0.345540)))

(container-set-ws-goal *container* *link* *e-goal*)

(container-plan *container*)

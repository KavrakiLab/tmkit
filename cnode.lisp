(require :tmsmt)

(in-package :tmsmt)

(ros-init :name "lisp")

(format t "ROS initialized~%")

(defparameter *node-handle* (node-handle-create "lisp"))

(format t "Node Handle Created~%")

(defparameter *container* (container-create *node-handle*))

(format t "Container loaded~%")

(format t "Vars: ~A~%" (tms-container-variable-count *container*))

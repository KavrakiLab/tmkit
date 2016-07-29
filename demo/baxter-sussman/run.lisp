;(require :tmsmt)

(sb-posix:setenv "ROS_PACKAGE_PATH" "/opt/ros/indigo/share/" 1)

(in-package :tmsmt)

(defparameter *demo-dir* (subdir (asdf:system-source-directory :tmsmt)
                                 '(:up "demo" "baxter-sussman")))

(defun demo-file (name type)
  (make-pathname :name name :type type :defaults *demo-dir*))

(defparameter *plan*
  (tmp-driver :start-scene (list "package://baxter_description/urdf/baxter.urdf"
                                 (demo-file "allowed-collision" "robray")
                                 (demo-file "sussman-0" "robray")
                                 )
              :goal-scene (demo-file "sussman-1" "robray")
              :task-domain (demo-file "domain" "pddl")
              :frame "right_endpoint"
              :max-steps 3
              :resolution .1
              :gui t
              :verbose t))


;; (robray::win-stop)
;; (robray::win-join)
;; (sb-ext:quit)

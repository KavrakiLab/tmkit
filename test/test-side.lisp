(require :tmsmt)
(in-package :tmsmt)

(defparameter *ros-pkg-path*
  (namestring (merge-pathnames (make-pathname :directory '(:relative "ros_ws" "src" "baxter_common"))
                               (user-homedir-pathname))))


(defun demo-file (&key directory name type)
  (merge-pathnames (make-pathname :directory `(:relative "demo" ,@(ensure-list directory))
                                  :name name
                                  :type type)
                   *tmsmt-root*))


(sb-posix:setenv "ROS_PACKAGE_PATH" *ros-pkg-path* 1)



(defparameter *baxter* (load-scene-file "package://baxter_description/urdf/baxter.urdf"))



(defparameter *table-dim* (vec3* .5 .5 .01))
(defparameter *box-dim* .060)
(defparameter *resolution* .10)
(defparameter *z* (/ (+ .02 (vec-z *table-dim*) *box-dim*)
                     2))

(defparameter *geometry* (robray::scene-geometry-box (draw-options-default :color '(1 0 0)
                                                                           :type "moveable"
                                                                           :visual t
                                                                           :collision t)
                                                     (vec3* *box-dim* *box-dim* *box-dim*)))


(defparameter *sg-table*
  (scene-graph (scene-frame-fixed nil "table-base"
                                  :tf (tf* (z-angle (* -45 (/ pi 180)))
                                           (vec3* .1 -.3 0)
                                           ))
               (scene-frame-fixed "table-base" "front_table"
                                  :tf (tf* (z-angle (* -30 (/ pi 180)))
                                           '(.6 0 0)
                                           )
                                  :geometry (robray::scene-geometry-box (draw-options-default :color '(.5 .5 .5)
                                                                                              :type "surface"
                                                                                              :visual t
                                                                                              :collision t)
                                                                        *table-dim*))))


(defparameter *sg-block*
  (scene-graph (scene-frame-fixed "front_table"  "block-0"
                                  :tf (tf* nil (vec3* (* 1 *resolution*) 0 *z*))
                                  :geometry *geometry*)
  ))


(defparameter *sg-block-1*
  (scene-graph (scene-frame-fixed "front_table"  "block-0"
                                  :tf (tf* nil (vec3* 0 0 *z*))
                                  :geometry *geometry*)
  ))

(defparameter *scenegraph*
  (scene-graph *baxter* *sg-table* *sg-block*
               (scene-frame-fixed "right_endpoint" "end_effector_grasp"
                                  :tf (tf* (quaternion* 0 1 0 0)
                                           (vec3* 0 0 .075)))))
(robray::win-set-scene-graph *scenegraph*)
(robray::win-run)



(tmp-driver :start-scene (scene-graph *scenegraph*
                                      (demo-file :directory "baxter-sussman"
                                                 :name "allowed-collision"
                                                 :type "robray"))
            :goal-scene (scene-graph *sg-table* *sg-block-1*)
            :gui t
            :pddl (demo-file :directory '("domains" "linear-blocksworld")
                             :name "linear-blocksworld"
                             :type "pddl")
            :output "/tmp/tmkit-test.tmp"
            :scripts (demo-file :directory '("domains" "linear-blocksworld")
                                :name "linear-blocksworld"
                                :type "py"))

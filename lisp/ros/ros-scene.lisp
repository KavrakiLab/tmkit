(in-package :tmsmt)

(cffi:defcfun tms-container-scene-send :void
  (container moveit-container-t))

(defun container-scene-send (container)
  (tms-container-scene-send container))

(cffi:defcfun tms-container-scene-add-box :void
  (container moveit-container-t)
  (name :string)
  (dim amino::vector-3-t)
  (quat amino::quaternion-t)
  (vec amino::vector-3-t))

(defun container-scene-add-box (container name dim tf)
  (tms-container-scene-add-box container name dim
                               (amino:rotation tf)
                               (amino:translation tf)))


(cffi:defcfun tms-container-scene-add-sphere :void
  (container moveit-container-t)
  (name :string)
  (radius :double)
  (position amino::vector-3-t))

(defun container-scene-add-sphere (container name radius position)
  (tms-container-scene-add-sphere container name
                                  (coerce radius 'double-float)
                                  position))


(cffi:defcfun tms-container-scene-add-cylinder :void
  (container moveit-container-t)
  (name :string)
  (radius :double)
  (heght :double)
  (quat amino::quaternion-t)
  (vec amino::vector-3-t))

(defun container-scene-add-cylinder (container name height radius tf)
  (tms-container-scene-add-cylinder container name
                                    (coerce radius  'double-float)
                                    (coerce height  'double-float)
                                    (amino:rotation tf)
                                    (amino:translation tf)))

(cffi:defcfun ("tms_container_scene_clear" container-scene-clear) :void
  (container moveit-container-t))

(cffi:defcfun ("tms_container_scene_rm" container-scene-rm) :void
  (container moveit-container-t)
  (name :string))


(cffi:defcfun ("tms_container_scene_set_color" container-scene-set-color) :void
  (container moveit-container-t)
  (name :string)
  (r :float)
  (g :float)
  (b :float)
  (a :float))

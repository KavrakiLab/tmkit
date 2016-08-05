(in-package |tmsmtpy|)

(defun |hello| ()
  (format t "~&Hello World!~%"))


(defun |bind_scene_state| (x)
  (setq tmsmt::*scene-state-function* x))


(defun |bind_scene_objects| (x)
  (setq tmsmt::*scene-objects-function* x))

(defun |collect_frame_type| (scene type)
  (tmsmt::scene-collect-type scene type))

(defun |mangle| (&rest args)
  (tmsmt::smt-mangle-list args))

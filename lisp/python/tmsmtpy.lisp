(in-package |tmsmtpy|)

(defvar *scene-state-function*)

(defun |hello| ()
  (format t "~&Hello World!~%"))


(defun |bind_scene_state| (x)
  (setq *scene-state-function* x))


(defun |collect_frame_type| (scene type)
  (tmsmt::scene-collect-type scene type))

(defun |mangle| (&rest args)
  (tmsmt::smt-mangle-list args))

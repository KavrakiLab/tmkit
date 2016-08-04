(in-package |tmsmtpy|)

(defvar *scene-state-function*)

(defun |hello| ()
  (format t "~&Hello World!~%"))


(defun |bind_scene_state| (x)
  (setq *scene-state-function* x))

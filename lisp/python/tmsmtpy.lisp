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

(defun |bind_refine_operator| (x)
  (setq tmsmt::*refine-operator-function* x))

(defun |op_motion| (motion-plan)
  (tmsmt::tm-op-motion motion-plan))

(defun |op_reparent| (scene config parent frame)
  (tmsmt::tm-op-reparent scene parent frame
                         :configuration-map config))


(aminopy::def-subs-accessors tmsmt::tm-op
  ("initial_config" tmsmt::tm-op-initial-config)
  ("initial_scene" tmsmt::tm-op-initial-scene-graph)
  ("final_config" tmsmt::tm-op-final-config)
  ("final_scene" tmsmt::tm-op-final-scene-graph))

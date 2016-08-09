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

;;;;;;;;;;;;;;;;;
;;; Operators ;;;
;;;;;;;;;;;;;;;;;

(defun |op_nop| (scene config)
  (tmsmt::tm-op-nop scene config))

(defun |op_motion| (previous-op sub-scene-graph goal)
  (let ((mp (motion-plan sub-scene-graph
                         (tmsmt::tm-op-final-config previous-op)
                         :workspace-goal goal
                         :simplify t
                         :timeout 1d0)))
    (if mp
        (tmsmt::tm-op-motion mp)
        (clpython:py-bool nil))))

(defun |op_reparent| (previous-op parent frame)
  (tmsmt::tm-op-reparent (tmsmt::tm-op-final-scene-graph previous-op)
                         parent frame
                         :configuration-map (tmsmt::tm-op-final-config previous-op)))


(defun |plan| (&rest ops)
  (tmsmt::tm-plan ops))

(aminopy::def-subs-accessors tmsmt::tm-op
  ("initial_config" tmsmt::tm-op-initial-config)
  ("initial_scene" tmsmt::tm-op-initial-scene-graph)
  ("final_config" tmsmt::tm-op-final-config)
  ("final_scene" tmsmt::tm-op-final-scene-graph))

(defun |op_tf_abs| (op frame)
  (tmsmt::tm-op-tf-abs op frame))

(defun |op_tf_rel| (op parent child)
  (tmsmt::tm-op-tf-rel op parent child))

(defun |PlanningFailure| (&optional value)
  (make-instance 'tmsmt::planning-failure :value value))

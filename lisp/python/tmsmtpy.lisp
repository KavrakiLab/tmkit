(in-package |tmsmtpy|)

(defun |bind_scene_state| (function)
  "Bind FUNCTION as the scene state function."
  (setq tmsmt::*scene-state-function* function))

(defun |bind_goal_state| (function)
  "Bind FUNCTION as the goal state function."
  (setq tmsmt::*goal-state-function* function))

(defun |bind_scene_objects| (function)
  "Bind FUNCTION as the scene objects function."
  (setq tmsmt::*scene-objects-function* function))

(defun |collect_frame_type| (scene type)
  "Return all frames in SCENE of the given TYPE."
  (tmsmt::scene-collect-type scene type))

(defun |bind_refine_operator| (function operator)
  "Bind FUNCTION as the refinement function for OPERATOR."
  (setf (gethash operator tmsmt::*refine-functions*)
        function))

(defun |mangle| (&rest args)
  "Convert ARGS in to a valid PDDL/SMTlib symbol.

Examples:

    mangle('a', 'b') => 'a__b'"

  (tmsmt::smt-mangle-list args))

;;;;;;;;;;;;;;;;;
;;; Operators ;;;
;;;;;;;;;;;;;;;;;

(defun |plan| (&rest operators)
  "Create a plan consisting of task-motion OPERATORS."
  (tmsmt::tm-plan operators))

(defun |op_nop| (scene config)
  "Create a NO-OP task-motion operator."
  (tmsmt::tm-op-nop scene config))

(defun |op_motion| (previous-op sub-scene-graph goal)
  "Create a motion-plan task-motion operator."
  (let ((mp (motion-plan sub-scene-graph
                         (tmsmt::tm-op-final-config previous-op)
                         :workspace-goal goal
                         :simplify t
                         :timeout tmsmt::*motion-timeout*)))
    (if mp
        (|plan| previous-op (tmsmt::tm-op-motion mp))
        (clpython:py-bool nil))))

(defun |op_reparent| (previous-op parent frame)
  "Create a reparent task-motion operator."
  (|plan| previous-op
          (tmsmt::tm-op-reparent (tmsmt::tm-op-final-scene-graph previous-op)
                                 parent frame
                                 :configuration-map (tmsmt::tm-op-final-config previous-op))))

(aminopy::def-subs-accessors tmsmt::tm-op
  ("initial_config" tmsmt::tm-op-initial-config)
  ("initial_scene" tmsmt::tm-op-initial-scene-graph)
  ("final_config" tmsmt::tm-op-final-config)
  ("final_scene" tmsmt::tm-op-final-scene-graph))

(defun |op_tf_abs| (operator frame)
  "Return the absolute pose of FRAME after OPERATOR."
  (tmsmt::tm-op-tf-abs operator frame))

(defun |op_tf_rel| (operator parent child)
  "Return the absolute pose of from parent to child after OPERATOR."
  (tmsmt::tm-op-tf-rel operator parent child))

(defun |PlanningFailure| (&optional value)
  "Create an exception indicating motion planning failure."
  (make-instance 'tmsmt::planning-failure :value value))

(defpackage tmsmt/pddl
  (:use :cl)
  (:export
   :domain
   :define
   :exists
   :forall
   :define
   :problem))

(defpackage :tmsmt
  (:use :cl :alexandria :sycamore
        :amino :sycamore :robray :sycamore-util :sycamore-cgen
        :tmsmt/pddl
        :smt-symbol)
  (:export
   :tmp-driver
   :tmp-refine

   :tm-op
   :tm-op-nop
   :tm-op-action
   :tm-op-reparent
   :tm-op-motion
   :tm-plan
   :tm-plan-endpoint
   :tm-plan-motion-plans))


(defpackage tmsmtpy
  (:use :cl :alexandria :sycamore :amino :sycamore :robray :sycamore-util :sycamore-cgen :tmsmt
        :aminopy)
  (:nicknames |tmsmtpy|)

  #.(let ((result
           (list
            ;; binders
            :|bind_goal_state|
            :|bind_scene_state|
            :|bind_scene_objects|
            :|bind_refine_operator|
            :|bind_collision_constraint|

            ;; Operators
            :|op_nop|
            :|op_motion|
            :|op_cartesian|
            :|op_reparent|
            :|op_tf_abs|
            :|op_tf_rel|
            :|plan|

            :|PlanningFailure|

            ;; helpers
            :|collect_frame_type|
            :|mangle|
            )))
      (do-external-symbols (s :aminopy)
        (push s result))
      (push :export result)
      result))

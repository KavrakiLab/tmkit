#ifndef TMPLAN_H
#define TMPLAN_H

enum tmplan_op {
    TMPLAN_OP_ACTION,
    TMPLAN_OP_MOTION_PLAN,
    TMPLAN_OP_MOTION_REPARENT

};

struct tmplan;

AA_API struct tmplan *
tmplan_create (struct aa_mem_region *reg);

struct tmplan_op_action;

AA_API struct tmplan_op_action *
tmplan_op_action_create (struct aa_mem_region *reg);

AA_API void
tmplan_op_action_set (struct tmplan_op_action *op, const char *value );

AA_API const char *
tmplan_op_action_get (const struct tmplan_op_action *op );

struct tmplan_op_motion_plan;

AA_API struct tmplan_op_motion_plan *
tmplan_op_motion_plan_create (struct aa_mem_region *reg);

struct tmplan_op_reparent;

AA_API struct tmplan_op_reparent *
tmplan_op_reparent_create (struct aa_mem_region *reg);



AA_API void
tmplan_parse (FILE *in, struct aa_mem_region *reg);

#endif /* TMPLAN_H*/

#ifndef TMPLAN_H
#define TMPLAN_H

enum tmplan_op_type {
    TMPLAN_OP_ACTION,
    TMPLAN_OP_MOTION_PLAN,
    TMPLAN_OP_REPARENT
};

struct tmplan;

AA_API struct tmplan *
tmplan_create (struct aa_mem_region *reg);

AA_API void
tmplan_add_op(struct tmplan * tmp, void *op);

struct tmplan_op;

AA_API struct tmplan_op *
tmplan_last_op(struct tmplan * tmp);

AA_API enum tmplan_op_type
tmplan_op_type( struct tmplan_op *op );

struct tmplan_op_action;

AA_API struct tmplan_op_action *
tmplan_op_action_create (struct tmplan *tmp);

AA_API void
tmplan_op_action_set (struct tmplan_op_action *op, const char *value );

AA_API const char *
tmplan_op_action_get (const struct tmplan_op_action *op );

struct tmplan_op_motion_plan;

AA_API struct tmplan_op_motion_plan *
tmplan_op_motion_plan_create (struct tmplan *tmp);

struct tmplan_op_reparent;

AA_API struct tmplan_op_reparent *
tmplan_op_reparent_create (struct tmplan *tmp);

AA_API struct tmplan*
tmplan_parse (FILE *in, struct aa_mem_region *reg);


AA_API int
tmplan_write (const struct tmplan *tmp, FILE *out );

#endif /* TMPLAN_H*/

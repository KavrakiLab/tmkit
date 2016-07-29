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
tmplan_finish_op(struct tmplan * tmp );

AA_API void
tmplan_add_op(struct tmplan * tmp, void *op);

AA_API void
tmplan_add_action(struct tmplan * tmp);

AA_API void
tmplan_add_motion_plan(struct tmplan * tmp);

AA_API void
tmplan_add_reparent(struct tmplan * tmp);


struct tmplan_op;

AA_API struct tmplan_op *
tmplan_last_op(struct tmplan * tmp);

AA_API enum tmplan_op_type
tmplan_op_type( struct tmplan_op *op );

struct tmplan_op_action;

AA_API void
tmplan_op_action_set (struct tmplan_op_action *op, const char *value );

AA_API const char *
tmplan_op_action_get (const struct tmplan_op_action *op );

struct tmplan_op_motion_plan;

AA_API void
tmplan_op_motion_plan_add_var (struct tmplan_op_motion_plan *op, const char *name);

AA_API void
tmplan_op_motion_plan_map_var (struct tmplan_op_motion_plan *op,
                               void (*function)(void *cx, const char *name),
                               void *cx);

AA_API void
tmplan_op_motion_plan_path_start (struct tmplan_op_motion_plan *op );

AA_API void
tmplan_op_motion_plan_path_add (struct tmplan_op_motion_plan *op, double x);

AA_API void
tmplan_op_motion_plan_path_finish (struct tmplan_op_motion_plan *op );

struct tmplan_op_reparent;

AA_API void
tmplan_op_reparent_set_frame (struct tmplan_op_reparent *op, const char *frame);

AA_API void
tmplan_op_reparent_set_new_parent (struct tmplan_op_reparent *op, const char *frame);

AA_API const char*
tmplan_op_reparent_get_frame (struct tmplan_op_reparent *op);

AA_API const char*
tmplan_op_reparent_get_new_parent (struct tmplan_op_reparent *op);

AA_API struct tmplan*
tmplan_parse (FILE *in, struct aa_mem_region *reg);


AA_API int
tmplan_write (const struct tmplan *tmp, FILE *out );

#endif /* TMPLAN_H*/

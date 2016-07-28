#ifndef TMPLAN_H
#define TMPLAN_H

enum tmplan_op {
    TMPLAN_OP_ACTION,
    TMPLAN_OP_MOTION_PLAN,
    TMPLAN_OP_MOTION_REPARENT

};

struct tmplan;

struct tmplan_op_action;

struct tmplan_op_motion_plan;

struct tmplan_op_reparent;


AA_API void
tmplan_parse (FILE *in);

#endif /* TMPLAN_H*/

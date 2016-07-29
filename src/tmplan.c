#include <amino.h>

#include "tmsmt/tmplan_internal.h"

AA_API struct tmplan *
tmplan_create (struct aa_mem_region *reg)
{
    struct tmplan *x = AA_MEM_REGION_NEW(reg, struct tmplan);
    x->reg = reg;
    return x;
}


AA_API struct tmplan_op_action *
tmplan_op_action_create (struct aa_mem_region *reg)
{
    return AA_MEM_REGION_NEW(reg, struct tmplan_op_action);
}

AA_API void
tmplan_op_action_set (struct tmplan_op_action *op, const char *value )
{
    op->action = value;
}


AA_API const char *
tmplan_op_action_get (const struct tmplan_op_action *op )
{
    return op->action;
}


AA_API struct tmplan_op_motion_plan *
tmplan_op_motion_plan_create (struct aa_mem_region *reg)
{

    return AA_MEM_REGION_NEW(reg, struct tmplan_op_motion_plan);
}

AA_API struct tmplan_op_reparent *
tmplan_op_reparent_create (struct aa_mem_region *reg)
{

    return AA_MEM_REGION_NEW(reg, struct tmplan_op_reparent);
}

#include <amino.h>

#include "tmsmt/tmplan_internal.h"

AA_API struct tmplan *
tmplan_create (struct aa_mem_region *reg)
{
    struct tmplan *x = AA_MEM_REGION_NEW(reg, struct tmplan);
    x->reg = reg;
    x->rlist = aa_mem_rlist_alloc(x->reg);
    x->count = 0;
    x->last = NULL;
    return x;
}

AA_API void
tmplan_add_op(struct tmplan * tmp, void *op)
{
    fprintf(stderr, "adding\n");
    aa_mem_rlist_enqueue_ptr(tmp->rlist, op);
    tmp->last = (struct tmplan_op*)op;
    tmp->count++;
}

AA_API struct tmplan_op *
tmplan_last_op(struct tmplan * tmp)
{
    return tmp->last;
}

AA_API enum tmplan_op_type
tmplan_op_type( struct tmplan_op *op )
{
    return op->type;
}

AA_API struct tmplan_op_action *
tmplan_op_action_create (struct tmplan *tmp)
{
    struct tmplan_op_action *op = AA_MEM_REGION_NEW(tmp->reg, struct tmplan_op_action);
    op->parent.type = TMPLAN_OP_ACTION;
    op->parent.tmp = tmp;
    return op;
}

AA_API void
tmplan_op_action_set (struct tmplan_op_action *op, const char *value )
{
    op->action = aa_mem_region_dup( op->parent.tmp->reg,
                                    value,
                                    1+strlen(value));
}

AA_API const char *
tmplan_op_action_get (const struct tmplan_op_action *op )
{
    return op->action;
}


AA_API struct tmplan_op_motion_plan *
tmplan_op_motion_plan_create (struct tmplan *tmp)
{
    struct tmplan_op_motion_plan *op = AA_MEM_REGION_NEW(tmp->reg, struct tmplan_op_motion_plan);
    op->parent.type = TMPLAN_OP_MOTION_PLAN;
    op->parent.tmp = tmp;
    return op;
}

AA_API struct tmplan_op_reparent *
tmplan_op_reparent_create (struct tmplan *tmp)
{
    struct tmplan_op_reparent *op = AA_MEM_REGION_NEW(tmp->reg, struct tmplan_op_reparent);
    op->parent.type = TMPLAN_OP_REPARENT;
    op->parent.tmp = tmp;
    return op;
}

AA_API int
tmplan_write (const struct tmplan *tmp, FILE *out )
{
    for( struct aa_mem_cons *c = tmp->rlist->head; c; c = c->next ) {
        struct tmplan_op *op =  (struct tmplan_op *)c->data;
        switch( op->type ) {
        case TMPLAN_OP_ACTION: {
            struct tmplan_op_action *x = (struct tmplan_op_action *)op;
            if( x->action ) {
                fprintf(out,"a %s\n",x->action);
            } else {
                fprintf(out, "a\n");
            }
        } break;
        case TMPLAN_OP_MOTION_PLAN: {
            struct tmplan_op_motion_plan *x = (struct tmplan_op_motion_plan *)op;
        } break;
        case TMPLAN_OP_REPARENT: {
            struct tmplan_op_reparent *x = (struct tmplan_op_reparent *)op;
        } break;
        }
    }
}

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



struct map_ops_cx {
    void *cx;
    void (*function)(void *cx, const struct tmplan_op *op);
};

AA_API void
map_ops_helper (void *cx_, void *data ) {
    struct map_ops_cx * cx = (struct map_ops_cx *)cx_;
    cx->function(cx->cx, data);
}

AA_API int
tmplan_map_ops (const struct tmplan *tmp,
                void (*function)(void *cx, const struct tmplan_op *op),
                void *cx )
{
    struct map_ops_cx cxp;
    cxp.cx = cx;
    cxp.function = function;
    aa_mem_rlist_map( tmp->rlist, map_ops_helper, &cxp );
}




static void
tmplan_write_helper (void *cx, const struct tmplan_op *op )
{
    FILE *out = (FILE*)cx;
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
        fprintf(out, "m\n");
        struct tmplan_op_motion_plan *x = (struct tmplan_op_motion_plan *)op;
    } break;
    case TMPLAN_OP_REPARENT: {
        fprintf(out, "p\n");
        struct tmplan_op_reparent *x = (struct tmplan_op_reparent *)op;
    } break;
    }
}

AA_API int
tmplan_write (const struct tmplan *tmp, FILE *out )
{
    tmplan_map_ops( tmp, tmplan_write_helper, out );
}

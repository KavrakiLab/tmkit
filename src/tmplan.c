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
tmplan_finish_op(struct tmplan * tmp )
{
    if( tmp->last ) {
        if( TMPLAN_OP_MOTION_PLAN == tmp->last->type ) {
            tmplan_op_motion_plan_path_finish(
                (struct tmplan_op_motion_plan*) tmp->last );
        }
        tmp->last = NULL;
    }
}

AA_API void
tmplan_add_op(struct tmplan * tmp, void *op)
{
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

AA_API void
tmplan_add_action(struct tmplan *tmp)
{
    tmplan_finish_op(tmp);
    struct tmplan_op_action *op = AA_MEM_REGION_NEW(tmp->reg, struct tmplan_op_action);
    op->parent.type = TMPLAN_OP_ACTION;
    op->parent.tmp = tmp;
    tmplan_add_op(tmp,op);
}

AA_API void
tmplan_op_action_set (struct tmplan_op_action *op, const char *value )
{
    op->action = aa_mem_region_strdup( op->parent.tmp->reg, value );
}

AA_API const char *
tmplan_op_action_get (const struct tmplan_op_action *op )
{
    return op->action;
}


AA_API void
tmplan_add_motion_plan(struct tmplan *tmp)
{
    tmplan_finish_op(tmp);
    struct tmplan_op_motion_plan *op = AA_MEM_REGION_NEW(tmp->reg, struct tmplan_op_motion_plan);
    op->parent.type = TMPLAN_OP_MOTION_PLAN;
    op->parent.tmp = tmp;
    op->names = aa_mem_rlist_alloc(tmp->reg);
    op->config_cnt = 0;
    op->path = NULL;
    op->path_cnt = 0;
    tmplan_add_op(tmp,op);
}


AA_API void
tmplan_op_motion_plan_add_var (struct tmplan_op_motion_plan *op, const char *name)
{
    op->config_cnt++;
    aa_mem_rlist_enqueue_cpy(op->names, name, 1+strlen(name));

}

struct map_var_cx {
    void *cx;
    void (*function)(void *cx, const char *name);
};

static void
map_var_helper( void *cx_, void *data )
{
    struct map_var_cx *cx = (struct map_var_cx *)cx_;
    cx->function(cx->cx, (const char *)data);
}

AA_API void
tmplan_op_motion_plan_map_var (struct tmplan_op_motion_plan *op,
                               void (*function)(void *cx, const char *name),
                               void *cx)
{
    struct map_var_cx cxp;
    cxp.cx = cx;
    cxp.function = function;
    aa_mem_rlist_map( op->names, map_var_helper, &cxp );
}


AA_API void
tmplan_op_motion_plan_path_start (struct tmplan_op_motion_plan *op )
{
    (void)op;
}


AA_API void
tmplan_op_motion_plan_path_add (struct tmplan_op_motion_plan *op, double x)
{
    size_t i = op->path_cnt++;
    op->path = aa_mem_region_tmprealloc( op->parent.tmp->reg,
                                         sizeof(double) * op->path_cnt );
    op->path[i] = x;
}

AA_API void
tmplan_op_motion_plan_path_finish (struct tmplan_op_motion_plan *op )
{
    struct aa_mem_region *reg = op->parent.tmp->reg;
    size_t size = op->path_cnt*sizeof(double);
    op->path = aa_mem_region_alloc( reg, size );
}

AA_API void
tmplan_add_reparent(struct tmplan *tmp)
{
    tmplan_finish_op(tmp);
    struct tmplan_op_reparent *op = AA_MEM_REGION_NEW(tmp->reg, struct tmplan_op_reparent);
    op->parent.type = TMPLAN_OP_REPARENT;
    op->parent.tmp = tmp;
    op->frame = NULL;
    op->new_parent = NULL;
    tmplan_add_op(tmp,op);
}

AA_API void
tmplan_op_reparent_set_frame (struct tmplan_op_reparent *op, const char *frame)
{
    op->frame = aa_mem_region_strdup(op->parent.tmp->reg, frame);
}

AA_API void
tmplan_op_reparent_set_new_parent (struct tmplan_op_reparent *op, const char *frame)
{
    op->new_parent = aa_mem_region_strdup(op->parent.tmp->reg, frame);
}

AA_API const char*
tmplan_op_reparent_get_frame (struct tmplan_op_reparent *op)
{
    return op->frame;
}

AA_API const char*
tmplan_op_reparent_get_new_parent (struct tmplan_op_reparent *op)
{
    return op->new_parent;
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


static void write_varname( void *cx, const char *name )
{
    fprintf((FILE*)cx, " %s", name);
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
        struct tmplan_op_motion_plan *x = (struct tmplan_op_motion_plan *)op;
        fprintf(out, "m");
        tmplan_op_motion_plan_map_var( x, write_varname, out );
        fprintf(out, "\n");
        for( size_t i = 0; i < x->path_cnt / x->config_cnt; i++ ) {
            fprintf(out, "p");
            for( size_t j = 0; j < x->config_cnt; j ++ ) {
                fprintf(out, " %f", x->path[i*x->config_cnt + j] );
            }
            fprintf(out, "\n");
        }
    } break;
    case TMPLAN_OP_REPARENT: {
        struct tmplan_op_reparent *x = (struct tmplan_op_reparent *)op;
        fprintf(out, "r %s %s\n",
                x->frame, x->new_parent );
    } break;
    }
}

AA_API int
tmplan_write (const struct tmplan *tmp, FILE *out )
{
    tmplan_map_ops( tmp, tmplan_write_helper, out );
}

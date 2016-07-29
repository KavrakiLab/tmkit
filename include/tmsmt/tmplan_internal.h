#ifndef TMPLAN_INTERNAL_H
#define TMPLAN_INTERNAL_H

#include "tmplan.h"

struct tmplan {
    struct aa_mem_region *reg;
    struct aa_mem_rlist *rlist;
    struct tmplan_op *last;
    size_t count;
};

struct tmplan_op {
    enum tmplan_op_type type;
    struct tmplan *tmp;
};

struct tmplan_op_action {
    struct tmplan_op parent;
    struct aa_mem_rlist *namelist;
    const char *action;
};


struct tmplan_op_motion_plan {
    struct tmplan_op parent;
    size_t config_cnt;
    struct aa_mem_rlist *names;
    double *path;  ///< plan, size config_count*point_cnt
    size_t path_cnt;
};


struct tmplan_op_reparent {
    struct tmplan_op parent;
    const char *frame;
    const char *new_parent;
};


#endif /* TMPLAN_INTERNAL_H*/

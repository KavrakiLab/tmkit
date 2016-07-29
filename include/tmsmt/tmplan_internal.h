#ifndef TMPLAN_H
#define TMPLAN_H

#include "tmplan.h"

struct tmplan {
    struct aa_mem_region *reg;
};

struct tmplan_op_action {
    const char *action;
};


struct tmplan_op_motion_plan {
    size_t config_cnt;
    size_t point_cnt; ///< number of waypoints
    const char **names;
    double *path;  ///< plan, size config_count*point_cnt
};


struct tmplan_op_reparent {
    const char *frame;
    const char *new_parent;
};


#endif /* TMPLAN_H*/

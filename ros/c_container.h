#ifndef C_CONTAINTER_H
#define C_CONTAINTER_H

#ifdef __cplusplus
extern "C" {
#endif

struct container;


struct container *
container_create( const char *name_space, const char *robot_description );

void
container_destroy( struct container * );

int
container_set_start( struct container * c, const char *group, size_t n, const double *q );

int
container_set_ws_goal( struct container * c, const char *name, const double quat[4], const double vec[3] );

int
container_plan( struct container * c );


int
container_group_fk( struct container * c, const char *group, size_t n, const double *q_group,
                    double r[4], double v[3]  );


int
container_link_fk( struct container * c, const char *link, size_t n, const double *q_all,
                   double r[4], double v[3]  );


#ifdef __cplusplus
}
#endif

#endif

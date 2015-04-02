#ifndef C_CONTAINTER_H
#define C_CONTAINTER_H

#ifdef __cplusplus
extern "C" {
#endif

struct container;


/**
 * Create a new motion planning container.
 */
struct container *
container_create( const char *name_space, const char *robot_description );

/**
 * Number of variables for container
 */
size_t
container_variable_count( struct container *c );

/**
 * Merge group configuration into full configuration.
 */
int
container_merge_group( struct container *c, const char *group,
                       size_t n_group, const double *q_group,
                       size_t n_all, double *q_all );

/**
 *  Destroy a motion planning container
 */
void
container_destroy( struct container * );

/**
 * Set container start state.
 */
int
container_set_start( struct container * c, size_t n_all, const double *q_all );

/**
 * Set group to plan for.
 */
int
container_set_group( struct container * c, const char *group );


int
container_merge_goal_clear( struct container *c );

/**
 * Set a workspace goal.
 */
int
container_set_ws_goal( struct container * c, const char *link, const double quat[4], const double vec[3],
                       double tol_x, double tol_angle );

/**
 * Compute a motion plan using previously set options.
 */
int
container_plan( struct container * c );

/**
 * Compute forward kinematics for end link of a group.
 */
int
container_group_fk( struct container * c, const char *group, size_t n, const double *q_group,
                    double r[4], double v[3]  );


/**
 * Compute forward kinematics for a link.
 */
int
container_link_fk( struct container * c, const char *link, size_t n, const double *q_all,
                   double r[4], double v[3]  );

/**
 * Find the link at the end of a group.
 */
const char *
container_group_endlink( struct container * c, const char *group );

#ifdef __cplusplus
}
#endif

#endif

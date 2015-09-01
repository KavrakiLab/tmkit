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
tms_container_create( struct cros_node_handle *nh, const char *robot_description );

/**
 * Number of variables for container
 */
size_t
tms_container_variable_count( struct container *c );

/**
 * Merge group configuration into full configuration.
 */
int
tms_container_merge_group( struct container *c, const char *group,
                       size_t n_group, const double *q_group,
                       size_t n_all, double *q_all );

/**
 *  Destroy a motion planning container
 */
void
tms_container_destroy( struct container * );

/**
 * Set container start state.
 */
int
tms_container_set_start( struct container * c, size_t n_all, const double *q_all );

/**
 * Set group to plan for.
 */
int
tms_container_set_group( struct container * c, const char *group );

/**
 * Clear goal constraints.
 */
int
tms_container_goal_clear( struct container *c );


/**
 * Set a joint space goal.
 */
int
tms_container_set_js_goal( struct container * c, const char *group, size_t n_all, double *q_all );

/**
 * Set a workspace goal.
 */
int
tms_container_set_ws_goal( struct container * c, const char *link, const double quat[4], const double vec[3],
                           double tol_x, double tol_angle );

/**
 * Compute a motion plan using previously set options.
 */
int
tms_container_plan( struct container * c,
                    double timeout,
                    size_t *n_vars, size_t *n_points, double **points);

/**
 * Compute forward kinematics for end link of a group.
 */
int
tms_container_group_fk( struct container * c, const char *group, size_t n, const double *q_group,
                        double r[4], double v[3]  );

/**
 * Return number of joints in the group.
 */
size_t
tms_container_group_joint_count( struct container * c, const char *group );

/**
 * Return name of the ith joint in the group.
 */
const char *
tms_container_group_joint_name( struct container * c, const char *group, size_t i );

/**
 * Compute forward kinematics for a link.
 */
int
tms_container_link_fk( struct container * c, const char *link, size_t n, const double *q_all,
                       double r[4], double v[3] );

/**
 * Find the link at the end of a group.
 */
const char *
tms_container_group_endlink( struct container * c, const char *group );

/**
 * Find the link at the end of a group.
 */
const char *
tms_container_group_endlink( struct container * c, const char *group );

int
tms_container_set_planner( struct container * c, const char *planner );

int
tms_container_set_volume( struct container * c,
                          const double min[3],
                          const double max[3] );

#ifdef __cplusplus
}
#endif

#endif

#ifndef TMPLAN_H
#define TMPLAN_H

/**
 * @file tmplan.h
 * @brief Data structure for task-motion plans
 */


/**
 * Types of operators in a task-motion plan.
 */
enum tmplan_op_type {
    TMPLAN_OP_ACTION,       ///< A task action
    TMPLAN_OP_MOTION_PLAN,  ///< A motion plan
    TMPLAN_OP_REPARENT      ///< A scene-graph reparenting
};


/**
 * @struct tmplan
 *
 * Opaque structure for a task-motion plan
 */
struct tmplan;

/**
 * Create a new task-motion plan allocated out of the given region.
 *
 *
 * To deallocate the task-motion plan, pop it from the region using
 * aa_mem_region_pop().
 */
AA_API struct tmplan *
tmplan_create (struct aa_mem_region *reg);


/**
 * Return the number of operators in the plan
 */
AA_API size_t
tmplan_op_count (struct tmplan * tmp );

/**
 * Finalize the last added operator.
 *
 * This function is called internally by the plan file parser.
 */
AA_API void
tmplan_finish_op(struct tmplan * tmp );

/**
 * Add a new operator to the plan.
 *
 * @pre The previously added operator (if any) must be finalized
 *      before this operator is allocated from the memory region.
 *
 * This function is called internally by the plan file parser.
 */
AA_API void
tmplan_add_op(struct tmplan * tmp, void *op);

/**
 * Add a task operator to the plan.
 */
AA_API void
tmplan_add_action(struct tmplan * tmp);

/**
 * Add a motion plan to the plan.
 */
AA_API void
tmplan_add_motion_plan(struct tmplan * tmp);

/**
 * Add a reparent operator to the plan.
 */
AA_API void
tmplan_add_reparent(struct tmplan * tmp);

/**
 * @struct tmplan_op
 *
 * Opaque structure for a task operator.
 */

struct tmplan_op;

/**
 * Return a pointer to the last added operator.
 *
 * This function is used internally by the plan file parser.
 */
AA_API struct tmplan_op *
tmplan_last_op(struct tmplan * tmp);

/**
 * Return the type of the operator.
 */
AA_API enum tmplan_op_type
tmplan_op_type( const struct tmplan_op *op );

/**
 * @struct tmplan_op_action
 *
 * Opaque type for a task action.
 */
struct tmplan_op_action;

/**
 * Set the value of the task action, represented as a string.
 */
AA_API void
tmplan_op_action_set (struct tmplan_op_action *op, const char *value );

/**
 * Get the value of the task action, represented as a string.
 */
AA_API const char *
tmplan_op_action_get (const struct tmplan_op_action *op );

/**
 * @struct tmplan_op_motion_plan
 *
 * Opaque type for a motion plan.
 */
struct tmplan_op_motion_plan;

/**
 * Add a new configuration variable to the motion plan.
 */
AA_API void
tmplan_op_motion_plan_add_var (struct tmplan_op_motion_plan *op, const char *name);

/**
 * Apply function to each configuration variable name in the motion plan.
 */
AA_API void
tmplan_op_motion_plan_map_var (struct tmplan_op_motion_plan *op,
                               void (*function)(void *cx, const char *name),
                               void *cx);

/**
 * Fill name with the configuration variable names.
 */
AA_API void
tmplan_op_motion_plan_vars ( struct tmplan_op_motion_plan *op,
                             size_t n, const char **name );

/**
 * Apply function to each op in the plan.
 */
AA_API int
tmplan_map_ops (const struct tmplan *tmp,
                void (*function)(void *cx, const struct tmplan_op *op),
                void *cx );

/**
 * Preprate to add points to the motion plan.
 */
AA_API void
tmplan_op_motion_plan_path_start (struct tmplan_op_motion_plan *op );

/**
 * Add the next waypoint configuration value to the motion plan.
 */
AA_API void
tmplan_op_motion_plan_path_add (struct tmplan_op_motion_plan *op, double x);

/**
 * Finalize the motion plan path.
 */
AA_API void
tmplan_op_motion_plan_path_finish (struct tmplan_op_motion_plan *op );

/**
 * Return a pointer to the path data.
 */
AA_API double *
tmplan_op_motion_plan_path(struct tmplan_op_motion_plan *op );

/**
 * Return the number of configuration variables used for the path.
 *
 */
AA_API size_t
tmplan_op_motion_plan_config_count(struct tmplan_op_motion_plan *op );

/**
 * Return the number of elements in the path.
 *
 * The number of waypoints in the path is the path size divided by the
 * number of configuration variables.
 *
 */
AA_API size_t
tmplan_op_motion_plan_path_size(struct tmplan_op_motion_plan *op );

/**
 * @struct tmplan_op_motion_plan
 *
 * Opaque type for a reparent operation.
 */
struct tmplan_op_reparent;

/**
 * Set the frame being reparented.
 */
AA_API void
tmplan_op_reparent_set_frame (struct tmplan_op_reparent *op, const char *frame);

/**
 * Set the new parent.
 */
AA_API void
tmplan_op_reparent_set_new_parent (struct tmplan_op_reparent *op, const char *frame);

/**
 * Get the frame being reparented.
 */
AA_API const char*
tmplan_op_reparent_get_frame (struct tmplan_op_reparent *op);

/**
 * Get the new parent.
 */
AA_API const char*
tmplan_op_reparent_get_new_parent (struct tmplan_op_reparent *op);

/**
 * Parse a plan file, allocation out of the given region.
 */
AA_API struct tmplan*
tmplan_parse_filename (const char *filename, struct aa_mem_region *reg);

/**
 * Parse a plan file, allocation out of the given region.
 */
AA_API struct tmplan*
tmplan_parse_file (FILE *in, struct aa_mem_region *reg);


/**
 * Write a tmplan to `out'.
 */
AA_API int
tmplan_write (const struct tmplan *tmp, FILE *out );

#endif /* TMPLAN_H*/

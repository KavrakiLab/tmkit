#ifdef __cplusplus
extern "C" {
#endif


struct syn_handle;

struct syn_plan {
    size_t n_step;
    size_t *src_object;
    size_t *dst_location;
};

/* Create a new synergistic planning task-planning handle */
struct syn_handle *syn_handle_create(
    size_t n_obj, size_t *obj_location, size_t n_location, size_t *n_label, size_t **labels );


/* Set the goal condition
 *
 * @param n_obj Number of objects with goal conditions
 * @param obj_index Array of object indices
 * @param obj_label The goal label for corresponding object in obj_index
 */
void syn_handle_goal(
    struct syn_handle *h,
    size_t n_goal_obj, size_t *obj_index, size_t *obj_label );

/* Destroy a synergistic planning task-planning handle */
void syn_handle_destroy( struct syn_handle *h);

enum syn_substep {
    SYN_SUBSTEP_PICK,   ///< Compute the initial task plan
    SYN_SUBSTEP_PLACE   ///< Motion planning failed, get a different task plan
};

/* Compute a task plan
 *
 * @param output_plan Plan is stored here in freshly-allocated arrays
 */
void syn_handle_plan( struct syn_handle *h,
                      struct syn_plan *output_plan );

/* Update search weights
 */
void syn_handle_update_weight( struct syn_handle *h,
                               size_t failed_step,
                               enum syn_substep failed_substep );

#ifdef __cplusplus
}
#endif

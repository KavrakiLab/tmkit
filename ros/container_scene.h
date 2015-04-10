#ifndef CONTAINTER_SCENE_H
#define CONTAINTER_SCENE_H

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Publish the scene.
 */
void
tms_container_scene_send( struct container * c );

/**
 * Add a box to the scene.
 */
void
tms_container_scene_add_box( struct container * c, const char *name, const double dim[3],
                             const double quat[4], const double vec[3] );

/**
 * Add a sphere to the scene.
 */
void
tms_container_scene_add_sphere( struct container * c, const char *name, double radius, const double vec[3] );

/**
 * Add a sphere to the scene.
 */
void
tms_container_scene_add_cylinder( struct container * c, const char *name,
                                  double radius, double height,
                                  const double quat[4], const double vec[3] );

/**
 * Remove an item from the scene.
 */
void
tms_container_scene_rm( struct container * c, const char *name );

/**
 * Remove all items from the scene.
 */
void
tms_container_scene_clear( struct container * c );

/**
 * Set object color.
 */
void
tms_container_scene_set_color( struct container * c, const char *name,
                               float r, float g, float b, float a);
#ifdef __cplusplus
}
#endif

#endif

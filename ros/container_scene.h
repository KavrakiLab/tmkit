#ifndef CONTAINTER_SCENE_H
#define CONTAINTER_SCENE_H

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Publish the scene.
 */
void
container_scene_send( struct container * c );

/**
 * Add a box to the scene.
 */
void
container_scene_add_box( struct container * c, const char *name, const double dim[3],
                         const double quat[4], const double vec[3] );

/**
 * Add a sphere to the scene.
 */
void
container_scene_add_sphere( struct container * c, const char *name, double radius, const double vec[3] );

/**
 * Add a sphere to the scene.
 */
void
container_scene_add_cylinder( struct container * c, const char *name,
                              double radius, double height,
                              const double quat[4], const double vec[3] );

/**
 * Remove an item from the scene.
 */
void
container_scene_rm( struct container * c, const char *name );

#ifdef __cplusplus
}
#endif

#endif

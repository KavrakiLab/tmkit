#ifndef CONTAINTER_SCENE_H
#define CONTAINTER_SCENE_H

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Publish the scene.
 */
const char *
container_scene_send( struct container * c );

/**
 * Add a box to the scene.
 */
const char *
container_scene_add_box( struct container * c, const char *name, const double dim[3],
                         const double quat[4], const double vec[3] );

/**
 * Remove an item from the scene.
 */
const char *
container_scene_rm( struct container * c, const char *name );

#ifdef __cplusplus
}
#endif

#endif

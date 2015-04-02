#include <cstdlib>

#include "cros.hpp"
#include "container_scene.h"
#include "moveit_container.hpp"

/**
 * Publish the scene.
 */
const char *
container_scene_send( struct container * c )
{
    moveit_msgs::PlanningScene msg;
    c->planning_scene->getPlanningSceneMsg(msg);
    //c->planning_scene.world.collision_objects.push_back(attached_object.object);
    //c->planning_scene.is_diff = true;
    c->scene_publisher.publish(msg);
}


/**
 * Add a box to the scene.
 */
const char *
container_scene_add_box( struct container * c, const char *name, const double dim[3],
                   const double quat[4], const double vec[3] )
{
    geometry_msgs::Pose pose;
    pose.orientation.x = quat[0];
    pose.orientation.y = quat[1];
    pose.orientation.z = quat[2];
    pose.orientation.w = quat[3];
    pose.position.x = vec[0];
    pose.position.y = vec[1];
    pose.position.z = vec[2];

    /* Define a box to be attached */
    shape_msgs::SolidPrimitive primitive;
    primitive.type = primitive.BOX;
    primitive.dimensions.resize(3);
    std::copy( dim, dim+3, primitive.dimensions.begin() );

    moveit_msgs::CollisionObject msg;
    msg.header.frame_id = c->robot_model->getModelFrame();
    msg.id = name;
    msg.operation = msg.ADD;
    msg.primitives.push_back(primitive);
    msg.primitive_poses.push_back(pose);

    c->planning_scene->processCollisionObjectMsg( msg );
}


/**
 * Remove an item from the scene.
 */
const char *
container_scene_rm( struct container * c, const char *name )
{

}

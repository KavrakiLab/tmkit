#include <cstdlib>

#include "cros.hpp"
#include "container_scene.h"
#include "moveit_container.hpp"
#include <std_msgs/ColorRGBA.h>

/**
 * Publish the scene.
 */
void
tms_container_scene_send( struct container * c )
{
    moveit_msgs::PlanningScene msg;
    c->planning_scene->getPlanningSceneMsg(msg);
    //c->planning_scene.world.collision_objects.push_back(attached_object.object);
    //c->planning_scene.is_diff = true;
    c->scene_publisher.publish(msg);
}

static geometry_msgs::Pose
array2pose( const double quat[4], const double vec[3] )
{
    geometry_msgs::Pose pose;
    pose.orientation.x = quat[0];
    pose.orientation.y = quat[1];
    pose.orientation.z = quat[2];
    pose.orientation.w = quat[3];
    pose.position.x = vec[0];
    pose.position.y = vec[1];
    pose.position.z = vec[2];
    return pose;
}

static void
add_primitive( struct container * c, const char *name,
               shape_msgs::SolidPrimitive &primitive,
               const double quat[4], const double vec[3] )
{
    moveit_msgs::CollisionObject msg;
    msg.header.frame_id = c->robot_model->getModelFrame();
    msg.id = name;
    msg.operation = msg.ADD;
    msg.primitives.push_back(primitive);
    msg.primitive_poses.push_back(array2pose(quat,vec));

    c->planning_scene->processCollisionObjectMsg( msg );
}

/**
 * Add a box to the scene.
 */
void
tms_container_scene_add_box( struct container * c, const char *name, const double dim[3],
                             const double quat[4], const double vec[3] )
{
    shape_msgs::SolidPrimitive primitive;
    primitive.type = primitive.BOX;
    primitive.dimensions.resize(3);
    std::copy( dim, dim+3, primitive.dimensions.begin() );

    add_primitive( c, name, primitive, quat, vec );
}

/**
 * Add a cylinder
 */
void
tms_container_scene_add_cylinder( struct container * c, const char *name,
                                  double radius, double height,
                                  const double quat[4], const double vec[3] )
{
    shape_msgs::SolidPrimitive primitive;
    primitive.type = primitive.CYLINDER;

    primitive.dimensions.resize(2);
    primitive.dimensions[ primitive.CYLINDER_HEIGHT] = height;
    primitive.dimensions[ primitive.CYLINDER_RADIUS] = radius;

    add_primitive( c, name, primitive, quat, vec );
}



void
tms_container_scene_add_sphere( struct container * c, const char *name, double radius, const double vec[3] )
{
    shape_msgs::SolidPrimitive primitive;
    primitive.type = primitive.SPHERE;
    primitive.dimensions.resize(1);
    primitive.dimensions[0] = radius;
    double quat[4] = {0,0,0,1};
    add_primitive( c, name, primitive, quat, vec );
}


/**
 * Remove an item from the scene.
 */
void
tms_container_scene_rm( struct container * c, const char *name )
{

    moveit_msgs::CollisionObject msg;
    msg.id = name;
    msg.operation = msg.REMOVE;
    c->planning_scene->processCollisionObjectMsg( msg );
}

void
tms_container_scene_clear( struct container * c )
{

    c->planning_scene->removeAllCollisionObjects();
}

void
tms_container_scene_set_color( struct container * c, const char *name,
                               float r, float g, float b, float a)
{
    std_msgs::ColorRGBA msg;
    msg.r = r;
    msg.g = g;
    msg.b = b;
    msg.a = a;
    c->planning_scene->setObjectColor( name, msg );
}

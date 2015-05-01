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
    if( c->planning_scene->getCurrentState().hasAttachedBody(name) ) {
        moveit_msgs::AttachedCollisionObject msg;
        msg.object.id = name;
        msg.object.operation = msg.object.REMOVE;
        c->planning_scene->processAttachedCollisionObjectMsg( msg );
    } else {
        moveit_msgs::CollisionObject msg;
        msg.id = name;
        msg.operation = msg.REMOVE;
        c->planning_scene->processCollisionObjectMsg( msg );
    }
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



static void
attach_primitive( struct container * c, const char *parent,
                  const char *name,
                  shape_msgs::SolidPrimitive &primitive,
                  const double quat[4], const double vec[3] )
{
    moveit_msgs::AttachedCollisionObject attached_object;
    attached_object.link_name = parent;
    attached_object.object.header.frame_id = c->planning_scene->getPlanningFrame();
    attached_object.object.id = name;

    attached_object.object.primitives.push_back(primitive);
    attached_object.object.primitive_poses.push_back(array2pose(quat,vec));

    attached_object.object.operation = attached_object.object.ADD;


    c->planning_scene->processAttachedCollisionObjectMsg( attached_object );

    // c->planning_scene->getTransforms();
    // printf("attached id: %s\n"
    //        "  link_name: %s\n"
    //        "   frame_id: %s\n"
    //        "   result:   %d\n",
    //        attached_object.object.id.c_str(),
    //        attached_object.link_name.c_str(),
    //        attached_object.object.header.frame_id.c_str(),
    //        r);
    // robot_state::RobotState state = c->planning_scene->getCurrentState();
    // std::cout << state << std::endl;
    // std::cout << "knows: " << name << " " << c->planning_scene->knowsFrameTransform(name)  << std::endl;
    // std::cout << "has attached: " << name << " " << state.hasAttachedBody(name)  << std::endl;

    // const Eigen::Affine3d &eigen_tf = c->planning_scene->getFrameTransform(name);
    // Eigen::Affine3d::ConstTranslationPart eigen_tf_vec = eigen_tf.translation();
    // printf("vec: %f %f %f\n",
    //        eigen_tf_vec[0],
    //        eigen_tf_vec[1],
    //        eigen_tf_vec[2] );
    // //std::cout << "tf: " << name << " " << eigen_tf  << std::endl;
    // //std::cout << "tf: " << name << " " << eigen_tf  << std::endl;


    // const robot_model::RobotModelConstPtr& model = c->planning_scene->getRobotModel();
    // const std::vector< std::string > &link_names = model->getLinkModelNames();
    // std::cout << "LINKS:" << std::endl;
    // for( auto itr = link_names.begin(); itr != link_names.end(); itr++ )
    //     std::cout << *itr << std::endl;
}


/**
 * Add a box to the scene.
 */
void
tms_container_scene_attach_box( struct container * c, const char *parent,
                                const char *name, const double dim[3],
                                const double quat[4], const double vec[3] )
{
    shape_msgs::SolidPrimitive primitive;
    primitive.type = primitive.BOX;
    primitive.dimensions.resize(3);
    std::copy( dim, dim+3, primitive.dimensions.begin() );

    if( parent ) {
        attach_primitive( c, parent, name, primitive, quat, vec );
    } else {
        add_primitive( c, name, primitive, quat, vec );
    }
}

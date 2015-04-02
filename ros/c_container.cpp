#include <cstdlib>

#include <Eigen/Geometry>
#include <moveit/kinematic_constraints/utils.h>

#include "c_container.h"
#include "moveit_container.hpp"

static void
robot_state_zero( robot_state::RobotState *state )
{
    double *x = state->getVariablePositions();
    size_t n = state->getVariableNames().size();
    memset(x, 0, n * sizeof(x[0]) );
}

struct container *
container_create( const char *name_space, const char *robot_description )
{
    return new container(name_space, robot_description);
}

void
container_destroy( struct container * c)
{
    delete c;
}

size_t
container_variable_count( struct container *c )
{
    return c->robot_model->getVariableCount();
}

int
container_merge_group( struct container *c, const char *group,
                       size_t n_group, const double *q_group,
                       size_t n_all, double *q_all )
{
    if( n_all != container_variable_count(c) ) return -1;

    robot_state::RobotState state(c->robot_model);
    state.setVariablePositions(q_all);
    size_t n_all_model = state.getVariableCount();
    state.setJointGroupPositions(group, q_group);
    memcpy(q_all, state.getVariablePositions(), n_all_model*sizeof(q_all[0]));
}

int
container_set_start( struct container * c, size_t n_all, const double *q_all )
{

    if( n_all != container_variable_count(c) ) return -1;
    robot_state::RobotState start_state(c->robot_model);
    start_state.setVariablePositions(q_all);
    start_state.update(true);

    c->req.start_state.joint_state.name =  start_state.getVariableNames();
    {
        size_t n = c->req.start_state.joint_state.name.size();
        double *p = start_state.getVariablePositions();
        c->req.start_state.joint_state.position.resize( n );
        std::copy ( p, p+n,
                    c->req.start_state.joint_state.position.begin() );
    }

    // // Print stuff
    // {
    //     double r[4],v[3];
    //     container_group_fk( c, group, n, q, r, v );

    //     fprintf(stderr,
    //             "r_start[4] = {%f, %f, %f, %f}\n"
    //             "v_start[3] = {%f, %f, %f}\n",
    //             r[0], r[1], r[2], r[3],
    //             v[0], v[1], v[2] );
    // }
}

int
container_set_group( struct container * c, const char *group )
{
    c->req.group_name = group;
}


int
container_merge_goal_clear( struct container *c )
{
    c->req.goal_constraints.clear();
    return 0;
}

int
container_set_ws_goal( struct container * c, const char *link, const double quat[4], const double vec[3],
                       double tol_x, double tol_angle )
{
    geometry_msgs::PoseStamped stamped_pose;
    stamped_pose.header.frame_id = "base";
    geometry_msgs::Pose &pose = stamped_pose.pose;

    pose.orientation.x = quat[0];
    pose.orientation.y = quat[1];
    pose.orientation.z = quat[2];
    pose.orientation.w = quat[3];
    pose.position.x = vec[0];
    pose.position.y = vec[1];
    pose.position.z = vec[2];


    fprintf(stderr,"constructing pose goal\n");
    moveit_msgs::Constraints pose_goal =
        kinematic_constraints::constructGoalConstraints(link, stamped_pose, tol_x, tol_angle );
    fprintf(stderr,"adding pose goal...\n");
    c->req.goal_constraints.push_back(pose_goal);
    fprintf(stderr,"...added\n");
    return 0;

    // robot_state::RobotState goal_state(c->robot_model);
    // /* Zero positions because somebody's not inititializing their shit */
    // robot_state_zero( &goal_state);

    // const robot_state::JointModelGroup* joint_model_group = goal_state.getJointModelGroup(group);
    // bool got_ik = goal_state.setFromIK(joint_model_group,pose);
    // fprintf(stderr, "IK: %s\n", got_ik ? "yes" : "no" );

    // if( ! got_ik ) return -1;

    // moveit_msgs::Constraints joint_goal = kinematic_constraints::constructGoalConstraints(goal_state,
    //                                                                                       joint_model_group);
    // c->req.goal_constraints.push_back(joint_goal);

    // {
    //     double *x = goal_state.getVariablePositions();
    //     for( size_t i = 0; i < goal_state.getVariableNames().size(); i++ ) {
    //         fprintf(stderr, "goal %lu: %f\n", i, x[i] );
    //     }
    // }

    // {
    //     double r[4],v[3];

    //     container_link_fk( c, container_group_endlink( c, group ),
    //                        goal_state.getVariableNames().size(),
    //                        goal_state.getVariablePositions(),
    //                        r, v );

    //     fprintf(stderr,
    //             "r_goal[4] = {%f, %f, %f, %f}\n"
    //             "v_goal[3] = {%f, %f, %f}\n",
    //             r[0], r[1], r[2], r[3],
    //             v[0], v[1], v[2] );
    // }

}


int
container_plan( struct container * c )
{
    /**********/
    /*  PLAN  */
    /**********/
    moveit_msgs::MoveItErrorCodes err;
    planning_interface::MotionPlanResponse res;
    planning_interface::PlanningContextPtr context =
        c->planner_instance->getPlanningContext(c->planning_scene, c->req, err);
    context->solve(res);
    if(res.error_code_.val != res.error_code_.SUCCESS)
    {
        //TODO: Why is this 0 instead of SUCCESS?
        fprintf(stderr, "Planning failed: %d\n", res.error_code_.val );
        //return 0;
    }


    /************/
    /*  Result  */
    /************/
    moveit_msgs::MotionPlanResponse res_msg;
    res.getMessage(res_msg);
    for( auto itr = res_msg.trajectory.joint_trajectory.points.begin();
         itr != res_msg.trajectory.joint_trajectory.points.end();
         itr++ )
    {
         printf("foo: ");
         for( auto j = itr->positions.begin();
              j != itr->positions.end();
              j++ )
         {
             printf("%f\t", *j );
         }
         printf("\n");
    }

    // /***************/
    // /*  Visualize  */
    // /***************/
    // ros::Publisher display_publisher = node_handle.advertise<moveit_msgs::DisplayTrajectory>("/move_group/display_planned_path", 1, true);
    // moveit_msgs::DisplayTrajectory display_trajectory;

    // ROS_INFO("Visualizing plan 1 (again)");
    // display_trajectory.trajectory_start = res_msg.trajectory_start;
    // display_trajectory.trajectory.push_back(res_msg.trajectory);
    // display_publisher.publish(display_trajectory);
    // /* Sleep to give Rviz time to visualize the plan. */
    // sleep(5.0);
}

const char *
container_group_endlink( struct container * c, const char *group )
{
    robot_state::RobotState state(c->robot_model);
    const robot_state::JointModelGroup* joint_model_group
        = state.getJointModelGroup(group);
    const std::vector<std::string> &link_names = joint_model_group->getLinkModelNames();
    const std::string & end_link =  link_names[ link_names.size()-1];
    return end_link.c_str();
}

int
container_group_fk( struct container * c, const char *group, size_t n, const double *q,
                    double r[4], double v[3]  )
{
    /* Find link for end of group */
    const char *end_link = container_group_endlink(c, group);

    robot_state::RobotState state(c->robot_model);
    /* Zero positions because somebody's not inititializing their shit */
    robot_state_zero(&state);
    const robot_state::JointModelGroup* joint_model_group
        = state.getJointModelGroup(group);

    /* Set state */
    {
        std::vector<double> joint_values(n, 0.0);
        std::copy ( q, q+n, joint_values.begin() );
        state.setJointGroupPositions(joint_model_group, joint_values);
    }

    return container_link_fk( c, end_link,
                              state.getVariableNames().size(),
                              state.getVariablePositions(),
                              r, v );

}


int
container_link_fk( struct container * c, const char *link, size_t n, const double *q,
                   double r[4], double v[3] )
{

    robot_state::RobotState state(c->robot_model);
    // Make robot state
    {
        double *x = state.getVariablePositions();
        size_t n2 = state.getVariableNames().size();
        if( n2 != n ) return -1;
        memcpy( x, q, n*sizeof(x[0]) );
    }

    // get TF
    const Eigen::Affine3d estart_tf = state.getFrameTransform(link);
    {
        const Eigen::Quaternion<double> equat( estart_tf.rotation() );
        r[0] = equat.x();
        r[1] = equat.y();
        r[2] = equat.z();
        r[3] = equat.w();
    }

    {
        const auto e_start = estart_tf.translation();
        v[0] = e_start[0];
        v[1] = e_start[1];
        v[2] = e_start[2];
    }

}

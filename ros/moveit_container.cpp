#include <pluginlib/class_loader.h>
#include <ros/ros.h>
#include <tf_conversions/tf_eigen.h>

#include <moveit/kinematic_constraints/utils.h>
#include <moveit/planning_interface/planning_interface.h>
#include <moveit/robot_model_loader/robot_model_loader.h>
#include <moveit/move_group_interface/move_group.h>
#include <moveit/planning_scene/planning_scene.h>

#include "moveit_container.hpp"

planning_interface::PlannerManagerPtr
load_planner( const std::string &ns,
             robot_model::RobotModelPtr robot_model)
{
    boost::scoped_ptr<pluginlib::ClassLoader<planning_interface::PlannerManager> > planner_plugin_loader;
    planning_interface::PlannerManagerPtr planner_instance;
    std::string planner_plugin_name = "ompl_interface/OMPLPlanner";

    try {
        planner_plugin_loader.reset(new pluginlib::ClassLoader<planning_interface::PlannerManager>("moveit_core", "planning_interface::PlannerManager"));
    } catch(pluginlib::PluginlibException& ex) {
        ROS_FATAL_STREAM("Exception while creating planning plugin loader " << ex.what());
    }

    try {
        planner_instance.reset(planner_plugin_loader->createUnmanagedInstance(planner_plugin_name));
        if (!planner_instance->initialize(robot_model, ns))
            ROS_FATAL_STREAM("Could not initialize planner instance");
        ROS_INFO_STREAM("Using planning interface '" << planner_instance->getDescription() << "'");
    } catch(pluginlib::PluginlibException& ex) {
        const std::vector<std::string> &classes = planner_plugin_loader->getDeclaredClasses();
        std::stringstream ss;
        for (std::size_t i = 0 ; i < classes.size() ; ++i)
            ss << classes[i] << " ";
        ROS_ERROR_STREAM("Exception while loading planner '" << planner_plugin_name << "': " << ex.what() << std::endl
                         << "Available plugins: " << ss.str());
    }

    return planner_instance;
}

container::container ( const std::string &ns, const char *name ) :
    robot_model_loader(name, true),
    robot_model( robot_model_loader.getModel() ),
    planning_scene (new planning_scene::PlanningScene(robot_model)),
    planner_instance( load_planner(ns, robot_model) )
{ }


int
container::set_start( const char *name, size_t n, const double *q )
{

    this->req.group_name = "right_arm";
    robot_state::RobotState start_state(this->robot_model);
    /* Zero positions because somebody's not inititializing their shit */
    {
        double *x = start_state.getVariablePositions();
        for( size_t i = 0; i < start_state.getVariableNames().size(); i++ ) {
            x[i] = 0;
        }
    }

    sensor_msgs::JointState start_joint_state;


    const robot_state::JointModelGroup* joint_model_group = start_state.getJointModelGroup(this->req.group_name);
    {
        std::vector<double> joint_values(n, 0.0);
        std::copy ( q, q+n, joint_values.begin() );
        start_state.setJointGroupPositions(joint_model_group, joint_values);
    }
    this->req.start_state.joint_state.name =  start_state.getVariableNames();
    {
        size_t n = this->req.start_state.joint_state.name.size();
        double *p = start_state.getVariablePositions();
        this->req.start_state.joint_state.position.resize( n );
        std::copy ( p, p+n,
                    this->req.start_state.joint_state.position.begin() );
    }

    // Print stuff
    {
        const std::vector<std::string> &link_names = joint_model_group->getLinkModelNames();
        std::string end_link =  link_names[ link_names.size()-1];
        fprintf(stderr, "Link: %s\n", end_link.c_str() );
        const Eigen::Affine3d estart_tf = start_state.getFrameTransform(end_link);

        tf::Transform start_pose;
        tf::poseEigenToTF(estart_tf, start_pose);
        tf::Quaternion start_q = start_pose.getRotation();
        tf::Vector3 start_v = start_pose.getOrigin();
        fprintf(stderr, "p_start[%lu] = {", n );
        for( size_t i = 0; i < n; i ++ ) {
            fprintf(stderr, "%f%s", q[i], (i+1==n) ? "};\n" : ", " );
        }
        fprintf(stderr,
                "r_start[4] = {%f, %f, %f, %f}\n"
                "v_start[3] = {%f, %f, %f}\n",
                start_q.x(),
                start_q.y(),
                start_q.z(),
                start_q.w(),
                start_v.x(),
                start_v.y(),
                start_v.z() );

    }
}

int container::set_ws_goal( const char *name, const double quat[4], const double vec[3] )
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

    robot_state::RobotState goal_state(this->robot_model);

    /* Zero positions because somebody's not inititializing their shit */
    {
        double *x = goal_state.getVariablePositions();
        for( size_t i = 0; i < goal_state.getVariableNames().size(); i++ ) {
            x[i] = 0;
        }
    }

    const robot_state::JointModelGroup* joint_model_group = goal_state.getJointModelGroup("right_arm");
    bool got_ik = goal_state.setFromIK(joint_model_group,pose);
    fprintf(stderr, "IK: %s\n", got_ik ? "yes" : "no" );

    if( ! got_ik ) return -1;

    moveit_msgs::Constraints joint_goal = kinematic_constraints::constructGoalConstraints(goal_state,
                                                                                          joint_model_group);
    this->req.goal_constraints.clear();
    this->req.goal_constraints.push_back(joint_goal);

    {
        double *x = goal_state.getVariablePositions();
        for( size_t i = 0; i < goal_state.getVariableNames().size(); i++ ) {
            fprintf(stderr, "goal %lu: %f\n", i, x[i] );
        }
    }


}

int container::plan( )
{

    /**********/
    /*  PLAN  */
    /**********/
    moveit_msgs::MoveItErrorCodes err;
    planning_interface::MotionPlanResponse res;
    planning_interface::PlanningContextPtr context =
        this->planner_instance->getPlanningContext(this->planning_scene, this->req, err);
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

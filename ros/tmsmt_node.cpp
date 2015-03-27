/*********************************************************************
 * Software License Agreement (BSD License)
 *
 *  Copyright (c) 2012, Willow Garage, Inc.
 *  All rights reserved.
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above
 *     copyright notice, this list of conditions and the following
 *     disclaimer in the documentation and/or other materials provided
 *     with the distribution.
 *   * Neither the name of Willow Garage nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 *  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 *  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 *  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 *  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 *  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 *  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 *  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 *  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 *  POSSIBILITY OF SUCH DAMAGE.
 *********************************************************************/

/* Author: Sachin Chitta */

#include <pluginlib/class_loader.h>
#include <ros/ros.h>


#include <srdfdom/model.h>
#include <urdf/model.h>

// MoveIt!
#include <moveit/move_group_interface/move_group.h>
#include <moveit/planning_interface/planning_interface.h>
#include <moveit/planning_scene/planning_scene.h>
#include <moveit/kinematic_constraints/utils.h>
#include <moveit_msgs/DisplayTrajectory.h>
#include <moveit_msgs/PlanningScene.h>



int main(int argc, char **argv)
{
    ros::init (argc, argv, "move_group_tutorial");
    // ros::AsyncSpinner spinner(1);
    // spinner.start();
    ros::NodeHandle node_handle("~");

    /********************/
    /* Load Robot Model */
    /********************/
    const std::string srdf_filename =
        "/home/ntd/ros_ws/src/moveit_robots/baxter/baxter_moveit_config/config/baxter.srdf";
    const std::string urdf_filename =
        "/home/ntd/git/mochi/robot/baxter/baxter.urdf";

    boost::shared_ptr<urdf::Model> urdf_model(new urdf::Model);
    if (!(*urdf_model).initFile(urdf_filename)){
        fprintf(stderr, "Failed to parse urdf file");
        return -1;
    }

    boost::shared_ptr<srdf::Model> srdf_model(new srdf::Model);
    if( ! (*srdf_model).initFile(*urdf_model, srdf_filename) ) {
        fprintf(stderr, "Failed to parse srdf file");
        return -1;
    }

    robot_model::RobotModelPtr robot_model(new robot_model::RobotModel(urdf_model, srdf_model));
    planning_scene::PlanningScenePtr planning_scene (new planning_scene::PlanningScene(robot_model));

    /***********************/
    /* Load Planner Plugin */
    /***********************/
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
        if (!planner_instance->initialize(robot_model, node_handle.getNamespace()))
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

    /***********************/
    /* Create Request      */
    /***********************/
    planning_interface::MotionPlanRequest req;
    req.group_name = "right_arm";
    /* Start State */
    {
        robot_state::RobotState start_state(robot_model);
        sensor_msgs::JointState start_joint_state;
        const robot_state::JointModelGroup* joint_model_group = start_state.getJointModelGroup(req.group_name);
        {
            std::vector<double> joint_values(7, 0.0);

            joint_values[0] = -0.5;
            start_state.setJointGroupPositions(joint_model_group, joint_values);
        }
        req.start_state.joint_state.name =  start_state.getVariableNames();
        {
            size_t n = req.start_state.joint_state.name.size();
            double *p = start_state.getVariablePositions();
            req.start_state.joint_state.position.resize( n );
            std::copy ( p, p+n,
                        req.start_state.joint_state.position.begin() );
        }
    }

    /* Goal State */
    robot_state::RobotState goal_state(robot_model);
    const robot_state::JointModelGroup* joint_model_group = goal_state.getJointModelGroup(req.group_name);
    {
        std::vector<double> joint_values(7, 0.0);
        joint_values[0] = 0.5;
        joint_values[3] = 0.5;
        joint_values[5] = 0.5;
        goal_state.setJointGroupPositions(joint_model_group, joint_values);
    }
    moveit_msgs::Constraints joint_goal = kinematic_constraints::constructGoalConstraints(goal_state, joint_model_group);
    req.goal_constraints.clear();
    req.goal_constraints.push_back(joint_goal);

    moveit_msgs::MoveItErrorCodes err;
    planning_interface::MotionPlanResponse res;
    planning_interface::PlanningContextPtr context = planner_instance->getPlanningContext(planning_scene, req, err);
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

    /***************/
    /*  Visualize  */
    /***************/
    ros::Publisher display_publisher = node_handle.advertise<moveit_msgs::DisplayTrajectory>("/move_group/display_planned_path", 1, true);
    moveit_msgs::DisplayTrajectory display_trajectory;

    ROS_INFO("Visualizing plan 1 (again)");
    display_trajectory.trajectory_start = res_msg.trajectory_start;
    display_trajectory.trajectory.push_back(res_msg.trajectory);
    display_publisher.publish(display_trajectory);
    /* Sleep to give Rviz time to visualize the plan. */
    sleep(5.0);

    return 0;
}

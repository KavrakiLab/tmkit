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
#include <tf_conversions/tf_eigen.h>

// MoveIt!
#include <moveit/robot_model_loader/robot_model_loader.h>
#include <moveit/move_group_interface/move_group.h>
#include <moveit/planning_interface/planning_interface.h>
#include <moveit/planning_scene/planning_scene.h>
#include <moveit/kinematic_constraints/utils.h>
#include <moveit_msgs/DisplayTrajectory.h>
#include <moveit_msgs/PlanningScene.h>

#include "moveit_container.hpp"



int main(int argc, char **argv)
{
    ros::init (argc, argv, "move_group_tutorial");
    ros::NodeHandle node_handle("~");
    container cont(node_handle.getNamespace(), "robot_description");


    /***********************/
    /* Create Request      */
    /***********************/
    double q0[7] = {0};
    cont.set_start( "right_arm", 7, q0 );

    /* Joint Goal */

    // robot_state::RobotState goal_state(robot_model);
    // const robot_state::JointModelGroup* joint_model_group = goal_state.getJointModelGroup(req.group_name);
    // {
    //     std::vector<double> joint_values(7, 0.0);
    //     joint_values[0] = 0.5;
    //     joint_values[3] = 0.5;
    //     joint_values[5] = 0.5;
    //     goal_state.setJointGroupPositions(joint_model_group, joint_values);
    // }
    // moveit_msgs::Constraints joint_goal = kinematic_constraints::constructGoalConstraints(goal_state, joint_model_group);
    // req.goal_constraints.clear();
    // req.goal_constraints.push_back(joint_goal);


    /* Workspace Goal */

    double q[4] = {0.423811, 0.566025, -0.423811, 0.566025};
    double v[3] = {0.363087, -1.278295, 0.320976 + .02};
    cont.set_ws_goal("right_arm", q, v );


    /**********/
    /*  PLAN  */
    /**********/
    moveit_msgs::MoveItErrorCodes err;
    planning_interface::MotionPlanResponse res;
    planning_interface::PlanningContextPtr context = cont.planner_instance->getPlanningContext(cont.planning_scene, cont.req, err);
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

    return 0;

}

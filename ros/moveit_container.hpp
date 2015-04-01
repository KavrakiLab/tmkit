#ifndef MOVEIT_CONTAINER_H
#define MOVEIT_CONTAINER_H

#include <moveit/robot_model_loader/robot_model_loader.h>
#include <moveit/move_group_interface/move_group.h>
#include <moveit/planning_interface/planning_interface.h>
#include <moveit/planning_scene/planning_scene.h>

planning_interface::PlannerManagerPtr
load_planner(ros::NodeHandle &node_handle,
             robot_model::RobotModelPtr robot_model);

struct container {
    robot_model_loader::RobotModelLoader robot_model_loader;
    robot_model::RobotModelPtr robot_model;
    planning_scene::PlanningScenePtr planning_scene;
    planning_interface::PlannerManagerPtr planner_instance;
    planning_interface::MotionPlanRequest req;

    container ( const std::string &ns, const char *name );
};

#endif

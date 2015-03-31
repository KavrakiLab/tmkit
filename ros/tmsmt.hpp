#ifndef TMSMT_H
#define TMSMT_H


planning_interface::PlannerManagerPtr
load_planner(ros::NodeHandle &node_handle,
             robot_model::RobotModelPtr robot_model);


#endif /*TMSMT_H*/

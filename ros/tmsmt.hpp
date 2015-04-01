#ifndef TMSMT_H
#define TMSMT_H


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

    int set_start( const char *name, size_t n, const double *q );
    int set_ws_goal( const char *name, const double quat[4], const double vec[3] );
};

#endif /*TMSMT_H*/

#include <cstdlib>
#include <assert.h>
#include "tmsmt.h"


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



// ros::AsyncSpinner spinner(1);
// spinner.start();
static ros::NodeHandle *node_handle = NULL;
static ros::Publisher display_publisher;

TMSMT_API void
tmsmt_ros_init( )
{
    if( NULL == node_handle ) {
        static char name[64];
        strcpy(name, "libtmsmt");
        char *x = name;
        char **y = &x;
        std::string name2="libtmsmt";
        int c=1;
        ros::init (c,y,name2);

        node_handle = new ros::NodeHandle("~");

        display_publisher = node_handle->advertise<moveit_msgs::DisplayTrajectory>("/move_group/display_planned_path", 1, true);
    }
}

static std::string planner_plugin_name = "ompl_interface/OMPLPlanner";

struct tmsmt_model {
    std::string srdf_filename;
    std::string urdf_filename;
    boost::shared_ptr<urdf::Model> urdf_model;
    boost::shared_ptr<srdf::Model> srdf_model;
    robot_model::RobotModelPtr *robot_model;
    planning_scene::PlanningScenePtr *planning_scene;

    planning_interface::MotionPlanRequest req;

    boost::scoped_ptr<pluginlib::ClassLoader<planning_interface::PlannerManager> > planner_plugin_loader;
    planning_interface::PlannerManagerPtr planner_instance;

    tmsmt_model( const char *urdf_filename, const char *srdf_filename ) :
        urdf_filename(urdf_filename),
        srdf_filename(srdf_filename),
        urdf_model(new urdf::Model),
        srdf_model(new srdf::Model)
    {
    }

    ~tmsmt_model() {
        if( robot_model ) delete robot_model;
        if( planning_scene ) delete planning_scene;
    }

    int
    init() {
        /* Load Model */
        if (!(*urdf_model).initFile(urdf_filename)){
            fprintf(stderr, "Failed to parse urdf file");
            return -1;
        }

        if( ! (*srdf_model).initFile(*urdf_model, srdf_filename) ) {
            fprintf(stderr, "Failed to parse srdf file");
            return -1;
        }

        robot_model = new robot_model::RobotModelPtr(new robot_model::RobotModel(urdf_model, srdf_model));
        planning_scene =  new planning_scene::PlanningScenePtr (new planning_scene::PlanningScene(*robot_model));


        /* Load Planner Plugin */
        try {
            planner_plugin_loader.reset(new pluginlib::ClassLoader<planning_interface::PlannerManager>("moveit_core", "planning_interface::PlannerManager"));
        } catch(pluginlib::PluginlibException& ex) {
            fprintf(stderr,"Exception while creating planning plugin loader\n");
            return -1;
        }

        try {
            planner_instance.reset(planner_plugin_loader->createUnmanagedInstance(planner_plugin_name));
            if (!planner_instance->initialize(*robot_model, node_handle->getNamespace()))
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


        return 0;
    }
};

struct tmsmt_model *
tmsmt_model_load( const char *urdf_filename,
                  const char *srdf_filename )
{
    fprintf(stderr, "Loading model\n");
    struct tmsmt_model *p = new tmsmt_model(urdf_filename, srdf_filename);
    if( p->init() ) {
        delete p;
        return NULL;
    }
    return p;
}


void
tmsmt_model_destroy( struct tmsmt_model *p )
{
    fprintf(stderr, "Deleting model\n");
    delete p;
}

int
tmsmt_model_set_start( struct tmsmt_model *p,
                       const char *group,
                       size_t n,
                       double *start )
{
    /* Start */
    {
        robot_state::RobotState start_state(*p->robot_model);
        sensor_msgs::JointState start_joint_state;
        const robot_state::JointModelGroup* joint_model_group = start_state.getJointModelGroup(group);
        {
            std::vector<double> joint_values(n, 0.0);
            std::copy ( start, start+n, joint_values.begin() );

            //joint_values[0] = -0.5;
            start_state.setJointGroupPositions(joint_model_group, joint_values);
        }
        p->req.start_state.joint_state.name =  start_state.getVariableNames();
        {
            size_t num = p->req.start_state.joint_state.name.size();
            double *pos = start_state.getVariablePositions();
            p->req.start_state.joint_state.position.resize( num );
            std::copy ( pos, pos+num,
                        p->req.start_state.joint_state.position.begin() );
        }
        assert( p->req.start_state.joint_state.name.size() == p->req.start_state.joint_state.position.size() );
    }
}


int
tmsmt_model_plan_simple( struct tmsmt_model *p,
                         const char *group,
                         size_t n,
                         double *goal )
{
    p->req.group_name = group;

    /* Goal State */
    robot_state::RobotState goal_state(*p->robot_model);
    const robot_state::JointModelGroup* joint_model_group = goal_state.getJointModelGroup(group);
    {
        std::vector<double> joint_values(n, 0.0);
        std::copy ( goal, goal+n, joint_values.begin() );
        // joint_values[0] = 0.5;
        // joint_values[3] = 0.5;
        // joint_values[5] = 0.5;
        goal_state.setJointGroupPositions(joint_model_group, joint_values);
    }

    //assert( goal_state.joint_state.name.size() == goal_state.joint_state.position.size() );
    moveit_msgs::Constraints joint_goal = kinematic_constraints::constructGoalConstraints(goal_state, joint_model_group);
    p->req.goal_constraints.clear();
    p->req.goal_constraints.push_back(joint_goal);

    moveit_msgs::MoveItErrorCodes err;
    planning_interface::MotionPlanResponse res;
    planning_interface::PlanningContextPtr context =
        p->planner_instance->getPlanningContext(*p->planning_scene, p->req, err);
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


    {
        moveit_msgs::DisplayTrajectory display_trajectory;

        ROS_INFO("Visualizing plan 1 (again)");
        display_trajectory.trajectory_start = res_msg.trajectory_start;
        display_trajectory.trajectory.push_back(res_msg.trajectory);
        display_publisher.publish(display_trajectory);
        //sleep(5);
    }


}

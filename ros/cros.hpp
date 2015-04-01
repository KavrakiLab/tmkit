#ifndef CROS_HPP
#define CROS_HPP

#include "cros.h"
#include <ros/ros.h>

struct cros_node_handle {
    ros::NodeHandle node_handle;
    cros_node_handle( const char *name ) :
        node_handle(name)
        {}
};

#endif

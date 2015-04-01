#include "cros.hpp"
#include <cstring>

void cros_init(int argc, char **argv, const char *name )
{
    ros::init( argc, argv, name );
}

struct cros_node_handle *
cros_node_handle_create( const char *name )
{
    return new cros_node_handle(name);
}

void
cros_node_handle_destroy( struct cros_node_handle * nh)
{
    delete nh;
}

char *
cros_node_handle_get_namespace_dup( struct cros_node_handle * nh)
{
    return strdup( nh->node_handle.getNamespace().c_str() );
}

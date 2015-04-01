#include <cstdlib>
#include "moveit_container.hpp"

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

int
container_set_start( struct container * c, const char *group, size_t n, const double *q )
{
    return c->set_start(group,n,q);
}

int
container_set_ws_goal( struct container * c, const char *name, const double quat[4], const double vec[3] )
{
    return c->set_ws_goal(name, quat,vec);
}

int
container_plan( struct container * c )
{
    return c->plan();
}

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
#include "cros.h"
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#include "c_container.h"


int main(int argc, char **argv)
{
    cros_init (argc, argv, "move_group_tutorial");
    struct cros_node_handle *nh = cros_node_handle_create("~");

    struct container *cont = container_create(nh, "robot_description");

    const char *group = "right_arm";
    const char *link = container_group_endlink(cont, group);

    printf("group: %s\n", group );
    printf("link:  %s\n", link );

    double q0_all[15] = {0};
    double q0_right[7] = {0, -.4*M_PI, 0,
                          .5*M_PI,
                          0, .4*M_PI, 0};
    container_merge_group( cont, group, 7, q0_right, 15, q0_all );

    container_set_start(cont, 15, q0_all );
    container_set_group(cont, group );

    double q[4] = {0.423811, 0.566025, -0.423811, 0.566025};
    double v[3] = {0.363087, -1.278295, 0.320976 + .02};
    container_set_ws_goal(cont, link, q, v, .01, .01 );

    container_plan(cont );
    sleep(5);

    container_destroy(cont);

    return 0;
}

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
#include <unistd.h>
#include <stdio.h>
#include <math.h>
#include <amino.h>

#include "c_container.h"
#include "container_scene.h"


int main(int argc, char **argv)
{
    cros_init (argc, argv, "move_group_tutorial");
    struct cros_node_handle *nh = cros_node_handle_create("~");

    struct container *cont = tms_container_create(nh, "robot_description");

    const char *group = "right_arm";
    const char *link = tms_container_group_endlink(cont, group);

    printf("group: %s\n", group );
    printf("link:  %s\n", link );

    double q0_all[15] = {0};
    double q0_right[7] = {0, -.4*M_PI, 0,
                          .5*M_PI,
                          0, .4*M_PI, 0};

    double r0[4], v0[4];
    tms_container_group_fk( cont, group, 7, q0_right, r0, v0 );

    fprintf(stderr,
            "r_start[4] = {%f, %f, %f, %f}\n"
            "v_start[3] = {%f, %f, %f}\n",
            r0[0], r0[1], r0[2], r0[3],
            v0[0], v0[1], v0[2] );

    //tms_container_merge_group( cont, group, 7, q0_right, 15, q0_all );

    tms_container_set_start(cont, 15, q0_all );
    tms_container_set_group(cont, group );

    // add collision object
    {
        double q[4] = {0,0,0,1};
        {
            //double dim[3] = {.05, .05, 1.5};
            double v[3] = {.5, -.5, 0};
            tms_container_scene_add_cylinder(cont, "a", .01, 1.5, q, v );
        }
        {
            //double dim[3] = {.05, .05, .5};
            double v[3] = {.4, -.4, 0};
            tms_container_scene_add_cylinder(cont, "b", .01, .5, q, v );
        }
        {
            //double dim[3] = {.05, .05, .5};
            double v[3] = {.6, -.6, .3};
            tms_container_scene_add_sphere(cont, "c", .05, v );
        }


        //tms_container_scene_rm(cont, "box1");
    }

    tms_container_scene_send(cont);

    double aa[4] = {0, 1, 0, .5*M_PI };
    double q1[4] = {0, 0, 0, 1 };
    aa_tf_axang2quat(aa,q1);
    //double v1[3] = {0.488372, -0.683374, 0.345540};
    double v1[3] = {0.788372, -0.383374, 0.345540};
    tms_container_set_ws_goal(cont, link, q1, v1, .01, .01 );


    //tms_container_plan(cont );

    tms_container_scene_clear(cont );
    sleep(1);

    tms_container_destroy(cont);

    return 0;
}

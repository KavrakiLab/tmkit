Tutorial {#tutorial}
========

<img src="baxter-sussman.png" style="float:left; margin:0em; margin-right: 3em;"></img>

This tutorial will show you how to use TMSMT for task-motion planning,
demonstrating with the Baxter robot.  You will begin with an example
domain and scene from TMSMT and modify the scene and goal.


[TOC]


<div style="clear: both"></div>

Creating a Planning Scene {#tutorial_run}
=========================

In this tutorial, you will first see how to run the planner on the
demo scene, then modify the scene with different goals and objects.

Prerequisites
-------------

* You are comfortable with a unix shell and text editor.
* You have [installed] (@ref installation) TMSMT.

Setup and Invocation {#tutorial_run_example}
--------------------

1. Obtain the baxter URDF:

   * If you already have an existing ROS installation, you can install
     the `baxter_description` ROS package, for example on ROS Indigo:

            sudo apt-get install ros-indigo-baxter-description
            export ROS_PACKAGE_PATH=/opt/ros/indigo/share

   * An existing ROS installation is not necessary, however, and you
     can install only the baxter URDF and meshes:

            git clone https://github.com/RethinkRobotics/baxter_common
            export ROS_PACKAGE_PATH=`pwd`/baxter_common

   Now, check that you can load the Baxter model.  The following
   command will visualize the Baxter in the [Amino viewer]
   (http://code.golems.org/pkg/amino/viewer.html).  Click and drag the
   mouse and to rotate the view, and zoom with the scroll wheel.
   Close the window the exit.

        aarxc --gui package://baxter_description/urdf/baxter.urdf

2. Copy the example files into a working directory:

        mkdir baxter-blocks
        cp tmsmt/demo/baxter-sussman/*.robray \
           tmsmt/demo/domains/blocksworld/tm-blocks.* \
           baxter-blocks

3. Visualize the initial scene. You should see the Baxter, a table,
   and some blocks.

       cd baxter-blocks
       aarxc --gui package://baxter_description/urdf/baxter.urdf sussman-0.robray

4. Run the [planner command] (@ref planner_command) on the [example problem]
   (https://en.wikipedia.org/wiki/Sussman_Anomaly).

        tmsmt package://baxter_description/urdf/baxter.urdf \
              sussman-0.robray \
              allowed-collision.robray \
              tm-blocks.pddl \
              tm-blocks.py \
              -g sussman-1.robray  \
              -o baxter-sussman.tmp

   The output is [plan file] (@ref planfile) `baxter-sussman.tmp`.

5. Load and view the computed plan:

        tmsmt package://baxter_description/urdf/baxter.urdf \
              sussman-0.robray \
              allowed-collision.robray \
              baxter-sussman.tmp \
              --gui

Changing the goal {#tutorial_run_change_goal}
-----------------

Next, we will change the goal for the task-motion planning problem.

1. Copy and edit the goal scene:

        cp sussman-1.tmp sussman-reversed.robray
        vi sussman-reversed.robray

2. Change the file so that the stacking order is reverse, with block C
   on Block B and Block B on Block A:

        include "class.robray"

        frame block_c {
            parent block_b;
            geometry {
                isa block;
            }
        }

        frame block_b {
            parent block_a;
            geometry {
                isa block;
            }
        }

3. Execute the planner and visualize the plan:

        tmsmt package://baxter_description/urdf/baxter.urdf \
              sussman-0.robray \
              allowed-collision.robray \
              tm-blocks.pddl \
              tm-blocks.py \
              -g sussman-reversed.robray  \
              -o baxter-sussman-reversed.tmp \
              --gui

Changing the scene {#tutorial_run_change_scene}
------------------

Next, we will change the start scene.

1. Copy and edit the start scene:

        cp sussman-0.tmp 4-blocks-goal.robray
        vi 4-blocks-start.robray


2. Add an additional block:

        frame block_d {
            parent block_b;
            translation [0, 0, block_stack];
            geometry {
                isa block;
                color [0,1,1];
            }
        }

3. View the new scene:

        aarxc --gui  package://baxter_description/urdf/baxter.urdf 4-blocks-start.robray


4. Copy and edit the goal scene:

        cp sussman-1.tmp 4-blocks-goal.robray
        vi 4-blocks-start.robray

5. Add the additional block:

        frame block_d {
            parent block_a;
            translation [0, 0, block_stack];
            geometry {
                isa block;
            }
        }

5. Execute the planner

        tmsmt package://baxter_description/urdf/baxter.urdf \
              4-blocks-start.robray \
              allowed-collision.robray \
              tm-blocks.pddl \
              tm-blocks.py \
              -g 4-blocks-goal.robray  \
              -o 4-blocks.tmp \
              --gui

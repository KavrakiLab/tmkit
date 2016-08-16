Tutorial {#tutorial}
========

<img src="baxter-sussman.png" style="float:left; margin:0em; margin-right: 3em;"/>

This tutorial will show you how to use TMSMT for task-motion planning,
demonstrating with the Baxter robot.  You will begin with an example
domain and scene from TMSMT and modify the scene and goal.


[TOC]


<div style="clear: both"></div>

Basic Planner Use {#tutorial_run}
=================

In this tutorial, you will first see how to run the planner on the
demo scene, then modify the scene with different goals and objects.

Prerequisites
-------------

* You are comfortable with a unix shell and text editor.
* You have [installed] (@ref installation) TMSMT.

Setup and Invocation {#tutorial_run_setup}
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
The goal is specified as an Amino
[Scene File](http://code.golems.org/pkg/amino/scenefile.html).

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

Next, we will change both the start and goal scenes, also specified
with as Amino
[Scene Files](http://code.golems.org/pkg/amino/scenefile.html).

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
        vi 4-blocks-goal.robray

5. Add the additional block:

        frame block_d {
            parent block_a;
            translation [0, 0, block_stack];
            geometry {
                isa block;
            }
        }

6. Execute the planner

        tmsmt package://baxter_description/urdf/baxter.urdf \
              4-blocks-start.robray \
              allowed-collision.robray \
              tm-blocks.pddl \
              tm-blocks.py \
              -g 4-blocks-goal.robray  \
              -o 4-blocks.tmp \
              --gui

Extending the Task Domain {#tutorial_task}
=========================

This tutorial demonstrates adding pure task operators.  You will add
operators to enable and disable a safety light.  Then, you will modify
the other preconditions to ensure that the robot only moves with the
safety light on.

Prerequisites
-------------

* You have completed the [setup] (@ref tutorial_run_setup) step from
  the previous tutorial.
* You are familiar with the
  [Planning Domain Definition Language (PDDL)]
  (https://en.wikipedia.org/wiki/Planning_Domain_Definition_Language)

Extend the Operators File {#tutorial_task_ops}
-------------------------

1. Copy the original operators file and edit:

        cp tm-blocks.pddl tm-blocks-light.pddl
        vi tm-blocks-light.pddl

2. Add the following predicate for the safety light:

        (safety-light)

3. Add an operator to turn on the safety light:

        (:action enable-motion
                 :parameters ()
                 :effect (and (safety-light)))

3. Add an operator to turn off the safety light:

        (:action disable-motion
                 :parameters ()
                 :effect (and (not (safety-light))))

4. Require the safety light to be on during motion by adding the
   `(safety-light)` predicate to the precondition of each motion
   action (`pick-up`, `stack`, etc.).



Extend the Goal Condition {#tutorial_task_facts}
-------------------------

1. Create a new facts file with the additional goal condition:

        vi light-goal.pddl

2. Add the following PDDL declarations:

        (define (problem sussman-anomaly)
          (:domain blocks)
          (:goal (not (safety-light))))

Run the planner {#tutorial_task_run}
---------------

    tmsmt package://baxter_description/urdf/baxter.urdf \
          sussman-0.robray \
          allowed-collision.robray \
          tm-blocks-light.pddl \
          light-goal.pddl \
          tm-blocks.py \
          -g baxter-sussman/sussman-1.robray  \
          -o baxter-sussman-light.tmp \
          --gui \


Extending the Task-Motion Domain {#tutorial_task_motion}
================================

**TODO**

This tutorial demonstrates adding new task-motion operators.  You will
add an operator to push a button when the robot finishes its task.


Prerequisites
-------------

* You have completed the [setup] (@ref tutorial_run_setup) step from
  the previous tutorial.
* You are familiar with the
  [Planning Domain Definition Language (PDDL)]
  (https://en.wikipedia.org/wiki/Planning_Domain_Definition_Language)
* You are familiar with the [Python] (@ref https://www.python.org/)
  programming language


Add button geometry
-------------------

Extend the Operators File
-------------------------

Extend the Facts File
---------------------

Extend the Domain Script
----------------------
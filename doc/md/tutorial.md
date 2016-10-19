Tutorial {#tutorial}
========

<img src="baxter-sussman.png" style="float:left; margin:0em; margin-right: 3em;"/>

This tutorial will show you how to use TMSMT for task-motion planning,
by starting by using the [Baxter]
(http://www.rethinkrobotics.com/baxter/) robot to solve the
[Sussman Anomaly] (https://en.wikipedia.org/wiki/Sussman_Anomaly), a
classic example planning problem involving rearranging several blocks.
Then, you will modify the the problem, first by changing the goal
positions of the blocks, next by changing the initial scene, and
finally by addition additional task operators.

[TOC]

<div style="clear: both"></div>

Basic Planner Use {#tutorial_run}
=================

In this tutorial, you will first see how to run the planner on the
demo scene, then modify the scene with different goals and objects.

Prerequisites {#tutorial_run_pre}
-------------

* You are comfortable with a unix shell and text editor.
* You have [installed] (@ref installation) TMSMT.

Setup and Invocation {#tutorial_run_setup}
--------------------

1. Obtain the baxter URDF, which describes the kinematics and geometry
   (meshes) of the robot.

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
        cp tmkit/demo/baxter-sussman/*.robray \
           tmkit/demo/baxter-sussman/q0.tmp \
           tmkit/demo/domains/blocksworld/tm-blocks.* \
           baxter-blocks

3. Visualize the initial scene, defined by the Baxter URDF and example
   scene (*.robray) files. You should see the Baxter, a table, and
   some blocks.

       cd baxter-blocks
       aarxc --gui package://baxter_description/urdf/baxter.urdf sussman-0.robray

4. Run the [planner command] (@ref planner_command) on the [example problem]
   (https://en.wikipedia.org/wiki/Sussman_Anomaly).

        tmsmt package://baxter_description/urdf/baxter.urdf \
              sussman-0.robray \
              allowed-collision.robray \
              tm-blocks.pddl \
              tm-blocks.py \
              -q q0.tmp \
              -g sussman-1.robray  \
              -o baxter-sussman.tmp

   This commands takes a number of inputs and options:
     - `package://baxter_description/urdf/baxter.urdf`: A scene
       description (for the robot) for the start scene in URDF format
     - `sussman-0.robray`: a scene description for the start scene in
       scene file format
     - `allowed-collision.robray`: an additional scene description
       contained the allowable collisions
     - `tm-blocks.pddl`: The task operators file
     - `tm-blocks.py`: The domain somantics file
     - `-q q0.tmp`: The initial configuration
     - `-g sussman-1.robray`: The goal scene
     - `-o baxter-sussman.tmp`: The output file [plan file] (@ref planfile)

5. Load and view the computed plan:

        tmsmt package://baxter_description/urdf/baxter.urdf \
              sussman-0.robray \
              allowed-collision.robray \
              baxter-sussman.tmp \
              --gui

   This command takes as parameters the initial scene (`*.urdf` and
   `*.robray` files) along with the previously computed plan file
   `baxter-sussman.tmp`.  The `--gui` option will display the plan in
   a 3D visualization.

Changing the goal {#tutorial_run_change_goal}
-----------------

Next, we will change the goal for the task-motion planning problem.
The goal is specified as an Amino
[Scene File](http://code.golems.org/pkg/amino/scenefile.html).

1. Copy and edit the goal scene:

        cp sussman-1.robray sussman-reversed.robray
        vi sussman-reversed.robray

2. Change the file so that the stacking order is reversed, with block C
   on Block B and Block B on Block A:

        /* include common definitions for blocks */
        include "class.robray"

        /* the kinematic frame for block "C" */
        frame block_c {
            parent block_b;  // the parent from of block_c is block_b
            geometry {
                isa block; // geometry class for blocks
            }
        }

        /* the kinematic frame for block "B" */
        frame block_b {
            parent block_a;  // the parent frame of block_b is block_a
            geometry {
                isa block; // geometry class for blocks
            }
        }

3. Re-execute the planner and visualize the plan:

        tmsmt package://baxter_description/urdf/baxter.urdf \
              sussman-0.robray \
              allowed-collision.robray \
              tm-blocks.pddl \
              tm-blocks.py \
              -q q0.tmp \
              -g sussman-reversed.robray  \
              -o baxter-sussman-reversed.tmp \
              --gui

Changing the scene {#tutorial_run_change_scene}
------------------

Next, we will change both the start and goal scenes, also specified
with as Amino
[Scene Files](http://code.golems.org/pkg/amino/scenefile.html).

1. Copy and edit the start scene:

        cp sussman-0.robray 4-blocks-start.robray
        vi 4-blocks-start.robray


2. Add an additional block:

        /* the kinematic frame for block "D" */
        frame block_d {
            parent block_b; // block_d is initially on block_b
            /* set the height of block_d above block_b */
            translation [0, 0, block_stack];
            geometry {
                isa block;
                color [0,1,1]; // block_d is cyan
            }
        }

3. View the new scene:

        aarxc --gui  package://baxter_description/urdf/baxter.urdf 4-blocks-start.robray

4. Copy and edit the goal scene:

        cp sussman-1.tmp 4-blocks-goal.robray
        vi 4-blocks-goal.robray

5. Add the additional block:

        frame block_d {
            parent block_a; // block "D" is stacked on block "A"
            /* set the relative height of block "D" */
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
              -q q0.tmp \
              -g 4-blocks-goal.robray  \
              -o 4-blocks.tmp \
              --gui

Extending the Task Domain {#tutorial_task}
=========================

This tutorial demonstrates adding pure task operators.  You will add
operators to enable and disable a safety light.  Then, you will modify
the other preconditions to ensure that the robot only moves with the
safety light on.

Prerequisites {#tutorial_task_pre}
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
          -q q0.tmp \
          -g baxter-sussman/sussman-1.robray  \
          -o baxter-sussman-light.tmp \
          --gui \


Extending the Task-Motion Domain {#tutorial_task_motion}
================================

This tutorial demonstrates adding new task-motion operators.  You will
add an operator to push a button when the robot finishes its task.  In
addition to creating the PDDL operator defintion as in the previous
tutorial, you will also define the *semantics* of the operator: how to
compute a motion plan for the operator.  These domain semantics are
defined as Python functions.


Prerequisites {#tutorial_task_motion_pre}
-------------

* You have completed the [setup] (@ref tutorial_run_setup) step from
  the previous tutorial.
* You are familiar with the
  [Planning Domain Definition Language (PDDL)]
  (https://en.wikipedia.org/wiki/Planning_Domain_Definition_Language)
* You are familiar with the [Python] (https://www.python.org/)
  programming language


Add button geometry {#tutorial_task_motion_geom}
-------------------

Create the additional frames and geometry for the button that the
robot will push.

1. Copy and edit the start scene:

        cp sussman-0.robray sussman-extend.robray
        vi sussman-extend.robray

2. Add the button geometry to `sussman-extend.robray`:

        def button_height .05;

        frame button_base {
            parent front_table;
            translation [-.3, -.3, button_height/2];
            geometry {
                shape box;
                dimension [.1, .1, button_height];
                color [.5, .5, .5];
            }
        }

        frame button {
            parent button_base;
            translation [0, 0, button_height/2];
            geometry {
                shape cylinder;
                radius .025;
                height .03;
                color [1, 0, 0 ];
            }
        }


Extend the Operators File {#tutorial_task_motion_ops}
-------------------------

Modify the operators file with an additional operator to push the
button and a predicate indicating button state.

1. Copy and edit the operators file:

        cp tm-blocks.pddl tm-blocks-extend.pddl
        vi tm-blocks-extend.pddl

2. Add an additional predicate `(running)`.

3. For each action, add `(running)` to the set of preconditions.

4. Add an additional action to push the button:

        (:action push-button
                  :parameters ()
                  :precondition (and (handempty) (running))
                  :effect (and (not (running))))


Add an Additional Facts File {#tutorial_task_motion_facts}
----------------------------

Add additional start state and goal conditions for the button.

1. Edit a new facts file:

        vi extended-facts.pddl

2. Set the start and goal as follows:

        (define (problem itmp) (:domain blocks)

         ;; Start: running is true
         (:init (running))

         ;; Goal: running is false
         (:goal (not (running))))

Extend the Domain Semantics {#tutorial_task_motion_script}
---------------------------

Create the refinement function for the `push-button` action.

1. Copy and edit the domain semantics:

        cp tm-blocks.py tm-blocks-extend.py
        vi tm-blocks-extend.py

2. Create a new refinement function:

        def op_push_button(scene, config, op):
            # wrap start scene and configuration
            nop = tm.op_nop(scene,config)
            # compute the workspace goal, i.e., the button'spose
            ws_goal = tm.op_tf_abs(nop,"button")
            # compute a motion plan to push the button
            return motion_plan(nop, FRAME, tm.op_tf_abs(nop,"button"))

3. Bind the refinement function

        # Bind the refinement function for the PUSH-Button operator
        tm.bind_refine_operator(op_push_button, "PUSH-BUTTON")

Run the Planner {#tutorial_task_motion_run}
---------------

    tmsmt package://baxter_description/urdf/baxter.urdf \
           sussman-extend-0.robray \
           allowed-collision.robray \
           tm-blocks-extend.pddl \
           extended-facts.pddl \
           tm-blocks-extend.py \
           -q q0.tmp \
           -g sussman-1.robray  \
           -o baxter-sussman-extend.tmp \
           --gui

The Planner Command {#planner_command}
===================

This package provides a shell command to invoke the task-motion
planner.

[TOC]

Input and Output {#planner_command_io}
================

Start and Goal Scenes
---------------------

* Start and goal scenes may be specified as Amino
  [Scene Files](http://code.golems.org/pkg/amino/scenefile.html) or as
  ROS [URDF](http://wiki.ros.org/urdf).
* The start scene includes the robot and all object in the
  environment.
* The goal scene defines target locations for (usually a subset of)
  environment objects.

Task Domain
-----------

* The task domain is specified in the
  [Planning Domain Definition Language (PDDL)](https://en.wikipedia.org/wiki/Planning_Domain_Definition_Language).
* Task facts -- PDDL Objects, start state, goal state, etc. -- are
  inferred from the start and goal scenes.

Task-Motion Map Scripts
-----------------------

* The domain-specific mapping from scenes to task state and task
  operators to motion planning problems is specified via functions
  defined in user-provided script files

* Scripts may be written in [Python]
  (https://common-lisp.net/project/clpython/) or [Common Lisp]
  (http://www.gigamonkeys.com/book/).  Note, however, that Python
  scripts cannot use extension modules.

Plan Files
----------

* Plans are recorded in as TMSMT [Plan Files](@ref planfile).

Option Summary {#planner_command_options}
==============

    Usage: tmsmt [OPTIONS]

    Options:

    -s SCENE_FILE
        Start scene file

    -g SCENE_FILE
        Goal scene file

    -d TASK_DOMAIN_FILE
        Task Domain (PDDL) file

    -l SCRIPT_FILE
        Load Script File

    -o OUTPUT_PLAN_FILE
        Output plan file

    --load-plan=PLAN_FILE
        Load plan from file

    -r RESOLUTION
        Discretization resolution

    -m MAX_STEPS
        Maximum number of task steps

    --gui
        Enable graphical interface

    -v
        Verbose output


Examples {#planner_command_examples}
========

When loading scenes from URDF, it is necessary to set the
`ROS_PACKAGE_PATH` environment variable (because URDF references files
via ROS packages).

    export ROS_PACKAGE_PATH=/opt/ros/indigo/share

The following command will compute a task-motion plan for the Baxter
robot and output the plan to `baxter-sussman.tmp`.

    tmsmt -s 'package://baxter_description/urdf/baxter.urdf' \
          -s sussman-0.robray \
          -s allowed-collision.robray \
          -g sussman-1.robray  \
          -d domain.pddl \
          -o baxter-sussman.tmp


The following command will load and visualize the previously computed
task-motion plan from the file `baxter-sussman.tmp`.

    tmsmt -s 'package://baxter_description/urdf/baxter.urdf' \
          -s sussman-0.robray \
          -s allowed-collision.robray \
          -i baxter-sussman.tmp

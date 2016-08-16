The Planner Command {#planner_command}
===================

This package provides a shell command to invoke the task-motion
planner.

[TOC]

Input and Output {#planner_command_io}
================

Start and Goal Scenes {#planner_command_io_scenes}
---------------------

* Start and goal scenes may be specified as Amino
  [Scene Files](http://code.golems.org/pkg/amino/scenefile.html) or as
  ROS [URDF](http://wiki.ros.org/urdf).
* The start scene includes the robot and all object in the
  environment.
* The goal scene defines target locations for (usually a subset of)
  environment objects.

Task Domain {#planner_command_io_task}
-----------

* The task domain is specified in the
  [Planning Domain Definition Language (PDDL)](https://en.wikipedia.org/wiki/Planning_Domain_Definition_Language).
* Task facts -- PDDL Objects, start state, goal state, etc. -- are
  inferred from the start and goal scenes.

Domain Scripts {#planner_command_io_scripts}
--------------

* The domain-specific mapping from scenes to task state and task
  operators to motion planning problems is specified via functions
  defined in user-provided [domain script] (@ref domain_script) files

* Scripts may be written in [Python]
  (https://common-lisp.net/project/clpython/) or [Common Lisp]
  (http://www.gigamonkeys.com/book/).  Note, however, that Python
  scripts cannot use extension modules.

@sa @ref tmsmtpy

Plan Files {#planner_command_io_planfile}
----------

* Plans are recorded in as TMSMT in a plain-text, line-based format.

@sa @ref planfile


Examples {#planner_command_examples}
========

The `demo` directory in the source distribution provides several
example domains and use cases for the planner command.  A few of these
cases are described in detail here.

Pure Task Planning
------------------

When given only the task domain and facts, the planner command will
compute a pure task plan.  Using the blocksworld domain included in
the source distribution, call the planner as:

    tmsmt -d demo/domains/blocksworld/blocks-domain.pddl \
          -f demo/domains/blocksworld/sussman-anomaly.pddl

Task-Motion Planning
--------------------

When loading scenes from URDF, it is necessary to set the
`ROS_PACKAGE_PATH` environment variable because URDF external files
such as meshes via ROS packages.

    # Assuming you have install ROS indigo under /opt
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


Options Summary {#planner_command_man}
===============

@sa [Man Page] (man_tmsmt.html)

@htmlonly
<iframe src="man_tmsmt.html"
        height="800"
        width="100%"
        >

</iframe>
@endhtmlonly

#!/bin/sh

## Compute a task-motion plan to solve the sussman anomaly with a
## Rethink Baxter robot.


export ROS_PACKAGE_PATH=/opt/ros/indigo/share
export PATH="..:$PATH"

tmsmt -s 'package://baxter_description/urdf/baxter.urdf' \
      -s baxter-sussman/sussman-0.robray \
      -s baxter-sussman/allowed-collision.robray \
      -g baxter-sussman/sussman-1.robray  \
      -d domains/blocksworld/tm-blocks.pddl \
      -l domains/blocksworld/tm-blocks.py \
      -o baxter-sussman.tmp \
      --gui \
      --write-facts=baxter-sussman.pddl \
      --verbose

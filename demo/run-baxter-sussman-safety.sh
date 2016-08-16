#!/bin/sh

## Compute a task-motion plan to solve the sussman anomaly with a
## Rethink Baxter robot.

# Maybe set ROS_PACKAGE_PATH
if [ -z "$ROS_PACKAGE_PATH" ]; then
   export ROS_PACKAGE_PATH=/opt/ros/indigo/share
fi

export PATH="..:$PATH"

tmsmt package://baxter_description/urdf/baxter.urdf \
      baxter-sussman/sussman-0.robray \
      baxter-sussman/allowed-collision.robray \
      domains/blocksworld/tm-blocks-safety.pddl \
      domains/blocksworld/tm-blocks.py \
      -g baxter-sussman/sussman-1.robray  \
      -o baxter-sussman-safety.tmp \
      --gui \
      --write-facts=baxter-sussman.pddl \
      --verbose

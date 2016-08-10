#!/bin/sh

export ROS_PACKAGE_PATH=/opt/ros/indigo/share

export PATH="..:$PATH"


exec tmsmt -s 'package://baxter_description/urdf/baxter.urdf' \
           -s baxter-sussman/sussman-0.robray \
           -s baxter-sussman/allowed-collision.robray \
           -g baxter-sussman/sussman-1.robray  \
           -d domains/linear-blocksworld/linear-blocksworld.pddl \
           -l domains/linear-blocksworld/linear-blocksworld.py \
           -o baxter-sussman-linear.tmp \
           --gui \
           --verbose

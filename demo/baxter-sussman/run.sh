#!/bin/sh

export ROS_PACKAGE_PATH=/opt/ros/indigo/share

export PATH="../..:$PATH"


exec tmsmt -s 'package://baxter_description/urdf/baxter.urdf' \
           -s sussman-0.robray \
           -s allowed-collision.robray \
           -l tm-map.py \
           -g sussman-1.robray  \
           -d domain.pddl \
           -o baxter-sussman.tmp \
           --write-facts=start-facts.pddl \
           --gui \
           --verbose

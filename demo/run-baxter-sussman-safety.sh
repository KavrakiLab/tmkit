#!/bin/sh

## Compute a task-motion plan to solve the sussman anomaly with a
## Rethink Baxter robot.

. ./demo-path.sh

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

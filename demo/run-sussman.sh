#!/bin/sh

## Compute the task plan for the sussman anomaly

. ./demo-path.sh

tmsmt domains/blocksworld/tm-blocks.pddl \
      domains/blocksworld/tm-sussman.pddl

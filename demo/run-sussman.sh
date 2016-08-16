#!/bin/sh

## Compute the task plan for the sussman anomaly

. ./demo-path.sh

tmsmt -d domains/blocksworld/tm-blocks.pddl\
      -f domains/blocksworld/tm-sussman.pddl

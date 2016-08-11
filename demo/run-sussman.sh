#!/bin/sh

## Compute the task plan for the sussman anomaly

PATH=..:$PATH

tmsmt -d domains/blocksworld/tm-blocks.pddl\
      -f domains/blocksworld/tm-sussman.pddl

#!/bin/sh

## Compute the task plan for the sussman anomaly

PATH=..:$PATH

tmsmt -d domains/blocksworld/blocks-domain.pddl \
      -f domains/blocksworld/sussman-anomaly.pddl

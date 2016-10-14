#!/bin/sh -e

for DOCKERFILE in $@; do
      docker build -t "tmkit:$DOCKERFILE-dep" -f "script/docker/$DOCKERFILE" .;
done

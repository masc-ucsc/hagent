#!/bin/bash

rm -f *.log
rm -f *.yaml
rm -rf equiv_check_* chisel2v_*
rm -f tmp_*txt
rm -rf output

if [ -n "$(docker ps -qa)" ]; then
  docker kill $(docker ps -qa)
fi
if [ -n "$(docker ps -qa)" ]; then
  docker stop $(docker ps -qa)
fi
if [ -n "$(docker ps -qa)" ]; then
  docker rm $(docker ps -qa)
fi
docker container prune -f
docker image prune -a -f

#!/bin/bash

rm -f *.log
rm -f *.yaml
rm -rf equiv_check_* chisel2v_*
rm -f tmp_*txt
rm -rf output

docker kill $(docker ps -q)
docker container prune -f
docker image prune -a -f

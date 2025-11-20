# Docker and HAgent

Multiple tools use docker, HAgent also benefits from docker because it allows to have a 'container' for the agent interactions. This allows to increase security (agent going crazy) but also to help detect edits/changes from HAgent.

This document containts some docker setup examples for HAgent related projects.


## Build Hagent-client docker


Command line that mounts a local cache (allows to reuse data across docker runs), and mounting the tech dir for synthesis


```bash
cd HAGENT_REPO
docker run --rm -it -v ~/tmp/cache:/code/workspace/cache -v$HAGENT_TECH_DIR:/code/workspace/tech -v.:/code/hagent  mascucsc/hagent-simplechisel:2025.11
```


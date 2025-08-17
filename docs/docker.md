# Docker and HAgent

Multiple tools use docker, HAgent also benefits from docker because it allows to have a 'container' for the agent interactions. This allows to increase security (agent going crazy) but also to help detect edits/changes from HAgent.

This document containts some docker setup examples for HAgent related projects.


## Build Hagent-client docker


## Run latest

```bash
docker run -it mascucsc/hagent-builder:2025.05 bash
```

## Chipyard

Chipyard deprecated their docker, so we need to create a new one. It is quite similar to the original, but the "chipyard" repository is NOT inside the docker. Just the build tools. This allows to track the edited files.

1-Get Chipyard repo:
```bash
git clone https://github.com/ucb-bar/chipyard.git
cd chipyard
# Get a stable chipyard version (last tested 1.13.0)
git checkout 1.13.0
```


2-Use the HAgent docker (allows chipyard and yosys)


```bash
# May require sudo dependent on your setup/permissions
docker pull ucbbar/chipyard-image
```


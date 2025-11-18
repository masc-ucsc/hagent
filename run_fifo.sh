 export HAGENT_REPO_DIR=$HOME/Divya/ProjectSVA/Fall2025/hagent
 export HAGENT_BUILD_DIR=$HOME/Divya/ProjectSVA/Fall2025/hagent/build
 export HAGENT_CACHE_DIR=$HOME/Divya/ProjectSVA/Fall2025/hagent/cache


export PYTHONPATH=$PYTHONPATH:/soe/dkohli1/Divya/ProjectSVA/Fall2025/hagent-private
#export PYTHONPATH=$PYTHONPATH:/soe/dkohli1/Divya/ProjectSVA/Fall2025/

uv run python3 hagent/tool/cli_formal.py   --slang /mada/users/dkohli1/Divya/ProjectSVA/Spring2025/spec_gen/build/build/slang/build/bin/slang   --rtl ~/Divya/ProjectSVA/Summer2025/Demo/fifo/src   --top Sync_FIFO   --out ~/Divya/ProjectSVA/Summer2025/out   --run-jg   --jasper-bin /mada/software/cadence/JASPER24/bin/jg

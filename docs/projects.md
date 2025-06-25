
# Popular Open Source projects

## Setup Docker

### OS X

```
brew install docker
brew install colima
colima start --vm-type=vz --vz-rosetta
# brew services start colima
```

To test it:
```
docker pull docker/welcome-to-docker
docker run -d -p 8080:80 docker/welcome-to-docker
```

To check the running docker and connect:
```
docker ps
docker exec -it <DOCKER_NUMBER>
```

To cleanup:
```
docker kill <DOCKER_NUMBER>
```


## XiangShan


Clone XiangShan parallel to hagent or another directory (not inside hagent)


```
git clone --recursive git@github.com:OpenXiangShan/XiangShan.git
```


Enable firrtool to dump source locators to help HAgent:

```
diff --git a/Makefile b/Makefile
index 6fb956621..973303cd8 100644
--- a/Makefile
+++ b/Makefile
@@ -78,7 +78,7 @@ MILL_BUILD_ARGS = -Djvm-xmx=$(JVM_XMX) -Djvm-xss=$(JVM_XSS)
 FPGA_MEM_ARGS = --firtool-opt "--repl-seq-mem --repl-seq-mem-file=$(TOP).$(RTL_SUFFIX).conf"
 SIM_MEM_ARGS = --firtool-opt "--repl-seq-mem --repl-seq-mem-file=$(SIM_TOP).$(RTL_SUFFIX).conf"
 MFC_ARGS = --dump-fir --target $(CHISEL_TARGET) --split-verilog \
-           --firtool-opt "-O=release --disable-annotation-unknown --lowering-options=explicitBitcast,disallowLocalVariables,disallowPortDeclSharing,locationInfoStyle=none"
+           --firtool-opt "-O=release --disable-annotation-unknown --lowering-options=explicitBitcast,disallowLocalVariables,disallowPortDeclSharing"

 # prefix of XSTop or XSNoCTop
 ifneq ($(XSTOP_PREFIX),)
```


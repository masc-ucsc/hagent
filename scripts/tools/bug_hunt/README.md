# HAgent - Bug Hunt

### Usage

#### Build:

`make all`


#### Run (required variables):

```
make run PASS_VCDS="./build/pass1.vcd ./build/pass2.vcd" \
          FAIL_VCD="./build/fail.vcd" \
          OUT="anomalies.txt" \
          WINDOW_EVENTS=2000 \
          TOPK=200 \
          DIVERSITY="--no_diversity"
```


#### Clean:

`make clean`

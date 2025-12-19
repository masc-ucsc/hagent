# Invariance Detect

## Overview

This tool analyzes **PASS** and **FAIL** VCD waveforms and ranks signals that are most likely involved in a bug.

Instead of comparing traces cycle-by-cycle, it:

* summarizes signal behavior over **windows**
* learns what behavior is **normal** from PASS runs
* flags signals whose FAIL behavior **violates that envelope**

The output is:

* a **ranked list of suspicious signals**
* optional **clusters** showing related signals (cause → effect)

## Architecture

                ┌─────────────────────────┐
                │        PASS VCDs         │
                │  (pass1.vcd, pass2.vcd) │
                └────────────┬────────────┘
                             │
                             ▼
                   ┌──────────────────┐
                   │    VcdStream     │
                   │ (event parsing)  │
                   └────────┬─────────┘
                            │
                            ▼
                 ┌──────────────────────┐
                 │   WindowManager      │
                 │ (EVENT / TIME / RET) │
                 └────────┬─────────────┘
                            │
                            ▼
              ┌────────────────────────────┐
              │   SigWindowFeat (per win)   │
              │  - seen1 / seen0            │
              │  - toggles                  │
              │  - transition stats         │
              │  - window signature         │
              └────────┬───────────────────┘
                            │ rotate
                            ▼
              ┌────────────────────────────┐
              │   SigAgg (PASS model)       │
              │  - stable masks             │
              │  - entropy / diversity      │
              │  - signature set            │
              └────────────────────────────┘


                ┌─────────────────────────┐
                │        FAIL VCDs         │
                │        (fail.vcd)        │
                └────────────┬────────────┘
                             │
                             ▼
              (same pipeline as PASS, built independently)
                             │
                             ▼
              ┌────────────────────────────┐
              │   SigAgg (FAIL model)       │
              └────────────────────────────┘


        ┌──────────────────────────────────────────┐
        │              Scorer                      │
        │                                          │
        │  PASS vs FAIL per signal:                │
        │   - Static Bit Novelty (bitNovel)        │
        │   - Behavioral Novelty (sigNovel)        │
        │   - Transition / timing differences      │
        │                                          │
        └───────────────┬──────────────────────────┘
                        │
                        ▼
        ┌──────────────────────────────────────────┐
        │          Ranked Anomalies                 │
        │   (mscratch, rdata, wdata, …)             │
        └───────────────┬──────────────────────────┘
                        │
                        ▼
        ┌──────────────────────────────────────────┐
        │           CausalGraph (optional)          │
        │   - dynamic co-activity edges             │
        │   - static↔dynamic bridges                │
        │   - cluster extraction                    │
        └──────────────────────────────────────────┘


---

## Input / Output

### Input

* One or more **PASS VCDs**
* One or more **FAIL VCDs**

### Output

* Ranked signals with scores
* (Optional) clusters of related signals

---

## How it works (simple, end-to-end)

### 1. Read VCD values

The VCD is treated as a stream of events:

```
time → signal name → value
```

No RTL knowledge is used — only value changes.

---

### 2. Windowing

The stream is split into **windows** (e.g., every N events or every T time units).

Each window is processed independently.

Purpose:

* reduce noise
* summarize behavior instead of raw cycles

---

### 3. Per-window signal summary

For each signal inside a window, the tool records:

* **seen1**: which bit positions were ever `1`
* **seen0**: which bit positions were ever `0`
* **toggles**: did the signal change value
* **transition counts**: how values changed
* **window signature**: a compact ID summarizing this window’s behavior

This is purely mechanical bookkeeping.

---

### 4. Aggregate across windows

Across all windows of a run, for each signal:

* **stable0_mask**: bits that were never `1`
* **stable1_mask**: bits that were never `0`
* **signature set**: all window signatures seen

PASS runs and FAIL runs are aggregated **separately**.

---

### 5. PASS vs FAIL comparison (bug detection)

For each signal:

#### a) Static Bit Novelty (`bitNovel`)

Checks:

> Did FAIL set bit positions that PASS never set?

This catches:

* stuck-at bugs
* unexpected high bits
* corrupted state

---

#### b) Behavioral Novelty (`sigNovel`)

Checks:

> Did FAIL exhibit per-window behaviors never seen in PASS?

This catches:

* control bugs
* timing/order differences
* logic path changes even when values look legal

---

### 6. Scoring and ranking

Each signal gets a score combining:

* bitNovel (new bit usage)
* sigNovel (new behavior)
* small activity/transition terms

Signals are **sorted by score**.

Higher score = more suspicious.

---

### 7. Optional clustering

Signals that frequently change together in FAIL are grouped.

This helps explain:

* propagation paths
* root cause vs downstream effects

---

## How to build

From the project root:

```bash
g++ -O2 -std=c++17 \
    main.cpp \
    -o invariance_detect
```

(Adjust include paths if needed.)

---

## How to run

### Basic usage

```bash
./invariance_detect \
  --pass_vcd pass1.vcd \
  --pass_vcd pass2.vcd \
  --fail_vcd fail.vcd
```

### With window size (recommended)

```bash
./invariance_detect \
  --pass_vcd pass1.vcd \
  --pass_vcd pass2.vcd \
  --fail_vcd fail.vcd \
  --window_events 50000
```

### Enable clustering and limit output

```bash
./invariance_detect \
  --pass_vcd pass1.vcd \
  --fail_vcd fail.vcd \
  --window_events 50000 \
  --enable_cluster \
  --topk 50
```

### Write output to a file

```bash
./invariance_detect \
  --pass_vcd pass1.vcd \
  --fail_vcd fail.vcd \
  --out result.txt
```

---

## Output format (example)

```
=== Per-Net Anomalies ===
mscratch        87.43
rdata           84.31
wdata           84.31
buggy_wdata     81.19

=== Causal Clusters ===
Cluster 0:
  mscratch
  buggy_wdata
  wdata
  rdata
```



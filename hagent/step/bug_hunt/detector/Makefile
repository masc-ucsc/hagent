CXX      ?= g++
CXXFLAGS ?= -std=c++17 -O2 -pipe -I.
LDFLAGS  ?=

SRCS := main.cpp scorer.cpp utils.cpp vcd_stream.cpp
OBJS := $(SRCS:%.cpp=build/%.o)
TARGET := build/invariance_detect

DEFAULT_OUT := $(shell { dir="build"; base="anomalies"; ext=".txt"; file="$$dir/$$base$$ext"; i=0; while [ -e "$$file" ]; do i=$$((i+1)); file="$$dir/$${base}_$${i}$$ext"; done; printf '%s\n' "$$file"; } | tail -n 1)
WINDOW_EVENTS ?= 2000
TOPK ?= 200
NO_DIVERSITY ?= 1
RUN_ARGS ?=
RUN_ARGS := $(if $(strip $(run_args)),$(strip $(run_args)),$(RUN_ARGS))

OUT_FILE := $(if $(strip $(out)),$(strip $(out)),$(DEFAULT_OUT))
WINDOW_EVENTS_VALUE := $(if $(strip $(window_events)),$(strip $(window_events)),$(WINDOW_EVENTS))
TOPK_VALUE := $(if $(strip $(topk)),$(strip $(topk)),$(TOPK))

PASS_ARGS := $(strip $(foreach f,$(pass_vcd),--pass_vcd $(f)))
FAIL_ARGS := $(strip $(foreach f,$(fail_vcd),--fail_vcd $(f)))

WANT_NO_DIVERSITY := $(NO_DIVERSITY)
ifneq ($(strip $(diversity)),)
WANT_NO_DIVERSITY := 0
endif
ifneq ($(strip $(no_diversity)),)
WANT_NO_DIVERSITY := $(strip $(no_diversity))
endif
NO_DIVERSITY_FLAG := $(if $(filter 1 yes true on,$(WANT_NO_DIVERSITY)),--no_diversity,)

.PHONY: all build clean run help

all: $(TARGET)

build: $(TARGET)

$(TARGET): $(OBJS)
	$(CXX) $(CXXFLAGS) $(OBJS) -o $@ $(LDFLAGS)

build/%.o: %.cpp common.hpp
	@mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< -o $@

run: $(TARGET)
	@if [ -z "$(strip $(pass_vcd))" ]; then \
		echo "ERROR: provide at least one pass_vcd value. Example: make run pass_vcd=\"build/pass1.vcd build/pass2.vcd\" fail_vcd=\"build/fail.vcd\""; \
		exit 1; \
	fi
	@if [ -z "$(strip $(fail_vcd))" ]; then \
		echo "ERROR: provide at least one fail_vcd value. Example: make run fail_vcd=\"build/fail.vcd\" pass_vcd=\"build/pass.vcd\""; \
		exit 1; \
	fi
	@mkdir -p $(dir $(OUT_FILE))
	@echo "Running: $(TARGET) $(PASS_ARGS) $(FAIL_ARGS) --out $(OUT_FILE) --window_events $(WINDOW_EVENTS_VALUE) --topk $(TOPK_VALUE) $(NO_DIVERSITY_FLAG) $(RUN_ARGS)"
	@$(TARGET) $(PASS_ARGS) $(FAIL_ARGS) --out "$(OUT_FILE)" --window_events "$(WINDOW_EVENTS_VALUE)" --topk "$(TOPK_VALUE)" $(NO_DIVERSITY_FLAG) $(RUN_ARGS)
	@echo "Output written to $(OUT_FILE)"

help:
	@echo "Targets:"
	@echo "  make build            Build $(TARGET)"
	@echo "  make run pass_vcd=\"p1 [p2 ...]\" fail_vcd=\"f1 [f2 ...]\" [out=FILE] [window_events=N] [topk=N] [no_diversity=0|1] [run_args=\"...\"]"
	@echo "                        Defaults: window_events=$(WINDOW_EVENTS), topk=$(TOPK), no_diversity=$(NO_DIVERSITY), out auto-increments under build/"
	@echo "                        Supply multiple VCDs as a quoted space-separated list."
	@echo "  make clean            Remove build artifacts"

clean:
	rm -rf build

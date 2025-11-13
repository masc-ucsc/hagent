CXX      ?= g++
CXXFLAGS ?= -std=c++17 -O2 -pipe -I.
LDFLAGS  ?=

override PATH := /usr/bin:$(PATH)

SRCS := main.cpp scorer.cpp utils.cpp vcd_stream.cpp
OBJS := $(SRCS:%.cpp=build/%.o)
TARGET := build/invariance_detect

.PHONY: all clean run help

all: $(TARGET)

$(TARGET): $(OBJS)
	$(CXX) $(CXXFLAGS) $(OBJS) -o $@ $(LDFLAGS)

build/%.o: %.cpp common.hpp | build
	$(CXX) $(CXXFLAGS) -c $< -o $@

build:
	@mkdir -p $@

clean:
	rm -rf build

run: $(TARGET)
	@PASS_LIST="$(strip $(pass_vcd))"; \
	FAIL_LIST="$(strip $(fail_vcd))"; \
	if [ -z "$$PASS_LIST" ]; then \
		echo "ERROR: provide at least one pass_vcd (space-separated list)"; \
		exit 1; \
	fi; \
	if [ -z "$$FAIL_LIST" ]; then \
		echo "ERROR: provide at least one fail_vcd (space-separated list)"; \
		exit 1; \
	fi; \
	OUT_OPT="$(strip $(out))"; \
	if [ -z "$$OUT_OPT" ]; then \
		BASE="anomalies-11040.txt"; \
		OUT_OPT="$$BASE"; \
		if [ -e "$$OUT_OPT" ]; then \
			STEM="$${BASE%.*}"; \
			EXT=".$${BASE##*.}"; \
			if [ "$$STEM" = "$$BASE" ]; then \
				STEM="$$BASE"; \
				EXT=""; \
			fi; \
			IDX=1; \
			while :; do \
				CAND="$$STEM_$${IDX}$$EXT"; \
				if [ ! -e "$$CAND" ]; then \
					OUT_OPT="$$CAND"; \
					break; \
				fi; \
				IDX=$$((IDX+1)); \
			done; \
		fi; \
	fi; \
	WINDOW_EVENTS_VAL="$(strip $(window_events))"; \
	if [ -z "$$WINDOW_EVENTS_VAL" ]; then WINDOW_EVENTS_VAL=2000; fi; \
	TOPK_VAL="$(strip $(topk))"; \
	if [ -z "$$TOPK_VAL" ]; then TOPK_VAL=200; fi; \
	NO_DIV="$(strip $(no_diversity))"; \
	if [ -z "$$NO_DIV" ]; then NO_DIV=1; fi; \
	CMD_ARGS=""; \
	for f in $$PASS_LIST; do CMD_ARGS="$$CMD_ARGS --pass_vcd $$f"; done; \
	for f in $$FAIL_LIST; do CMD_ARGS="$$CMD_ARGS --fail_vcd $$f"; done; \
	CMD_ARGS="$$CMD_ARGS --out $$OUT_OPT --window_events $$WINDOW_EVENTS_VAL --topk $$TOPK_VAL"; \
	if [ "$$NO_DIV" != "0" ]; then CMD_ARGS="$$CMD_ARGS --no_diversity"; fi; \
	if [ -n "$(strip $(args))" ]; then CMD_ARGS="$$CMD_ARGS $(strip $(args))"; fi; \
	echo "./$(TARGET) $$CMD_ARGS"; \
	./$(TARGET) $$CMD_ARGS

help:
	@echo "Usage:"
	@echo "  make            Build the detector binary"
	@echo "  make run pass_vcd=\"good.vcd ...\" fail_vcd=\"bad.vcd ...\" [out=FILE] [window_events=N] [topk=N] [no_diversity=0] [args=\"...\"]"
	@echo "  make clean      Remove build artifacts"

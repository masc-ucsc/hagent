CXX      ?= g++
CXXFLAGS ?= -std=c++17 -O2 -pipe -I. #-I/soe/jj8/local/sqlite/include 
LDFLAGS  ?=

SRCS := main.cpp scorer.cpp utils.cpp vcd_stream.cpp
OBJS := $(SRCS:%.cpp=build/%.o)
TARGET := build/invariance_detect

.PHONY: all clean

all: $(TARGET)

# Link step
$(TARGET): $(OBJS)
	$(CXX) $(CXXFLAGS) $(OBJS) -o $@ $(LDFLAGS)

# Compile step — ensure build directory exists first
build/%.o: %.cpp common.hpp
	@mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	rm -rf build

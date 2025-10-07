# ================================
# Invariance Detector Makefile
# ================================

# Compiler and build flags
CXX      := g++
CXXFLAGS := -std=c++17 -O2 -pipe
TARGET   := invariance_detect
SRC      := invariance_detect.cpp

# ================================
# User variables (must be provided)
# ================================

# Example usage:
# make run PASS_VCDS="./build/pass1.vcd ./build/pass2.vcd" \
#           FAIL_VCD="./build/fail.vcd" \
#           OUT="./anomalies.txt" \
#           WINDOW_EVENTS=2000 \
#           TOPK=200 \
#           DIVERSITY="--no_diversity"

# ================================
# Build target
# ================================

all: $(TARGET)

$(TARGET): $(SRC)
	@echo "Compiling $(TARGET)..."
	$(CXX) $(CXXFLAGS) $(SRC) -o $(TARGET)
	@echo "Build complete."

# ================================
# Run target (requires variables)
# ================================

run: check-vars $(TARGET)
	@echo "Running invariance detection..."
	./$(TARGET) \
		$(foreach vcd,$(PASS_VCDS),--pass_vcd $(vcd)) \
		--fail_vcd $(FAIL_VCD) \
		--out $(OUT) \
		--window_events $(WINDOW_EVENTS) \
		--topk $(TOPK) \
		$(DIVERSITY)

# ================================
# Clean target
# ================================

clean:
	@echo "Cleaning build artifacts..."
	rm -f $(TARGET) $(OUT)
	@echo "Clean complete."

# ================================
# Variable checking
# ================================

check-vars:
ifndef PASS_VCDS
	$(error PASS_VCDS is not set. Example: make run PASS_VCDS="./build/p1.vcd ./build/p2.vcd" FAIL_VCD=./build/f.vcd OUT=out.txt WINDOW_EVENTS=2000 TOPK=200 DIVERSITY="--no_diversity")
endif
ifndef FAIL_VCD
	$(error FAIL_VCD is not set.)
endif
ifndef OUT
	$(error OUT is not set.)
endif
ifndef WINDOW_EVENTS
	$(error WINDOW_EVENTS is not set.)
endif
ifndef TOPK
	$(error TOPK is not set.)
endif

# ================================
# Help
# ================================

help:
	@echo "Usage:"
	@echo "  make all"
	@echo "  make run PASS_VCDS=\"./build/p1.vcd ./build/p2.vcd\" FAIL_VCD=./build/fail.vcd OUT=out.txt WINDOW_EVENTS=2000 TOPK=200 DIVERSITY=\"--no_diversity\""
	@echo "  make clean"

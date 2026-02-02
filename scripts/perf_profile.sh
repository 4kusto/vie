#!/bin/bash

# Configuration
ITERATIONS=${1:-10000}
OUTPUT_DIR=".lake/build/bin"
BENCH_EXE="$OUTPUT_DIR/bench"
PERF_DATA="perf.data"

echo "=== ViE Performance Profile Script ==="

# 1. Build the benchmark executable
echo "Building benchmark..."
lake build bench

if [ $? -ne 0 ]; then
    echo "Error: Build failed."
    exit 1
fi

if [ ! -f "$BENCH_EXE" ]; then
    echo "Error: Benchmark executable not found at $BENCH_EXE"
    exit 1
fi

# 2. Check for perf
if ! command -v perf &> /dev/null; then
    echo "Error: 'perf' command not found. Please install perf"
    exit 1
fi

# 3. Run perf record
echo "Running perf record with $ITERATIONS iterations..."
echo "This may require sudo permissions for kernel-level profiling."

perf record -g --call-graph dwarf "$BENCH_EXE" "$ITERATIONS"

if [ $? -eq 0 ]; then
    echo "=== Profile Complete ==="
    echo "To view the results, run:"
    echo "  perf report"
    echo ""
    echo "To generate a flamegraph (if tools are installed):"
    echo "  perf script | stackcollapse-perf.pl | flamegraph.pl > flamegraph.svg"
else
    echo "Error: perf record failed. You might need to run: sudo sysctl -w kernel.perf_event_paranoid=-1"
fi

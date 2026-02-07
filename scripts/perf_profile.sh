#!/bin/bash

# Roles:
#   - perf_profile.sh: full perf/c2c profiling for the bench binary.
#   - perf_bench_bin.sh: perf profiling of bench binary (no lake exec overhead).
#   - perf_bench_lake.sh: perf profiling via lake exe (includes lake overhead).

set -euo pipefail

# Configuration
ITERATIONS=${1:-10000}
OUTPUT_DIR=".lake/build/bin"
BENCH_EXE="$OUTPUT_DIR/bench"
BENCH_ARGS="${PERF_BENCH_ARGS:---no-render}"

# Results directory configuration
RESULTS_ROOT="${PERF_RESULTS_ROOT:-perf}"
RUN_LABEL="${PERF_RUN_LABEL:-$(date +%H%M%S)}"
DATE_DIR="${RESULTS_ROOT}/$(date +%Y-%m-%d)"
REPORT_DIR="${DATE_DIR}/report"
FLAME_DIR="${DATE_DIR}/flamegraph"
PERF_DATA="${DATE_DIR}/perf-${RUN_LABEL}.data"
PERF_REPORT="${REPORT_DIR}/perf-${RUN_LABEL}.log"
PERF_FOLDED="${FLAME_DIR}/perf-${RUN_LABEL}.folded"
FLAMEGRAPH_SVG="${FLAME_DIR}/flamegraph-${RUN_LABEL}.svg"
FLAMEGRAPH_DIR="${FLAMEGRAPH_DIR:-$HOME/.local/bin/FlameGraph}"
STACKCOLLAPSE_BIN="${STACKCOLLAPSE_BIN:-${FLAMEGRAPH_DIR}/stackcollapse-perf.pl}"
FLAMEGRAPH_BIN="${FLAMEGRAPH_BIN:-${FLAMEGRAPH_DIR}/flamegraph.pl}"

# Mode: perf | c2c | both
PERF_MODE="${PERF_MODE:-perf}"
C2C_DIR="${DATE_DIR}/c2c"
C2C_DATA="${C2C_DIR}/c2c-${RUN_LABEL}.data"
C2C_REPORT="${C2C_DIR}/c2c-${RUN_LABEL}.log"

echo "=== ViE Performance Profile Script ==="
echo "Results: ${DATE_DIR}"

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

# 3. Prepare output directories
mkdir -p "$REPORT_DIR" "$FLAME_DIR"

# 3. Run perf record (mode: perf/both)
if [ "$PERF_MODE" = "perf" ] || [ "$PERF_MODE" = "both" ]; then
    echo "Running perf record with $ITERATIONS iterations..."
    echo "This may require sudo permissions for kernel-level profiling."

    perf record -g --call-graph dwarf -o "$PERF_DATA" "$BENCH_EXE" "$ITERATIONS" $BENCH_ARGS

    if [ $? -eq 0 ]; then
        echo "=== perf record complete ==="
        echo "Writing report to ${PERF_REPORT}"
        perf report -i "$PERF_DATA" --stdio > "$PERF_REPORT"

        if { [ -x "${STACKCOLLAPSE_BIN}" ] && [ -x "${FLAMEGRAPH_BIN}" ]; } || \
           { command -v stackcollapse-perf.pl &> /dev/null && command -v flamegraph.pl &> /dev/null; }; then
            echo "Generating flamegraph..."
            if [ -x "${STACKCOLLAPSE_BIN}" ] && [ -x "${FLAMEGRAPH_BIN}" ]; then
                perf script -i "$PERF_DATA" | "${STACKCOLLAPSE_BIN}" > "$PERF_FOLDED"
                "${FLAMEGRAPH_BIN}" "$PERF_FOLDED" > "$FLAMEGRAPH_SVG"
            else
                perf script -i "$PERF_DATA" | stackcollapse-perf.pl > "$PERF_FOLDED"
                flamegraph.pl "$PERF_FOLDED" > "$FLAMEGRAPH_SVG"
            fi
        else
            echo "Flamegraph tools not found. Skipping flamegraph generation."
            echo "Expected in \$FLAMEGRAPH_DIR (default: ${FLAMEGRAPH_DIR})"
        fi
    else
        echo "Error: perf record failed. You might need to run: sudo sysctl -w kernel.perf_event_paranoid=-1"
        exit 1
    fi
fi

# 4. Run perf c2c record/report (mode: c2c/both)
if [ "$PERF_MODE" = "c2c" ] || [ "$PERF_MODE" = "both" ]; then
    if perf c2c record --help &> /dev/null; then
        echo "Running perf c2c record with $ITERATIONS iterations..."
        mkdir -p "$C2C_DIR"
        perf c2c record -o "$C2C_DATA" -- "$BENCH_EXE" "$ITERATIONS" $BENCH_ARGS
        if [ $? -eq 0 ]; then
            echo "Writing c2c report to ${C2C_REPORT}"
            perf c2c report -i "$C2C_DATA" --stdio > "$C2C_REPORT"
        else
            echo "Warning: perf c2c record failed."
            exit 1
        fi
    else
        echo "Warning: perf c2c is not available in this perf build."
        exit 1
    fi
fi

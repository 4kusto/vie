#!/bin/bash

set -euo pipefail

# Usage:
#   scripts/perf_bench_bin.sh [iterations]
#
# Environment:
#   BENCH_ARGS         Extra args for benchmark (default: --no-render)
#   BENCH_EXE          Path to bench binary (default: .lake/build/bin/bench)
#   PERF_RESULTS_ROOT  Results root dir (default: perf)
#   PERF_RUN_LABEL     Label for run (default: HHMMSS)
#   FLAMEGRAPH_DIR     Flamegraph tools dir (default: $HOME/.local/bin/Flamegraph)
#
# Example:
#   BENCH_ARGS="--case search-bloom --lines 800 --line-len 120 --no-render" scripts/perf_bench_bin.sh 2000

ITERATIONS="10000"
BENCH_ARGS="${BENCH_ARGS:---no-render}"
PERF_CASES="${PERF_CASES:-}"

usage() {
  cat <<'USAGE'
Usage:
  scripts/perf_bench_bin.sh [iterations]
  scripts/perf_bench_bin.sh --iterations N
  scripts/perf_bench_bin.sh --case NAME [--case NAME...]
  scripts/perf_bench_bin.sh --cases "case1,case2"

Notes:
  - Cases are passed through to: bench --case <name>
  - Aliases: linear -> search-linear, bloom -> search-bloom
  - Extra bench args via BENCH_ARGS env (default: --no-render)
USAGE
}

case_list=""
iter_set="0"
while [ "$#" -gt 0 ]; do
  case "$1" in
    -n|--iterations)
      ITERATIONS="${2:-}"
      iter_set="1"
      shift 2
      ;;
    --case)
      case_list="${case_list}${2:-},"
      shift 2
      ;;
    --cases)
      PERF_CASES="${2:-}"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      if [[ "$1" =~ ^[0-9]+$ ]] && [ "$iter_set" = "0" ]; then
        ITERATIONS="$1"
        iter_set="1"
        shift
      else
        echo "Error: unknown argument '$1'"
        usage
        exit 1
      fi
      ;;
  esac
done

if [ -n "$case_list" ]; then
  case_list="${case_list%,}"
  if [ -n "$PERF_CASES" ]; then
    PERF_CASES="${PERF_CASES},${case_list}"
  else
    PERF_CASES="${case_list}"
  fi
fi
BENCH_EXE="${BENCH_EXE:-.lake/build/bin/bench}"

RESULTS_ROOT="${PERF_RESULTS_ROOT:-perf}"
RUN_LABEL="${PERF_RUN_LABEL:-$(date +%H%M%S)}"
DATE_DIR="${RESULTS_ROOT}/$(date +%Y-%m-%d)"
REPORT_DIR="${DATE_DIR}/report"
PERF_DATA="${DATE_DIR}/perf-bench-bin-${RUN_LABEL}.data"
PERF_REPORT="${REPORT_DIR}/perf-bench-bin-${RUN_LABEL}.log"
FLAME_DIR="${DATE_DIR}/flamegraph"
PERF_FOLDED="${FLAME_DIR}/perf-bench-bin-${RUN_LABEL}.folded"
FLAMEGRAPH_SVG="${FLAME_DIR}/flamegraph-bench-bin-${RUN_LABEL}.svg"
FLAMEGRAPH_DIR="${FLAMEGRAPH_DIR:-$HOME/.local/bin/FlameGraph}"
STACKCOLLAPSE_BIN="${STACKCOLLAPSE_BIN:-${FLAMEGRAPH_DIR}/stackcollapse-perf.pl}"
FLAMEGRAPH_BIN="${FLAMEGRAPH_BIN:-${FLAMEGRAPH_DIR}/flamegraph.pl}"

echo "=== ViE perf (bench binary) ==="
echo "Iterations: ${ITERATIONS}"
echo "Bench args: ${BENCH_ARGS}"
if [ -n "${PERF_CASES}" ]; then
  echo "Perf cases: ${PERF_CASES}"
fi
echo "Bench exe:  ${BENCH_EXE}"
echo "Results: ${DATE_DIR}"

# 1. Build bench
echo "Building benchmark..."
lake build bench

if [ ! -x "${BENCH_EXE}" ]; then
  echo "Error: bench executable not found at ${BENCH_EXE}"
  exit 1
fi

# 2. Check for perf
if ! command -v perf &> /dev/null; then
  echo "Error: 'perf' command not found. Please install perf."
  exit 1
fi

# 3. Prepare output directories
mkdir -p "${REPORT_DIR}" "${FLAME_DIR}"

# 4. Run perf record against the bench binary (no lake exec overhead)
run_one () {
  local label="$1"
  shift
  local -a extra_args=("$@")
  local data="${DATE_DIR}/perf-bench-bin-${label}.data"
  local report="${REPORT_DIR}/perf-bench-bin-${label}.log"
  local folded="${FLAME_DIR}/perf-bench-bin-${label}.folded"
  local svg="${FLAME_DIR}/flamegraph-bench-bin-${label}.svg"

  echo "Running perf record (${label})..."
  perf record -g --call-graph dwarf -o "${data}" -- \
    "${BENCH_EXE}" "${ITERATIONS}" "${BENCH_ARGS_ARR[@]}" "${extra_args[@]}"

  echo "Writing report to ${report}"
  perf report -i "${data}" --stdio > "${report}"

  if { [ -x "${STACKCOLLAPSE_BIN}" ] && [ -x "${FLAMEGRAPH_BIN}" ]; } || \
     { command -v stackcollapse-perf.pl &> /dev/null && command -v flamegraph.pl &> /dev/null; }; then
    echo "Generating flamegraph (${label})..."
    if [ -x "${STACKCOLLAPSE_BIN}" ] && [ -x "${FLAMEGRAPH_BIN}" ]; then
      perf script -i "${data}" | "${STACKCOLLAPSE_BIN}" > "${folded}"
      "${FLAMEGRAPH_BIN}" "${folded}" > "${svg}"
    else
      perf script -i "${data}" | stackcollapse-perf.pl > "${folded}"
      flamegraph.pl "${folded}" > "${svg}"
    fi
  else
    echo "Flamegraph tools not found. Skipping flamegraph generation."
    echo "Expected in \$FLAMEGRAPH_DIR (default: ${FLAMEGRAPH_DIR})"
  fi
}

read -r -a BENCH_ARGS_ARR <<< "${BENCH_ARGS}"

if [ -n "${PERF_CASES}" ]; then
  IFS=',' read -r -a CASES_ARR <<< "${PERF_CASES}"
  for c in "${CASES_ARR[@]}"; do
    c_trim="$(echo "${c}" | xargs)"
    if [ -z "${c_trim}" ]; then
      continue
    fi
    case "${c_trim}" in
      linear) norm="search-linear" ;;
      bloom) norm="search-bloom" ;;
      *) norm="${c_trim}" ;;
    esac
    run_one "${RUN_LABEL}-${norm}" --case "${norm}"
  done
else
  run_one "${RUN_LABEL}"
fi

echo "Done."

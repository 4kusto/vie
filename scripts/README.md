# Scripts

This directory contains perf profiling helpers for the `bench` executable.

## Quick Summary

- `perf_bench_bin.sh`: perf record for the bench binary directly (no lake overhead).
- `perf_bench_lake.sh`: perf record via `lake exe bench` (includes lake overhead).
- `perf_profile.sh`: heavier profiling (perf and optional c2c) with reports and flamegraph.

## Common Output

All scripts write to `perf/YYYY-MM-DD/`:

- `report/`: perf report logs
- `flamegraph/`: folded stacks and SVG flamegraphs
- `c2c/`: cache-to-cache reports (when enabled)

## perf_bench_bin.sh

Purpose: fast perf capture of the bench binary.

Usage examples:

```bash
./scripts/perf_bench_bin.sh --iterations 10000 --case linear
./scripts/perf_bench_bin.sh --cases linear,bloom --iterations 20000
```

Key options:

- `--iterations N`
- `--case NAME` or `--cases NAME,NAME`
- `--no-render` is passed to the bench by default (override with `PERF_BENCH_ARGS`).

## perf_bench_lake.sh

Purpose: perf capture through `lake exe bench` (measures lake overhead too).

Usage examples:

```bash
./scripts/perf_bench_lake.sh --iterations 10000 --case linear
./scripts/perf_bench_lake.sh --cases linear,bloom --iterations 20000
```

Key options match `perf_bench_bin.sh`.

## perf_profile.sh

Purpose: heavier profiling (perf report + optional c2c) and flamegraph.

Usage examples:

```bash
./scripts/perf_profile.sh 10000
PERF_MODE=both ./scripts/perf_profile.sh 10000
PERF_MODE=c2c ./scripts/perf_profile.sh 10000
```

## Flamegraph Tools

By default, scripts look in:

- `$HOME/.local/bin/FlameGraph`

You can override with:

- `FLAMEGRAPH_DIR=/path/to/FlameGraph`
- `STACKCOLLAPSE_BIN=/path/to/stackcollapse-perf.pl`
- `FLAMEGRAPH_BIN=/path/to/flamegraph.pl`

## Environment Variables

- `PERF_RESULTS_ROOT`: results directory root (default: `perf`)
- `PERF_RUN_LABEL`: label for the run (default: `HHMMSS`)
- `PERF_BENCH_ARGS`: extra args passed to the bench executable
- `PERF_MODE`: for `perf_profile.sh` only (`perf`, `c2c`, `both`)

## Notes

- `perf` may require elevated permissions depending on your kernel settings.
- If you see a permissions error, check `kernel.perf_event_paranoid`.

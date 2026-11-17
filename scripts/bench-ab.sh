#!/usr/bin/env bash
set -euo pipefail

# A/B benchmark driver: freeze a baseline binary, then measure it turn about with
# the current build on one machine and let `CompPolyBench --compare` judge.
#
# Run from the repository root. Everything lives under bench/out/ab/, which is
# gitignored. The Lean binary does all statistics; this script only sequences.

usage() {
  cat <<'EOF'
Usage:
  scripts/bench-ab.sh freeze [--force]
  scripts/bench-ab.sh run <group>[,<group>...]
  scripts/bench-ab.sh clean [--all]

freeze   build the benchmark executable and keep a copy as the baseline
run      build the current tree as the candidate, run baseline and candidate
         alternately on the given groups plus the harness self-check, and
         judge the candidate with `CompPolyBench --compare`
clean    remove comparison runs under bench/out/ab/ (--all: the baseline too)

Environment:
  BENCH_AB_ROUNDS     invocations per side (default 5)
  BENCH_AB_PRESET     small | medium | large (default medium)
  BENCH_AB_THRESHOLD  practical-importance threshold in percent (default 5)

Exit codes follow `CompPolyBench --compare`: 0 every row judged, 1 nothing
compared, 3 a row mismatched or went missing. Misuse exits 2.
EOF
}

AB_DIR="bench/out/ab"
BASELINE_DIR="$AB_DIR/baseline"
BASELINE_BIN="$BASELINE_DIR/CompPolyBench"
BUILT_BIN=".lake/build/bin/CompPolyBench"
HARNESS_GROUPS="harness-floor,harness-canary,harness-chain-floor,harness-chain-linearity"

ROUNDS="${BENCH_AB_ROUNDS:-5}"
PRESET="${BENCH_AB_PRESET:-medium}"
THRESHOLD="${BENCH_AB_THRESHOLD:-5}"

build_bench() {
  echo "building CompPolyBench..."
  lake build CompPolyBenchLib CompPolyBench
}

describe_commit() {
  local sha dirty
  sha="$(git rev-parse HEAD)"
  dirty=""
  if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    dirty=" (dirty)"
  fi
  printf '%s%s\n' "$sha" "$dirty"
}

cmd_freeze() {
  local force=0
  if [ "${1:-}" = "--force" ]; then
    force=1
    shift
  fi
  if [ "$#" -ne 0 ]; then
    usage
    exit 2
  fi
  if [ -x "$BASELINE_BIN" ] && [ "$force" -ne 1 ]; then
    echo "a baseline is already frozen at $BASELINE_BIN" >&2
    echo "  commit: $(cat "$BASELINE_DIR/commit.txt" 2>/dev/null || echo unknown)" >&2
    echo "rerun with --force to replace it" >&2
    exit 2
  fi
  build_bench
  mkdir -p "$BASELINE_DIR"
  cp "$BUILT_BIN" "$BASELINE_BIN"
  describe_commit > "$BASELINE_DIR/commit.txt"
  echo "froze baseline from $(cat "$BASELINE_DIR/commit.txt") at $BASELINE_BIN"
}

run_side() {
  local bin="$1" out_dir="$2" groups="$3"
  mkdir -p "$out_dir"
  if ! "$bin" "--$PRESET" --json-only --out-dir "$out_dir" --groups "$groups" > "$out_dir/stdout.log" 2> "$out_dir/stderr.log"; then
    echo "benchmark run failed: $bin (see $out_dir/stderr.log)" >&2
    cat "$out_dir/stderr.log" >&2
    exit 1
  fi
}

cmd_run() {
  if [ "$#" -ne 1 ]; then
    usage
    exit 2
  fi
  local groups="$1"
  case "$PRESET" in
    small|medium|large) ;;
    *) echo "BENCH_AB_PRESET must be small, medium or large, got '$PRESET'" >&2; exit 2 ;;
  esac
  if ! [ "$ROUNDS" -ge 1 ] 2>/dev/null; then
    echo "BENCH_AB_ROUNDS must be a positive integer, got '$ROUNDS'" >&2
    exit 2
  fi
  if [ ! -x "$BASELINE_BIN" ]; then
    echo "no frozen baseline at $BASELINE_BIN; run 'scripts/bench-ab.sh freeze' first" >&2
    exit 2
  fi

  # Build once, before any measurement, so a rebuild can never race a run; from
  # here on the binaries are invoked directly rather than through `lake exe`.
  build_bench

  local run_id selection
  run_id="$(date +%y%m%d-%H%M%S)"
  local run_dir="$AB_DIR/$run_id"
  selection="$groups,$HARNESS_GROUPS"
  echo "baseline: $(cat "$BASELINE_DIR/commit.txt")"
  echo "candidate: $(describe_commit)"
  echo "groups: $selection"
  echo "preset: $PRESET, rounds: $ROUNDS per side, output: $run_dir"

  local k
  local -a baseline_args=() candidate_args=()
  for k in $(seq 1 "$ROUNDS"); do
    local b_dir="$run_dir/baseline/$k" c_dir="$run_dir/candidate/$k"
    # Alternate which side goes first so a slow drift in the machine cannot
    # systematically favour one of them.
    if [ $((k % 2)) -eq 1 ]; then
      echo "round $k: baseline, candidate"
      run_side "$BASELINE_BIN" "$b_dir" "$selection"
      run_side "$BUILT_BIN" "$c_dir" "$selection"
    else
      echo "round $k: candidate, baseline"
      run_side "$BUILT_BIN" "$c_dir" "$selection"
      run_side "$BASELINE_BIN" "$b_dir" "$selection"
    fi
    baseline_args+=(--baseline "$b_dir")
    candidate_args+=(--candidate "$c_dir")
  done

  echo
  set +e
  "$BUILT_BIN" --compare "${baseline_args[@]}" "${candidate_args[@]}" \
    --threshold "$THRESHOLD" --out-dir "$run_dir"
  local status=$?
  set -e
  exit "$status"
}

cmd_clean() {
  local all=0
  if [ "${1:-}" = "--all" ]; then
    all=1
    shift
  fi
  if [ "$#" -ne 0 ]; then
    usage
    exit 2
  fi
  if [ ! -d "$AB_DIR" ]; then
    echo "nothing to clean: $AB_DIR does not exist"
    exit 0
  fi
  local dir
  for dir in "$AB_DIR"/*/; do
    [ -d "$dir" ] || continue
    if [ "$dir" = "$BASELINE_DIR/" ] && [ "$all" -ne 1 ]; then
      continue
    fi
    echo "removing $dir"
    rm -rf "$dir"
  done
}

case "${1:-}" in
  freeze) shift; cmd_freeze "$@" ;;
  run) shift; cmd_run "$@" ;;
  clean) shift; cmd_clean "$@" ;;
  -h|--help|help) usage; exit 0 ;;
  *) usage; exit 2 ;;
esac

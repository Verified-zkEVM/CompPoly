#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  build_timing_report.sh run <label> <results-file> -- <command> [args...]
  build_timing_report.sh render <results-file>

Labels:
  clean_build
  warm_rebuild
  test_path
EOF
}

append_result() {
  local results_file="$1"
  local label="$2"
  local real_time="$3"
  local user_time="$4"
  local sys_time="$5"
  local exit_code="$6"

  python3 - "$results_file" "$label" "$real_time" "$user_time" "$sys_time" "$exit_code" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
path.parent.mkdir(parents=True, exist_ok=True)

record = {
    "label": sys.argv[2],
    "real": float(sys.argv[3]),
    "user": float(sys.argv[4]),
    "sys": float(sys.argv[5]),
    "exit_code": int(sys.argv[6]),
}

with path.open("a", encoding="utf-8") as handle:
    handle.write(json.dumps(record) + "\n")
PY
}

run_command() {
  if [ "$#" -lt 4 ]; then
    usage
    exit 2
  fi

  local label="$1"
  local results_file="$2"
  shift 2

  if [ "$1" != "--" ]; then
    usage
    exit 2
  fi
  shift

  local timing_file
  timing_file="$(mktemp)"

  set +e
  /usr/bin/time -p -o "$timing_file" "$@"
  local exit_code=$?
  set -e

  local real_time user_time sys_time
  real_time="$(awk '$1 == "real" { print $2 }' "$timing_file")"
  user_time="$(awk '$1 == "user" { print $2 }' "$timing_file")"
  sys_time="$(awk '$1 == "sys" { print $2 }' "$timing_file")"
  rm -f "$timing_file"

  append_result "$results_file" "$label" "$real_time" "$user_time" "$sys_time" "$exit_code"
  exit "$exit_code"
}

render_report() {
  if [ "$#" -ne 1 ]; then
    usage
    exit 2
  fi

  local results_file="$1"

  python3 - "$results_file" <<'PY'
import json
import os
import pathlib
import sys

path = pathlib.Path(sys.argv[1])

display = {
    "clean_build": ("Clean build", "`rm -rf .lake/build && lake build`"),
    "warm_rebuild": ("Warm rebuild", "`lake build`"),
    "test_path": ("Test path", "`lake test`"),
}
ordered_labels = ["clean_build", "warm_rebuild", "test_path"]

records = {}
if path.exists():
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        record = json.loads(line)
        records[record["label"]] = record


def fmt(value: float) -> str:
    return f"{value:.2f}"


def status(record: dict) -> str:
    return "ok" if record["exit_code"] == 0 else f"exit {record['exit_code']}"


source_sha = os.environ.get("BUILD_TIMING_SOURCE_SHA")
source_subject = os.environ.get("BUILD_TIMING_SOURCE_SUBJECT")
source_branch = os.environ.get("BUILD_TIMING_SOURCE_BRANCH") or os.environ.get("GITHUB_REF_NAME")
source_repo = os.environ.get("GITHUB_REPOSITORY")

print("## Build Timing Report")
print()

if source_sha:
    short_sha = source_sha[:7]
    if source_repo:
        commit_ref = f"[`{short_sha}`](https://github.com/{source_repo}/commit/{source_sha})"
    else:
        commit_ref = f"`{short_sha}`"
    print(f"- Commit: {commit_ref}")
if source_subject:
    print(f"- Message: {source_subject}")
if source_branch:
    print(f"- Ref: `{source_branch}`")
print("- Measured on `ubuntu-latest` with `/usr/bin/time -p`.")
print()

if not records:
    print("No timing data was captured.")
    sys.exit(0)

print("| Measurement | Command | Real (s) | User (s) | Sys (s) | Status |")
print("| --- | --- | ---: | ---: | ---: | --- |")
for label in ordered_labels:
    if label not in records:
        continue
    record = records[label]
    name, command = display[label]
    print(
        f"| {name} | {command} | {fmt(record['real'])} | {fmt(record['user'])} | "
        f"{fmt(record['sys'])} | {status(record)} |"
    )

clean = records.get("clean_build")
warm = records.get("warm_rebuild")
test_path = records.get("test_path")

print()
print("### Variability")
print()
if clean and warm:
    delta = clean["real"] - warm["real"]
    spread = abs(delta)
    ratio = clean["real"] / warm["real"] if warm["real"] else None
    print(f"- Clean vs warm delta: `{delta:.2f}s`")
    if ratio is None:
        print("- Clean vs warm ratio: unavailable (`warm rebuild` reported `0.00s`)")
    else:
        print(f"- Clean vs warm ratio: `{ratio:.2f}x`")
    print(f"- Clean/warm spread: `{spread:.2f}s`")
else:
    print("- Clean/warm variability is unavailable because one of the build measurements is missing.")

if test_path:
    print(f"- Test path wall-clock: `{test_path['real']:.2f}s`")
else:
    print("- Test path timing is unavailable because the test measurement is missing.")

print()
print(
    "This compares a clean project build against an incremental rebuild in the same CI job; "
    "it is a lightweight variability signal, not a full cross-run benchmark."
)
PY
}

main() {
  if [ "$#" -lt 1 ]; then
    usage
    exit 2
  fi

  local command="$1"
  shift

  case "$command" in
    run)
      run_command "$@"
      ;;
    render)
      render_report "$@"
      ;;
    *)
      usage
      exit 2
      ;;
  esac
}

main "$@"

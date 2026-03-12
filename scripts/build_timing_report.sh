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
  local log_dir="${BUILD_TIMING_LOG_DIR:-}"
  local log_file=""

  if [ -n "$log_dir" ]; then
    mkdir -p "$log_dir"
    log_file="$log_dir/${label}.log"
  fi

  set +e
  if [ -n "$log_file" ]; then
    /usr/bin/time -p -o "$timing_file" "$@" 2>&1 | tee "$log_file"
    local exit_code=${PIPESTATUS[0]}
  else
    /usr/bin/time -p -o "$timing_file" "$@"
    local exit_code=$?
  fi
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
import re
import sys

path = pathlib.Path(sys.argv[1])

display = {
    "clean_build": {
        "name": "Clean build",
        "command": "`rm -rf .lake/build && lake build`",
    },
    "warm_rebuild": {
        "name": "Warm rebuild",
        "command": "`lake build`",
    },
    "test_path": {
        "name": "Test path",
        "command": "`lake test`",
    },
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


def module_to_source_path(target: str) -> str | None:
    if target == "CompPoly":
        return "CompPoly.lean"
    if target.startswith("CompPoly."):
        return target.replace(".", "/") + ".lean"
    if target == "CompPolyTests":
        return "tests/CompPolyTests.lean"
    if target.startswith("CompPolyTests."):
        return "tests/" + target.replace(".", "/") + ".lean"
    return None


def extract_clean_build_targets() -> list[dict]:
    log_dir = os.environ.get("BUILD_TIMING_LOG_DIR")
    if not log_dir:
        return []

    clean_log = pathlib.Path(log_dir) / "clean_build.log"
    if not clean_log.exists():
        return []

    pattern = re.compile(r"Built\s+(.+?)\s+\((\d+(?:\.\d+)?)s\)")
    entries = []
    seen = set()
    for line in clean_log.read_text(encoding="utf-8", errors="replace").splitlines():
        match = pattern.search(line)
        if not match:
            continue
        target = match.group(1).strip()
        if target in seen:
            continue
        seen.add(target)
        entries.append(
            {
                "target": target,
                "seconds": float(match.group(2)),
                "source": module_to_source_path(target),
            }
        )

    preferred = [
        entry for entry in entries if entry["target"].startswith(("CompPoly", "CompPolyTests"))
    ]
    selected = preferred if preferred else entries
    return sorted(selected, key=lambda entry: entry["seconds"], reverse=True)


source_sha = os.environ.get("BUILD_TIMING_SOURCE_SHA")
source_subject = os.environ.get("BUILD_TIMING_SOURCE_SUBJECT")
source_branch = os.environ.get("BUILD_TIMING_SOURCE_BRANCH") or os.environ.get("GITHUB_REF_NAME")
source_repo = os.environ.get("GITHUB_REPOSITORY")
clean_build_targets = extract_clean_build_targets()

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
print(
    "- Commands: "
    + "; ".join(
        f"{display[label]['name'].lower()} {display[label]['command']}" for label in ordered_labels
    )
    + "."
)
print()

if not records:
    print("No timing data was captured.")
    sys.exit(0)

print("| Measurement | Wall (s) | Status |")
print("| --- | ---: | --- |")
for label in ordered_labels:
    if label not in records:
        continue
    record = records[label]
    print(f"| {display[label]['name']} | {fmt(record['real'])} | {status(record)} |")

clean = records.get("clean_build")
warm = records.get("warm_rebuild")

print()
print("### Incremental Rebuild Signal")
print()
if clean and warm:
    delta = clean["real"] - warm["real"]
    ratio = clean["real"] / warm["real"] if warm["real"] else None
    if ratio is None:
        print(f"- Warm rebuild saved `{delta:.2f}s` vs clean.")
        print("- Clean:warm ratio is unavailable because `warm rebuild` reported `0.00s`.")
    else:
        print(f"- Warm rebuild saved `{delta:.2f}s` vs clean (`{ratio:.2f}x` faster).")
else:
    print("- Clean:warm comparison is unavailable because one of the build measurements is missing.")

print()
print(
    "This compares a clean project build against an incremental rebuild in the same CI job; "
    "it is a lightweight variability signal, not a full cross-run benchmark."
)

print()
print("### Slowest Clean-Build Files")
print()
if clean_build_targets:
    shown = clean_build_targets[:20]
    print(
        f"Showing {len(shown)} slowest of {len(clean_build_targets)} repo targets parsed from the clean build log."
    )
    print()
    print("| Wall (s) | Path |")
    print("| ---: | --- |")
    for entry in shown:
        path_label = entry["source"] or entry["target"]
        print(f"| {entry['seconds']:.2f} | `{path_label}` |")
else:
    print("No per-target timings were parsed from the clean build log.")
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

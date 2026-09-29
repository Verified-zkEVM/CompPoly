#!/usr/bin/env python3
"""Validate and compare the 18 selected Lean/Plonky3 scalar field workloads."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
FIELDS = {"koalabear": "KoalaBear", "mersenne31": "Mersenne31", "goldilocks": "Goldilocks"}
GROUPS = [f"fields-{f}-{op}" for f in FIELDS for op in ("add", "mul", "inv", "pow")]
EXPECTED = {(g, mode) for g in GROUPS for mode in
            (("latency", "throughput") if g.endswith(("-add", "-mul")) else ("latency",))}


def command(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def rows(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def indexed(records, lean=False):
    selected = {}
    for row in records:
        if lean and not row["name"].endswith("-fast"):
            continue
        mode = (row["digest_class"] or "latency") if lean else row["mode"]
        key = row["group_key"], mode
        if key in selected:
            raise ValueError(f"duplicate case: {key}")
        selected[key] = row
    if selected.keys() != EXPECTED:
        raise ValueError(f"unexpected cases: missing {EXPECTED - selected.keys()}, extra {selected.keys() - EXPECTED}")
    return selected


def compare(lean, rust):
    for key in EXPECTED:
        for prop in ("checksum", "work_units"):
            if int(lean[key][prop]) != int(rust[key][prop]):
                raise ValueError(f"{key}: {prop} differs: {lean[key][prop]} vs {rust[key][prop]}")


def report(out, measurements, manifest):
    lines = ["## Small fields: fast Lean vs Plonky3", "",
             "Nanoseconds per operation; **lower is better**. Values are the median of run medians; ± is the median absolute deviation between runs. Ratio = Lean / Rust (>1 means Rust is faster).", ""]
    for mode in ("latency", "throughput"):
        lines += [f"### {mode.title()}", "", "| Field | Operation | Fast Lean (ns) | Plonky3 (ns) | Lean / Rust |",
                  "| :--- | :--- | ---: | ---: | ---: |"]
        for field, title in FIELDS.items():
            for op in ("add", "mul", "inv", "pow"):
                key = f"fields-{field}-{op}", mode
                if key not in EXPECTED:
                    continue
                values = []
                for language in ("lean", "rust"):
                    runs = [statistics.median(pair[language][key]["samples_picos"]) /
                            (1000 * pair[language][key]["work_units"]) for pair in measurements]
                    median = statistics.median(runs)
                    mad = statistics.median(abs(x - median) for x in runs)
                    values.append((median, mad))
                (lean, lm), (rust, rm) = values
                lines.append(f"| {title} | {'exp' if op == 'pow' else op} | {lean:.2f} ± {lm:.2f} | {rust:.2f} ± {rm:.2f} | {lean/rust:.2f}× |")
        lines.append("")
    lines += ["### Machine and method", "",
              f"- **CPU:** {manifest['cpu_model']}; {manifest['logical_cpus']} logical CPUs. Both runners pinned to logical CPU {manifest['cpu']}, sequentially, with one thread (SMT siblings: {manifest['smt_siblings']}).",
              f"- **Memory:** {manifest['memory_gib']:.1f} GiB. **OS:** {manifest['os']}; kernel {manifest['kernel']} ({manifest['architecture']}).",
              f"- **Toolchains:** {manifest['lean_version']}; {manifest['rust_version']}; Plonky3 0.4.2. Rust release, LTO, one codegen unit; RUSTFLAGS={manifest['rustflags']!r}.",
              f"- **Source:** `{manifest['commit']}`; tracked files dirty: {manifest['dirty']}. Fixture SHA-256: `{manifest['fixture_sha256']}`.",
              f"- **Sampling:** {len(measurements)} paired runs, alternating Lean/Rust order; each case uses 50 ms warmup and 20 samples targeting 1 ms each. All 18 untimed result digests agree with Lean; Lean also checks its reference implementations.",
              "- **Workloads:** add/mul use 1,280 operations per batch. Throughput uses ten scalar lanes and nine final combining operations (outside the 1,280 divisor), matching Lean. Inv/exp use 64 dependent steps of `inv(x + b)` / `(x + b)^0x5A5A5A5A`, so their times include one add per step. Only the final batch result is consumed.",
              "- **Shared host:** other jobs may contend for the CPU, SMT sibling, caches, or boost budget. These are observations under load, not isolated-machine speed claims.", ""]
    (out / "report.md").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--skip-build", action="store_true", help="use already built executables")
    parser.add_argument("--cpu", type=int, help="logical CPU; default: first allowed CPU")
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--out-dir", type=Path)
    args = parser.parse_args()
    if args.runs < 3:
        parser.error("use at least three paired runs")
    allowed = os.sched_getaffinity(0)
    cpu = min(allowed) if args.cpu is None else args.cpu
    if cpu not in allowed:
        parser.error(f"CPU {cpu} is outside allowed affinity")
    os.sched_setaffinity(0, {cpu})
    os.environ["LEAN_NUM_THREADS"] = "1"
    os.environ["CARGO_BUILD_JOBS"] = "1"
    out = (args.out_dir or ROOT / "bench/out" / time.strftime("small-fields-%Y%m%d-%H%M%S")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    if not args.skip_build:
        subprocess.run(["lake", "build", "CompPolyBench", "CompPolyFieldFixtures"], cwd=ROOT, check=True)
        subprocess.run(["cargo", "build", "--release", "--locked", "-j", "1"], cwd=ROOT / "bench/rust", check=True)
    fixtures = out / "fixtures.jsonl"
    fixtures.write_text(command([str(ROOT / ".lake/build/bin/CompPolyFieldFixtures")]) + "\n")
    rust_exe = ROOT / "bench/rust/target/release/comppoly-field-bench"

    def run(language, label, validate):
        directory = out / label / language
        directory.mkdir(parents=True)
        if language == "lean":
            cmd = [str(ROOT / ".lake/build/bin/CompPolyBench"), "--medium", "--json-only",
                   "--groups", ",".join(GROUPS), "--out-dir", str(directory)]
        else:
            cmd = [str(rust_exe), str(fixtures)]
        if validate:
            cmd.append("--validate-only")
        with (directory / "stdout.jsonl").open("w") as log:
            subprocess.run(cmd, cwd=ROOT, stdout=log, check=True)
        if language == "lean":
            files = list(directory.glob("results-*.jsonl"))
            if len(files) != 1:
                raise ValueError("expected one Lean result file")
            return indexed(rows(files[0]), lean=True)
        return indexed(rows(directory / "stdout.jsonl"))

    compare(run("lean", "validation", True), run("rust", "validation", True))
    print("All 18 cases: Lean/Rust checksums and operation counts agree.", flush=True)
    if args.validate_only:
        return
    manifest = {
        "commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(command(["git", "status", "--porcelain", "--untracked-files=no"])),
        "cpu": cpu, "logical_cpus": os.cpu_count(),
        "smt_siblings": Path(f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list").read_text().strip(),
        "cpu_model": next(line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("model name")),
        "memory_gib": int(Path("/proc/meminfo").read_text().splitlines()[0].split()[1]) / 1024**2,
        "os": platform.freedesktop_os_release()["PRETTY_NAME"], "kernel": platform.release(),
        "architecture": platform.machine(), "lean_version": command(["lake", "env", "lean", "--version"]),
        "rust_version": command(["rustc", "--version"], ROOT / "bench/rust"),
        "rustflags": os.environ.get("RUSTFLAGS", ""), "runs": args.runs,
        "fixture_sha256": hashlib.sha256(fixtures.read_bytes()).hexdigest(),
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "load_start": os.getloadavg(),
    }
    measurements = []
    for i in range(args.runs):
        pair = {}
        for language in (("lean", "rust") if i % 2 == 0 else ("rust", "lean")):
            print(f"Run {i+1}/{args.runs}: {language}, CPU {cpu}", flush=True)
            pair[language] = run(language, f"run-{i+1}", False)
        compare(pair["lean"], pair["rust"])
        measurements.append(pair)
    manifest["load_end"] = os.getloadavg()
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    report(out, measurements, manifest)
    print(f"Report: {out / 'report.md'}")


if __name__ == "__main__":
    main()

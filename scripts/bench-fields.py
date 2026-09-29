#!/usr/bin/env python3
"""Validate and compare selected Lean/Rust field workloads."""
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
SUITES = {
    "small-prime": {"koalabear": ("KoalaBear", "Plonky3", ("add", "mul", "inv", "pow")),
                    "mersenne31": ("Mersenne31", "Plonky3", ("add", "mul", "inv", "pow")),
                    "goldilocks": ("Goldilocks", "Plonky3", ("add", "mul", "inv", "pow"))},
    "large-prime": {"bn254": ("BN254 scalar", "arkworks", ("add", "mul", "inv", "pow"))},
}


def selection(suite):
    fields = {f: spec for name, values in SUITES.items()
              if suite == "all" or suite == name for f, spec in values.items()}
    groups = [f"fields-{f}-{op}" for f, (_, _, ops) in fields.items() for op in ops]
    expected = {(g, mode) for g in groups for mode in
                (("latency", "throughput") if g.endswith(("-add", "-mul")) else ("latency",))}
    return fields, groups, expected


def command(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def rows(path):
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def indexed(records, expected, lean=False):
    selected = {}
    for row in records:
        if lean and not row["name"].endswith("-fast"):
            continue
        mode = (row["digest_class"] or "latency") if lean else row["mode"]
        key = row["group_key"], mode
        if key in selected:
            raise ValueError(f"duplicate case: {key}")
        selected[key] = row
    if selected.keys() != expected:
        raise ValueError(f"unexpected cases: missing {expected - selected.keys()}, extra {selected.keys() - expected}")
    return selected


def compare(lean, rust):
    if lean.keys() != rust.keys():
        raise ValueError("Lean/Rust case sets differ")
    for key in lean:
        for prop in ("checksum", "work_units"):
            if int(lean[key][prop]) != int(rust[key][prop]):
                raise ValueError(f"{key}: {prop} differs: {lean[key][prop]} vs {rust[key][prop]}")


def report(out, measurements, manifest, fields, expected):
    lines = ["## Fields: fast Lean vs Rust", "",
             "Rust uses Plonky3 for small primes and arkworks for BN254 scalar arithmetic.", "",
             "Nanoseconds per operation; **lower is better**. Values are the median of run medians; ± is the median absolute deviation between runs. Ratio = Lean / Rust (>1 means Rust is faster).", ""]
    for mode in ("latency", "throughput"):
        lines += [f"### {mode.title()}", "", "| Field | Operation | Fast Lean (ns) | Rust (ns) | Lean / Rust |",
                  "| :--- | :--- | ---: | ---: | ---: |"]
        for field, (title, _library, operations) in fields.items():
            for op in operations:
                key = f"fields-{field}-{op}", mode
                if key not in expected:
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
              f"- **Toolchains:** {manifest['lean_version']}; {manifest['rust_version']}; Plonky3 0.4.2 and arkworks 0.5.0. Rust release, LTO, one codegen unit; RUSTFLAGS={manifest['rustflags']!r}.",
              f"- **Source:** `{manifest['commit']}`; tracked files dirty: {manifest['dirty']}. Fixture SHA-256: `{manifest['fixture_sha256']}`.",
              f"- **Sampling:** {len(measurements)} paired runs, alternating Lean/Rust order; each case uses 50 ms warmup and 20 samples targeting 1 ms each. All {len(expected)} untimed result digests agree with Lean; Lean also checks its reference implementations.",
              "- **Workloads:** small-prime add/mul use 1,280 operations per batch; BN254 add/mul use 320. Throughput uses ten scalar lanes and nine final combining operations (outside the batch divisor), matching Lean. Inv/exp use 64 dependent steps of `inv(x + b)` / `(x + b)^0x5A5A5A5A`, so their times include one add per step. Only the final batch result is consumed. BN254 inversion uses CompPoly’s checked binary-GCD implementation and arkworks’ inverse.",
              "- **Shared host:** other jobs may contend for the CPU, SMT sibling, caches, or boost budget. These are observations under load, not isolated-machine speed claims.", ""]
    (out / "report.md").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=[*SUITES, "all"], default="small-prime")
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--skip-build", action="store_true", help="use already built executables")
    parser.add_argument("--cpu", type=int, help="logical CPU; default: first allowed CPU")
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--out-dir", type=Path)
    args = parser.parse_args()
    fields, groups, expected = selection(args.suite)
    if args.runs < 3:
        parser.error("use at least three paired runs")
    allowed = os.sched_getaffinity(0)
    cpu = min(allowed) if args.cpu is None else args.cpu
    if cpu not in allowed:
        parser.error(f"CPU {cpu} is outside allowed affinity")
    os.sched_setaffinity(0, {cpu})
    os.environ["LEAN_NUM_THREADS"] = "1"
    os.environ["CARGO_BUILD_JOBS"] = "1"
    out = (args.out_dir or ROOT / "bench/out" / time.strftime(f"fields-{args.suite}-%Y%m%d-%H%M%S")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    if not args.skip_build:
        subprocess.run(["lake", "build", "CompPolyBench", "CompPolyFieldFixtures"], cwd=ROOT, check=True)
        subprocess.run(["cargo", "build", "--release", "--locked", "-j", "1"], cwd=ROOT / "bench/rust", check=True)
    fixtures = out / "fixtures.jsonl"
    exported = [json.loads(line) for line in command(
        [str(ROOT / ".lake/build/bin/CompPolyFieldFixtures")]).splitlines()]
    selected = [row for row in exported if row["group_key"] in groups]
    if len(selected) != len(groups) or {row["group_key"] for row in selected} != set(groups):
        raise ValueError("missing or duplicate fixtures")
    fixtures.write_text("".join(json.dumps(row) + "\n" for row in selected))
    rust_exe = ROOT / "bench/rust/target/release/comppoly-field-bench"

    def run(language, label, validate):
        directory = out / label / language
        directory.mkdir(parents=True)
        if language == "lean":
            cmd = [str(ROOT / ".lake/build/bin/CompPolyBench"), "--medium", "--json-only",
                   "--groups", ",".join(groups), "--out-dir", str(directory)]
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
            return indexed(rows(files[0]), expected, lean=True)
        return indexed(rows(directory / "stdout.jsonl"), expected)

    compare(run("lean", "validation", True), run("rust", "validation", True))
    print(f"All {len(expected)} cases: Lean/Rust checksums and operation counts agree.", flush=True)
    if args.validate_only:
        return
    manifest = {
        "suite": args.suite,
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
    report(out, measurements, manifest, fields, expected)
    print(f"Report: {out / 'report.md'}")


if __name__ == "__main__":
    main()

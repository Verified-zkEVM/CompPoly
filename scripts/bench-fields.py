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
import tomllib
import bench_ntt

ROOT = Path(__file__).resolve().parents[1]
SUITES = {
    "small-prime": {"koalabear": ("KoalaBear", "Plonky3", ("add", "mul", "inv", "pow")),
                    "mersenne31": ("Mersenne31", "Plonky3", ("add", "mul", "inv", "pow")),
                    "goldilocks": ("Goldilocks", "Plonky3", ("add", "mul", "inv", "pow"))},
    "large-prime": {"bn254": ("BN254 scalar", "arkworks", ("add", "mul", "inv", "pow"))},
    "binary": {f"tower-bt{bits}": (f"Binary tower {bits}", "Binius", ("mul", "square", "inv"))
               for bits in (8, 64, 128)},
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


BUILD_RECORD = ROOT / ".lake/build/field-bench-build.json"
EXECUTABLES = (".lake/build/bin/CompPolyBench", ".lake/build/bin/CompPolyFieldFixtures",
               ".lake/build/bin/CompPolyNTTBench",
               "bench/rust/target/release/comppoly-field-bench")


def file_hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_context():
    # Include untracked sources and file contents: a dirty boolean is insufficient.
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"], cwd=ROOT
    ).decode().split("\0")
    digest = hashlib.sha256()
    for name in sorted(set(paths) - {""}):
        path = ROOT / name
        digest.update(name.encode() + b"\0")
        digest.update((file_hash(path) if path.is_file() else "missing").encode() + b"\0")
    cpu = Path("/proc/cpuinfo").read_text().split("\n\n", 1)[0]
    return {
        "commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(command(["git", "status", "--porcelain", "--untracked-files=normal"])),
        "source_sha256": digest.hexdigest(),
        "lean_version": command(["lake", "env", "lean", "--version"]),
        "rust_version": command(["rustc", "--version"], ROOT / "bench/rust"),
        "rustflags": os.environ.get("RUSTFLAGS", ""),
        "build_environment": {k: v for k, v in sorted(os.environ.items())
                              if k.startswith(("RUST", "CARGO", "LEAN", "LAKE"))
                              or k in ("CC", "CXX", "CFLAGS", "CXXFLAGS", "LDFLAGS", "PATH")},
        "native_cpu": [line for line in cpu.splitlines()
                       if line.startswith(("model name", "flags"))],
    }


def executable_hashes():
    return {name: file_hash(ROOT / name) for name in EXECUTABLES}


def verify_build(record, context):
    if record["context"] != context or record["executables"] != executable_hashes():
        raise ValueError("benchmark build does not match sources, toolchains, flags, CPU, or binaries")


def prepare_build(skip):
    context = build_context()
    if skip:
        try:
            record = json.loads(BUILD_RECORD.read_text())
            verify_build(record, context)
        except (OSError, ValueError, KeyError, TypeError) as error:
            raise SystemExit(f"Cannot reuse benchmark build: {error}. Run without --skip-build.")
        return record
    # A failed/interrupted build must not leave a valid-looking old record.
    BUILD_RECORD.unlink(missing_ok=True)
    subprocess.run(["lake", "build", "CompPolyBench", "CompPolyFieldFixtures", "CompPolyNTTBench"], cwd=ROOT, check=True)
    subprocess.run(["cargo", "build", "--release", "--locked", "-j", "1"], cwd=ROOT / "bench/rust", check=True)
    if build_context() != context:
        raise SystemExit("Sources or build settings changed during the build; rerun before measuring.")
    record = {"context": context, "executables": executable_hashes()}
    temporary = BUILD_RECORD.with_suffix(".tmp")
    temporary.write_text(json.dumps(record, indent=2) + "\n")
    temporary.replace(BUILD_RECORD)
    return record


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
             "Rust uses Plonky3 for small primes, arkworks for BN254 scalar arithmetic, and Binius for binary towers.", "",
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
              f"- **Toolchains:** {manifest['lean_version']}; {manifest['rust_version']}; Plonky3 0.4.2, arkworks 0.5.0, and Binius 0.2.0 (revision `{manifest['binius_revision']}`). Rust release, LTO, one codegen unit; RUSTFLAGS={manifest['rustflags']!r}.",
              f"- **Source:** `{manifest['commit']}`; tracked files dirty: {manifest['dirty']}. Fixture SHA-256: `{manifest['fixture_sha256']}`.",
              f"- **Sampling:** {len(measurements)} paired runs, alternating Lean/Rust order; each case uses 50 ms warmup and 20 samples targeting 1 ms each. All {len(expected)} untimed result digests agree with Lean; prime-field groups also check their reference implementations.",
              "- **Workloads:** small-prime add/mul use 1,280 operations per batch; BN254 add/mul use 320. Small-prime throughput uses a ten-lane ring and nine final combining operations; BN254 uses two independent chains, four rounds unrolled, with the same fixed operand as latency and one final combining operation. This configuration was selected manually on Rust and fixed identically in Lean. Combining operations are outside the batch divisor, matching Lean. Inv/exp use 64 dependent steps of `inv(x + b)` / `(x + b)^0x5A5A5A5A`, so their times include one add per step. Only the final batch result is consumed. BN254 inversion uses CompPoly’s checked binary-GCD implementation and arkworks’ inverse.",
              "- **Binary workloads:** Fan–Paar tower coefficients in little-endian bytes, with the same basis on both sides. Multiplication uses 64 dependent steps or two independent 32-step chains plus one final multiply (excluded from the divisor). Squaring uses 63 dependent squares, unrolled seven at a time; 63 is not a whole Frobenius cycle at any selected size. Inversion uses 64 steps of `inv(x XOR b)`, including the XOR. Only the final batch result is consumed. Scalar Binius field types are used, with supported CPU instructions enabled; there is no explicit packed-SIMD workload.",
              f"- **CPU instruction support:** {', '.join(manifest['cpu_features'])}. The archived Binius tower library is pinned because Binius64 uses different field representations.",
              "- **Shared host:** other jobs may contend for the CPU, SMT sibling, caches, or boost budget. These are observations under load, not isolated-machine speed claims.", ""]
    (out / "report.md").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=[*SUITES, "ntt", "all"], default="small-prime")
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--skip-build", action="store_true", help="reuse executables only if recorded build metadata and hashes match")
    parser.add_argument("--cpu", type=int, help="logical CPU; default: first allowed CPU")
    parser.add_argument("--cpus", help="distinct logical CPU IDs for the NTT (one worker each; SMT allowed), e.g. 8,9,10,11")
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--out-dir", type=Path)
    args = parser.parse_args()
    if args.runs < 3:
        parser.error("use at least three paired runs")
    allowed = os.sched_getaffinity(0)
    if args.suite == "ntt":
        import sys
        bench_ntt.run(args, sys.modules[__name__], allowed)
        return
    fields, groups, expected = selection(args.suite)
    cpu = min(allowed) if args.cpu is None else args.cpu
    if cpu not in allowed:
        parser.error(f"CPU {cpu} is outside allowed affinity")
    os.sched_setaffinity(0, {cpu})
    os.environ["LEAN_NUM_THREADS"] = "1"
    os.environ["CARGO_BUILD_JOBS"] = "1"
    os.environ.setdefault("RUSTFLAGS", "-C target-cpu=native")
    out = (args.out_dir or ROOT / "bench/out" / time.strftime(f"fields-{args.suite}-%Y%m%d-%H%M%S")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    build = prepare_build(args.skip_build)
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
    verify_build(build, build_context())
    if args.validate_only:
        if args.suite == "all":
            run_remaining_suites(args, allowed, out)
        return
    lock = tomllib.loads((ROOT / "bench/rust/Cargo.lock").read_text())
    binius = next(p for p in lock["package"] if p["name"] == "binius_field")
    cpu_flags = next(line.split(":", 1)[1].split() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("flags"))
    manifest = {
        "binius_revision": binius["source"].split("#")[1],
        "cpu_features": [f for f in ("sse2", "ssse3", "sse4_1", "avx", "avx2", "pclmulqdq", "gfni", "avx512f") if f in cpu_flags],
        "suite": args.suite,
        "commit": build["context"]["commit"],
        "dirty": build["context"]["dirty"],
        "build": build,
        "cpu": cpu, "logical_cpus": os.cpu_count(),
        "smt_siblings": Path(f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list").read_text().strip(),
        "cpu_model": next(line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("model name")),
        "memory_gib": int(Path("/proc/meminfo").read_text().splitlines()[0].split()[1]) / 1024**2,
        "os": platform.freedesktop_os_release()["PRETTY_NAME"], "kernel": platform.release(),
        "architecture": platform.machine(), "lean_version": build["context"]["lean_version"],
        "rust_version": build["context"]["rust_version"],
        "rustflags": build["context"]["rustflags"], "runs": args.runs,
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
    verify_build(build, build_context())
    manifest["load_end"] = os.getloadavg()
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    report(out, measurements, manifest, fields, expected)
    print(f"Report: {out / 'report.md'}")
    if args.suite == "all":
        run_remaining_suites(args, allowed, out)


def run_remaining_suites(args, allowed, out):
    import copy
    import sys
    ntt_args = copy.copy(args)
    ntt_args.out_dir = out / "ntt"
    ntt_args.skip_build = True
    bench_ntt.run(ntt_args, sys.modules[__name__], allowed)


if __name__ == "__main__":
    main()

"""Lean planned NTT versus the optimized Plonky3 API."""
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import time


def run(args, common, allowed):
    if args.cpus:
        cpus = [int(c) for c in args.cpus.split(",")]
    elif args.cpu is not None:
        cpus = [args.cpu]
    else:
        physical = {}
        for c in sorted(allowed):
            siblings = Path(f"/sys/devices/system/cpu/cpu{c}/topology/thread_siblings_list").read_text()
            physical.setdefault(siblings, c)
        preferred = list(physical.values()) + sorted(allowed - set(physical.values()))
        cpus = preferred[:min(16, 2 ** (len(preferred).bit_length() - 1))]
    workers = len(cpus)
    if not workers or workers & (workers - 1) or len(set(cpus)) != workers or not set(cpus) <= allowed:
        raise SystemExit("select a power-of-two number of distinct available CPUs")
    physical_cores = len({Path(f"/sys/devices/system/cpu/cpu{c}/topology/thread_siblings_list").read_text() for c in cpus})
    os.sched_setaffinity(0, {cpus[0]})
    os.environ["LEAN_NUM_THREADS"] = "1"
    os.environ["CARGO_BUILD_JOBS"] = "1"
    os.environ.setdefault("RUSTFLAGS", "-C target-cpu=native")
    out = (args.out_dir or common.ROOT / "bench/out" / time.strftime("ntt-%Y%m%d-%H%M%S")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    build = common.prepare_build(args.skip_build)
    lean = common.ROOT / ".lake/build/bin/CompPolyNTTBench"
    rust = common.ROOT / "bench/rust/target/release/comppoly-field-bench"
    os.sched_setaffinity(0, set(cpus))
    runtime_env = dict(os.environ, LEAN_NUM_THREADS=str(workers), RAYON_NUM_THREADS=str(workers))
    depth = int(runtime_env.get("NTT_DEPTH", "4"))
    if depth < 0:
        raise SystemExit("NTT_DEPTH must be nonnegative")
    rust_ntt = json.loads(subprocess.check_output([str(rust), "--ntt", "--info"], env=runtime_env, text=True))
    if rust_ntt["workers"] != workers:
        raise ValueError("Plonky3 worker count mismatch")
    # Tiny odd/even sizes exercise leftover radix-2 stages; only large sizes are timed.
    sizes = (12, 16, 20)
    fixtures = {}
    roots = {}
    for log_n in (0, 1, 3, 4, 5, *sizes):
        root = int(common.command([str(lean), "--root", str(log_n)]))
        roots[log_n] = root
        rng = random.Random(f"comppoly-ntt-koalabear-v1:{log_n}")
        path = out / f"koalabear-{log_n}.bin"
        with path.open("wb") as stream:
            stream.write(root.to_bytes(4, "little"))
            for i in range(2 * 2**log_n):
                value = (0, 1, 2130706432)[i] if i < 3 else rng.randrange(2130706433)
                stream.write(value.to_bytes(4, "little"))
        fixtures[log_n] = path
    manifest = {
        "build": build, "cpus": cpus, "workers": workers, "physical_cores": physical_cores, "runs": args.runs,
        "rust_ntt": rust_ntt, "lean_ntt": {"packed": {"implementation": "NTTFast.Packed.Plan", "task_depth": depth, "storage_externs": 2}, "externless": {"implementation": "NTTFast.NaturalPlan", "max_arithmetic_workers": workers, "serial_below_log_n": 18}, "leanc_args": ["-march=native"]}, "ordering": "natural input and output",
        "cpu_model": next(s.split(":", 1)[1].strip() for s in Path("/proc/cpuinfo").read_text().splitlines() if s.startswith("model name")),
        "memory_gib": int(Path("/proc/meminfo").read_text().splitlines()[0].split()[1]) / 1024**2,
        "os": platform.freedesktop_os_release()["PRETTY_NAME"], "kernel": platform.release(),
        "fixture_format": "field-coordinates-le-v1; canonical u32 root, then two arrays of 2^log_n coefficients",
        "roots": roots, "fixture_sha256": {str(k): common.file_hash(v) for k, v in fixtures.items()},
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "load_start": os.getloadavg(),
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    def measure(language, log_n, direction, label, validate):
        cmd = [str(rust), "--ntt"] if language == "rust" else [str(lean)]
        cmd += [str(fixtures[log_n]), str(log_n), direction, str(validate).lower()]
        env = dict(runtime_env, COMPPOLY_NTT_IMPL=language)
        result = subprocess.check_output(cmd, cwd=common.ROOT, env=env, text=True)
        (out / f"{label}-{log_n}-{direction}-{language}.jsonl").write_text(result)
        row = json.loads(result)
        if row["group_key"] != f"ntt-koalabear-{log_n}-{direction}" or row["work_units"] != 1:
            raise ValueError("unexpected NTT workload")
        return row

    results = {}
    for log_n in fixtures:
        for direction in ("forward", "inverse"):
            validated = [measure(lang, log_n, direction, "validation", True) for lang in ("packed", "externless", "rust")]
            expected = int(validated[0]["checksum"])
            if any(expected != int(row["checksum"]) for row in validated[1:]):
                raise ValueError(f"NTT checksum mismatch: log_n={log_n}, {direction}")
            print(f"Validated KoalaBear NTT: 2^{log_n}, {direction}", flush=True)
            if args.validate_only or log_n not in sizes:
                continue
            for i in range(args.runs):
                for language in (("packed", "externless", "rust") if i % 2 == 0 else ("rust", "externless", "packed")):
                    row = measure(language, log_n, direction, f"run-{i + 1}", False)
                    if int(row["checksum"]) != expected:
                        raise ValueError("NTT timing-run checksum mismatch")
                    results.setdefault((log_n, direction, language), []).append(statistics.median(row["samples_picos"]) / 1e9)
            print(f"Measured KoalaBear NTT: 2^{log_n}, {direction}", flush=True)
    common.verify_build(build, common.build_context())
    manifest["load_end"] = os.getloadavg()
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.validate_only:
        return
    lines = ["# KoalaBear NTT: Lean vs optimized Plonky3", "", "Milliseconds per complete transform; median of paired run medians ± between-run MAD. All implementations receive the same CPU budget. Both Lean pipelines are fully proved: packed Lean uses two native storage externs; externless Lean uses ordinary field arrays and parallel segments above 2^18 elements. Lean / Rust > 1 means Rust is faster.", "",
             "| Elements | Direction | Packed Lean | Externless Lean | Plonky3 | Packed / Rust | Externless / Rust |", "|---:|---|---:|---:|---:|---:|---:|"]
    for log_n in sizes:
        for direction in ("forward", "inverse"):
            medians, cells = [], []
            for language in ("packed", "externless", "rust"):
                samples = results[log_n, direction, language]
                median = statistics.median(samples)
                mad = statistics.median(abs(x - median) for x in samples)
                medians.append(median)
                cells.append(f"{median:.4f} ± {mad:.4f}")
            lines.append(f"| {2**log_n:,} | {direction} | {' | '.join(cells)} | {medians[0] / medians[2]:.2f}× | {medians[1] / medians[2]:.2f}× |")
    lines += ["", "## Machine and method", "",
              f"- {manifest['cpu_model']}; {manifest['memory_gib']:.1f} GiB; {manifest['os']}, kernel {manifest['kernel']}; {workers} workers on {physical_cores} physical cores, logical CPUs {cpus}.",
              f"- {build['context']['lean_version']}; {build['context']['rust_version']}; Rust flags {build['context']['rustflags']!r}. Source `{build['context']['commit']}`, dirty={build['context']['dirty']}.",
              f"- Packed Lean uses NTTFast.Packed.Plan with depth {depth}, fused input splitting, leaf normalization, one buffer assembly and a tiled decoder; its arithmetic module uses -march=native. Externless Lean uses the proved NTTFast.NaturalPlan parallel API, with independent aligned segments, a cached permutation, specialized normalization and bounds-proved machine-index butterflies. Rust calls {rust_ntt['implementation']} from p3-dft 0.4.2 directly, with packing width {rust_ntt['packing_width']}; native SIMD is enabled. Plonky3's parallel feature is enabled. This compares different algorithms implementing the same transform.",
              "- All three APIs use natural-order inputs and outputs. Forward maps coefficients to evaluations; inverse maps evaluations to coefficients, including 1/n normalization. The fixture root must equal both Lean's certified root and Plonky3's selected root.",
              "- Plan construction, twiddle tables, cached permutation indices and fixture decoding are outside timing. Input copying, arithmetic, output disposal and ordering conversions are timed, including each Lean ordering adapter. Inverse normalization is timed. Inputs remain reusable and unchanged in all three implementations.",
              "- Two deterministic inputs alternate to prevent result hoisting. Full output digests are checked outside timing; a four-position output sink is used inside timing. Native validation includes tiny odd/even sizes and zero/one/near-modulus coordinates.",
              f"- {args.runs} alternating three-way rounds, 50 ms warmup and 20 samples per invocation. Shared-host load {manifest['load_start']} → {manifest['load_end']}; other work may affect timings.", ""]
    (out / "report.md").write_text("\n".join(lines))
    print(f"Report: {out / 'report.md'}")

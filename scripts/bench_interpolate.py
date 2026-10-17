"""Lean coset interpolation versus Plonky3's `interpolate_coset`."""
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import time


IMPLS = ("packed", "reference", "rust")
P = 2130706433


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
        preferred = list(physical.values())
        cpus = preferred[:min(16, 2 ** (len(preferred).bit_length() - 1))]
    workers = len(cpus)
    if not workers or workers & (workers - 1) or len(set(cpus)) != workers or not set(cpus) <= allowed:
        raise SystemExit("select a power-of-two number of distinct available CPUs")
    physical_cores = len({Path(f"/sys/devices/system/cpu/cpu{c}/topology/thread_siblings_list").read_text() for c in cpus})
    os.sched_setaffinity(0, {cpus[0]})
    os.environ["LEAN_NUM_THREADS"] = "1"
    os.environ["CARGO_BUILD_JOBS"] = "1"
    os.environ.setdefault("RUSTFLAGS", "-C target-cpu=native")
    out = (args.out_dir or common.ROOT / "bench/out" / time.strftime("interpolate-%Y%m%d-%H%M%S")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    build = common.prepare_build(args.skip_build)
    lean = common.ROOT / ".lake/build/bin/CompPolyInterpolateBench"
    roots_exe = common.ROOT / ".lake/build/bin/CompPolyNTTBench"
    rust = common.ROOT / "bench/rust/target/release/comppoly-field-bench"
    os.sched_setaffinity(0, set(cpus))
    runtime_env = dict(os.environ, LEAN_NUM_THREADS=str(workers), RAYON_NUM_THREADS=str(workers))
    # Tiny shapes exercise single-row and narrow matrices; only the large ones are timed.
    timed = [(12, 1), (12, 16), (16, 1), (16, 16), (20, 1), (20, 16)]
    shapes = [(0, 1), (1, 1), (3, 2), (5, 3), *timed]
    fixtures = {}
    roots = {}
    for log_n, width in shapes:
        if log_n not in roots:
            roots[log_n] = int(common.command([str(roots_exe), "--root", str(log_n)]))
        rng = random.Random(f"comppoly-interpolate-koalabear-v1:{log_n}:{width}")
        path = out / f"koalabear-{log_n}-{width}.bin"
        with path.open("wb") as stream:
            # Root, shift (KoalaBear's multiplicative generator), two extension points, matrix.
            header = [roots[log_n], 3] + [rng.randrange(P) for _ in range(8)]
            for value in header + [rng.randrange(P) for _ in range(2 ** log_n * width)]:
                stream.write(value.to_bytes(4, "little"))
        fixtures[log_n, width] = path
    manifest = {
        "build": build, "cpus": cpus, "workers": workers, "physical_cores": physical_cores, "runs": args.runs,
        "packed": {"implementation": "KoalaBear.Fast.interpolateCosetPacked (parallel row ranges, packed words)", "leanc_args": ["-march=native"]},
        "reference": {"implementation": "KoalaBear.Fast.interpolateCoset (proved reference, sequential)", "leanc_args": ["-march=native"]},
        "rust": {"implementation": "p3_interpolation::interpolate_coset", "extension": "BinomialExtensionField<KoalaBear, 4>", "matrix": "RowMajorMatrix", "parallel": True},
        "cpu_model": next(s.split(":", 1)[1].strip() for s in Path("/proc/cpuinfo").read_text().splitlines() if s.startswith("model name")),
        "memory_gib": int(Path("/proc/meminfo").read_text().splitlines()[0].split()[1]) / 1024**2,
        "os": platform.freedesktop_os_release()["PRETTY_NAME"], "kernel": platform.release(),
        "fixture_format": "field-coordinates-le-v1; canonical u32 root, shift, two degree-4 points, then a row-major 2^log_n × width matrix",
        "roots": roots, "fixture_sha256": {f"{k[0]}-{k[1]}": common.file_hash(v) for k, v in fixtures.items()},
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "load_start": os.getloadavg(),
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    def measure(language, log_n, width, label, validate):
        cmd = [str(rust), "--interpolate"] if language == "rust" else [str(lean)]
        cmd += [str(fixtures[log_n, width]), str(log_n), str(width), str(validate).lower()]
        if language != "rust":
            cmd.append(language)
        result = subprocess.check_output(cmd, cwd=common.ROOT, env=runtime_env, text=True)
        (out / f"{label}-{log_n}-{width}-{language}.jsonl").write_text(result)
        row = json.loads(result)
        if row["group_key"] != f"interpolate-koalabear-{log_n}-{width}" or row["work_units"] != 1:
            raise ValueError("unexpected interpolation workload")
        return row

    results = {}
    for log_n, width in shapes:
        validated = [measure(lang, log_n, width, "validation", True) for lang in IMPLS]
        expected = int(validated[0]["checksum"])
        if any(expected != int(row["checksum"]) for row in validated[1:]):
            raise ValueError(f"interpolation checksum mismatch: log_n={log_n}, width={width}")
        print(f"Validated KoalaBear coset interpolation: 2^{log_n} × {width}", flush=True)
        if args.validate_only or (log_n, width) not in timed:
            continue
        for i in range(args.runs):
            for language in IMPLS[i % 3:] + IMPLS[:i % 3]:
                row = measure(language, log_n, width, f"run-{i + 1}", False)
                if int(row["checksum"]) != expected:
                    raise ValueError("interpolation timing-run checksum mismatch")
                results.setdefault((log_n, width, language), []).append(statistics.median(row["samples_picos"]) / 1e9)
        print(f"Measured KoalaBear coset interpolation: 2^{log_n} × {width}", flush=True)
    common.verify_build(build, common.build_context())
    manifest["load_end"] = os.getloadavg()
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.validate_only:
        return
    lines = ["# KoalaBear coset interpolation: Lean vs Plonky3", "", "Milliseconds per call; median of run medians ± between-run MAD. Each call evaluates every column of a row-major matrix of values on a coset at a degree-4 extension point. Lean / Plonky3 > 1 means Plonky3 is faster.", "",
             "| Rows | Columns | Lean packed | Lean reference | Plonky3 | Lean packed / Plonky3 |", "|---:|---:|---:|---:|---:|---:|"]
    for log_n, width in timed:
        medians, cells = [], []
        for language in IMPLS:
            samples = results[log_n, width, language]
            median = statistics.median(samples)
            mad = statistics.median(abs(x - median) for x in samples)
            medians.append(median)
            cells.append(f"{median:.4f} ± {mad:.4f}")
        lines.append(f"| {2**log_n:,} | {width} | {' | '.join(cells)} | {medians[0] / medians[2]:.2f}× |")
    lines += ["", "## Machine and method", "",
              f"- {manifest['cpu_model']}; {manifest['memory_gib']:.1f} GiB; {manifest['os']}, kernel {manifest['kernel']}; {workers} workers on {physical_cores} physical cores, logical CPUs {cpus}.",
              f"- {build['context']['lean_version']}; {build['context']['rust_version']}; Rust flags {build['context']['rustflags']!r}. Source `{build['context']['commit']}`, dirty={build['context']['dirty']}.",
              "- Lean packed runs `KoalaBear.Fast.interpolateCosetPacked` on the matrix's Montgomery words in a `ByteArray`: row ranges on parallel tasks, blocks of 512 rows with base-field weights from one inversion per block, lazily reduced column sums four columns at a time. `interpolateCosetPacked_eq` proves it equal to the reference.",
              "- Lean reference runs the proved `KoalaBear.Fast.interpolateCoset` sequentially: coset nodes by prefix products, one batch inversion over lists, the weights xᵢ/(z - xᵢ), one dot product per column, and a final scale by (zⁿ - sⁿ)/(n sⁿ). Plonky3 calls `p3_interpolation::interpolate_coset` 0.4.2 on a `RowMajorMatrix` with `BinomialExtensionField<KoalaBear, 4>`, with its parallel feature and native SIMD.",
              "- All compute the coset nodes, inversions and weights inside every call. Fixture decoding and matrix construction are outside timing.",
              "- Two deterministic points alternate to prevent result hoisting. Full output digests of all three implementations agree before timing, including single-row and narrow matrices.",
              f"- {args.runs} rounds in rotating order, 200 ms warmup and 50 samples per invocation. Shared-host load {manifest['load_start']} → {manifest['load_end']}; other work may affect timings.", ""]
    (out / "report.md").write_text("\n".join(lines))
    print(f"Report: {out / 'report.md'}")

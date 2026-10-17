"""Lean coset low-degree extension versus Plonky3's `coset_lde_batch`."""
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import time


LEAN = ("lean",)
RUST = ("dit-parallel", "recursive", "small-batch")
IMPLS = LEAN + RUST
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
    out = (args.out_dir or common.ROOT / "bench/out" / time.strftime("lde-%Y%m%d-%H%M%S")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    build = common.prepare_build(args.skip_build)
    lean = common.ROOT / ".lake/build/bin/CompPolyLdeBench"
    roots_exe = common.ROOT / ".lake/build/bin/CompPolyNTTBench"
    rust = common.ROOT / "bench/rust/target/release/comppoly-field-bench"
    os.sched_setaffinity(0, set(cpus))
    runtime_env = dict(os.environ, LEAN_NUM_THREADS=str(workers), RAYON_NUM_THREADS=str(workers))
    # (log height, width, added bits). Tiny shapes exercise single rows, odd heights and widths off
    # the tile sizes; only the large ones are timed.
    timed = [(14, 64, 1), (16, 8, 1), (16, 64, 1), (16, 256, 1), (18, 64, 1), (20, 8, 1), (20, 64, 1), (16, 64, 2)]
    shapes = [(0, 1, 1), (1, 3, 1), (3, 2, 2), (5, 9, 1), (6, 17, 2), (7, 4, 3), (9, 7, 1), *timed]
    fixtures = {}
    roots = {}
    for log_h, width, bits in shapes:
        log_n = log_h + bits
        if log_n not in roots:
            roots[log_n] = int(common.command([str(roots_exe), "--root", str(log_n)]))
        rng = random.Random(f"comppoly-lde-koalabear-v1:{log_h}:{width}:{bits}")
        path = out / f"koalabear-{log_h}-{width}-{bits}.bin"
        with path.open("wb") as stream:
            # Root of the extended domain, shift (KoalaBear's multiplicative generator), then two
            # row-major matrices.
            for value in [roots[log_n], 3]:
                stream.write(value.to_bytes(4, "little"))
            stream.write(b"".join(rng.randrange(P).to_bytes(4, "little") for _ in range(2 * 2 ** log_h * width)))
        fixtures[log_h, width, bits] = path
    manifest = {
        "build": build, "cpus": cpus, "workers": workers, "physical_cores": physical_cores, "runs": args.runs,
        "lean": {"implementation": "NTTFast.Packed.Native.cosetLde (row chunks)", "leanc_args": ["-march=native", "-mstackrealign"]},
        "rust": {"implementation": "TwoAdicSubgroupDft::coset_lde_batch(..).bit_reverse_rows().to_row_major_matrix()",
                 "dfts": ["Radix2DitParallel", "p3_monty_31::dft::RecursiveDft", "Radix2DFTSmallBatch"], "parallel": True},
        "cpu_model": next(s.split(":", 1)[1].strip() for s in Path("/proc/cpuinfo").read_text().splitlines() if s.startswith("model name")),
        "memory_gib": int(Path("/proc/meminfo").read_text().splitlines()[0].split()[1]) / 1024**2,
        "os": platform.freedesktop_os_release()["PRETTY_NAME"], "kernel": platform.release(),
        "fixture_format": "field-coordinates-le-v1; canonical u32 root of the extended domain, shift, then two row-major 2^log_h × width matrices",
        "roots": roots, "fixture_sha256": {f"{k[0]}-{k[1]}-{k[2]}": common.file_hash(v) for k, v in fixtures.items()},
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "load_start": os.getloadavg(),
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    def measure(impl, shape, label, validate):
        log_h, width, bits = shape
        args_ = [str(fixtures[shape]), str(log_h), str(width), str(bits)]
        if impl in RUST:
            cmd = [str(rust), "--lde", *args_, impl, str(validate).lower()]
        else:
            cmd = [str(lean), *args_, str(validate).lower()]
        result = subprocess.check_output(cmd, cwd=common.ROOT, env=runtime_env, text=True)
        (out / f"{label}-{log_h}-{width}-{bits}-{impl}.jsonl").write_text(result)
        row = json.loads(result)
        if row["group_key"] != f"lde-koalabear-{log_h}-{width}-{bits}" or row["work_units"] != 1:
            raise ValueError("unexpected LDE workload")
        return row

    results = {}
    for shape in shapes:
        validated = [measure(impl, shape, "validation", True) for impl in IMPLS]
        expected = int(validated[0]["checksum"])
        if any(expected != int(row["checksum"]) for row in validated[1:]):
            raise ValueError(f"LDE checksum mismatch: {shape}")
        print(f"Validated KoalaBear coset LDE: 2^{shape[0]} × {shape[1]}, blowup 2^{shape[2]}", flush=True)
        if args.validate_only or shape not in timed:
            continue
        for i in range(args.runs):
            for impl in IMPLS[i % len(IMPLS):] + IMPLS[:i % len(IMPLS)]:
                row = measure(impl, shape, f"run-{i + 1}", False)
                if int(row["checksum"]) != expected:
                    raise ValueError("LDE timing-run checksum mismatch")
                results.setdefault((shape, impl), []).append(statistics.median(row["samples_picos"]) / 1e9)
        print(f"Measured KoalaBear coset LDE: 2^{shape[0]} × {shape[1]}, blowup 2^{shape[2]}", flush=True)
    common.verify_build(build, common.build_context())
    manifest["load_end"] = os.getloadavg()
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.validate_only:
        return

    def cell(shape, impl):
        samples = results[shape, impl]
        median = statistics.median(samples)
        return median, f"{median:.2f} ± {statistics.median(abs(x - median) for x in samples):.2f}"

    lines = ["# KoalaBear coset low-degree extension: Lean vs Plonky3", "",
             "Milliseconds per call; median of run medians ± between-run MAD. Each call extends every column of a row-major matrix of values on the subgroup of order 2^log_h to the coset `3 · ⟨ω⟩` of order 2^(log_h + bits), and returns the rows in the bit-reversed order Plonky3's two-adic FRI commitment commits. Lean / Plonky3 > 1 means Plonky3 is faster; Plonky3 is its fastest DFT for the shape.", "",
             "| Rows | Columns | Blowup | Lean | DitParallel | Recursive | SmallBatch | Lean / Plonky3 |",
             "|---:|---:|---:|---:|---:|---:|---:|---:|"]
    for shape in timed:
        cells = {impl: cell(shape, impl) for impl in IMPLS}
        best = min(cells[impl][0] for impl in RUST)
        lines.append(f"| 2^{shape[0]} | {shape[1]} | 2^{shape[2]} | {' | '.join(cells[impl][1] for impl in IMPLS)} | "
                     f"{cells['lean'][0] / best:.2f}× |")
    lines += ["", "## Machine and method", "",
              f"- {manifest['cpu_model']}; {manifest['memory_gib']:.1f} GiB; {manifest['os']}, kernel {manifest['kernel']}; {workers} workers on {physical_cores} physical cores, logical CPUs {cpus}.",
              f"- {build['context']['lean_version']}; {build['context']['rust_version']}; Rust flags {build['context']['rustflags']!r}. Source `{build['context']['commit']}`, dirty={build['context']['dirty']}.",
              "- Lean runs `NTTFast.Packed.Native.cosetLde` on the matrix's Montgomery words in a `ByteArray`: tasks transpose row ranges into columns, run one unnormalized inverse transform per column and one DIF transform per column and coset of the scaled coefficients, whose DIF order is the commitment order, and transpose each block's rows as soon as its columns are done. It returns those row chunks, where Plonky3's threads write one buffer in place; joining the chunks (`joinRows`) would add one copy of the output.",
              "- Plonky3 0.4.2 runs `coset_lde_batch` on a `RowMajorMatrix` with each of `Radix2DitParallel`, Monty31's `RecursiveDft` and `Radix2DFTSmallBatch`, then `bit_reverse_rows().to_row_major_matrix()`, exactly as `TwoAdicFriPcs::commit`; for the first two the bit reversal is free. Parallel feature and native SIMD enabled.",
              "- Plans and twiddles are built outside timing (Plonky3's caches are warmed by the untimed digest pass). Input copies, transposes, all transforms and output assembly are timed.",
              "- Two deterministic matrices alternate. Full output digests of all four implementations agree before timing, including single-row, odd-height and narrow matrices.",
              f"- {args.runs} rounds in rotating order, 200 ms warmup and 50 samples per invocation. Shared-host load {manifest['load_start']} → {manifest['load_end']}; other work may affect timings.", ""]
    (out / "report.md").write_text("\n".join(lines))
    print(f"Report: {out / 'report.md'}")

"""One-polynomial, one-point suite for bench-fields.py."""
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import time

FIELDS = {
    "koalabear": ("KoalaBear", 4, 2130706433),
    "goldilocks": ("Goldilocks", 8, 18446744069414584321),
    "bn254": ("BN254 scalar", 32, 21888242871839275222246405745257275088548364400416034343698204186575808495617),
}


def run(args, common, allowed):
    if args.cpus:
        cpus = [int(c) for c in args.cpus.split(",")]
    else:
        physical = {}
        for c in sorted(allowed):
            key = Path(f"/sys/devices/system/cpu/cpu{c}/topology/thread_siblings_list").read_text()
            physical.setdefault(key, c)
        preferred = list(physical.values())
        count = min(16, 2 ** (len(preferred).bit_length() - 1))
        cpus = preferred[:count]
    workers = len(cpus)
    if workers < 2 or workers & (workers - 1) or len(set(cpus)) != workers:
        raise SystemExit("--cpus must list a power-of-two number of distinct CPUs (at least two)")
    if not set(cpus) <= allowed:
        raise SystemExit("--cpus includes unavailable CPUs")
    topology = [Path(f"/sys/devices/system/cpu/cpu{c}/topology/thread_siblings_list").read_text().strip() for c in cpus]
    physical_cores = len(set(topology))
    depth = workers.bit_length() - 1
    os.environ["LEAN_NUM_THREADS"] = "1"
    os.environ["CARGO_BUILD_JOBS"] = "1"
    os.environ.setdefault("RUSTFLAGS", "-C target-cpu=native")
    # Compile with one core, independently of the runtime worker budget.
    os.sched_setaffinity(0, {cpus[0]})
    out = (args.out_dir or common.ROOT / "bench/out" / time.strftime("poly-eval-%Y%m%d-%H%M%S")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    build = common.prepare_build(args.skip_build)
    fixtures = {}
    sizes = (2**12, 2**16, 2**20)
    for field, (_, width, modulus) in FIELDS.items():
        rng = random.Random(f"comppoly-poly-eval-v1:{field}")
        path = out / f"{field}.bin"
        with path.open("wb") as f:
            # First four values are points; the rest are coefficients, low degree first.
            for _ in range(max(sizes) + 4):
                f.write(rng.randrange(2, modulus).to_bytes(width, "little"))
        fixtures[field] = path
    manifest = {"build": build, "cpus": cpus, "workers": workers, "physical_cores": physical_cores, "smt_siblings": topology,
                "cpu_model": next(s.split(":", 1)[1].strip() for s in Path("/proc/cpuinfo").read_text().splitlines() if s.startswith("model name")),
                "memory_gib": int(Path("/proc/meminfo").read_text().splitlines()[0].split()[1]) / 1024**2,
                "os": platform.freedesktop_os_release()["PRETTY_NAME"], "kernel": platform.release(),
                "fixture_format": "field-coordinates-le-v1; four points, then coefficients; widths 4/8/32",
                "fixture_sha256": {f: common.file_hash(p) for f, p in fixtures.items()},
                "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "load_start": os.getloadavg(), "runs": args.runs}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    def measure(language, field, size, mode, label, validate):
        active = cpus[:1] if mode == "horner" else cpus
        env = dict(os.environ, LEAN_NUM_THREADS=str(workers if mode == "parallel" else 1))
        cmd = ["taskset", "-c", ",".join(map(str, active))]
        if language == "lean":
            cmd += [str(common.ROOT / ".lake/build/bin/CompPolyEvalBench")]
        else:
            cmd += [str(common.ROOT / "bench/rust/target/release/comppoly-field-bench"), "--poly-eval"]
        cmd += [field, str(fixtures[field]), str(size), str(depth), mode, str(validate).lower()]
        result = subprocess.check_output(cmd, cwd=common.ROOT, env=env, text=True)
        path = out / f"{label}-{field}-{size}-{mode}-{language}.jsonl"
        path.write_text(result)
        rows = [json.loads(line) for line in result.splitlines() if line.strip()]
        if len(rows) != 1:
            raise ValueError("expected one result")
        row = rows[0]
        if row["group_key"] != f"poly-eval-{field}-{size}" or row["work_units"] != 1:
            raise ValueError("unexpected workload")
        return row

    results = {}
    for field in FIELDS:
        for size in sizes:
            expected = None
            for mode in ("horner", "parallel"):
                for language in ("lean", "rust"):
                    row = measure(language, field, size, mode, "validation", True)
                    digest = int(row["checksum"])
                    if expected is None:
                        expected = digest
                    if digest != expected:
                        raise ValueError(f"checksum mismatch: {field}, {size}, {mode}, {language}")
            print(f"Validated {field}: {size} coefficients, Horner and {workers}-worker evaluation", flush=True)
            if args.validate_only:
                continue
            for iteration in range(args.runs):
                # Reverse both method and language order to limit ordering bias.
                cases = [(m, l) for m in ("horner", "parallel") for l in ("lean", "rust")]
                if iteration % 2:
                    cases.reverse()
                for mode, language in cases:
                    row = measure(language, field, size, mode, f"run-{iteration+1}", False)
                    if int(row["checksum"]) != expected:
                        raise ValueError("timing run checksum mismatch")
                    ms = statistics.median(row["samples_picos"]) / 1e9
                    results.setdefault((field, size, mode, language), []).append(ms)
            print(f"Measured {field}: {size} coefficients", flush=True)
    common.verify_build(build, common.build_context())
    manifest["load_end"] = os.getloadavg()
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.validate_only:
        return
    lines = ["# One polynomial, one point", "", "Milliseconds per complete steady-state evaluation; median of run medians ± between-run MAD. Lower is better. Rust is arkworks' stock `DensePolynomial::evaluate` (ark-poly 0.5.0, `parallel` feature). Lean / Rust compares parallel evaluation (>1 means Rust is faster).", "",
             f"| Field | Coefficients | Lean evalHorner (1 core) | Lean evalFast ({workers} workers) | ark-poly (1 thread) | ark-poly ({workers} threads) | Lean speedup | Lean / Rust |",
             "|---|---:|---:|---:|---:|---:|---:|---:|"]
    for field, (title, _, _) in FIELDS.items():
        for size in sizes:
            values = []
            medians = []
            for language, mode in (("lean", "horner"), ("lean", "parallel"), ("rust", "horner"), ("rust", "parallel")):
                runs = results[field, size, mode, language]
                median = statistics.median(runs)
                mad = statistics.median(abs(x - median) for x in runs)
                medians.append(median)
                values.append(f"{median:.4f} ± {mad:.4f}")
            lines.append(f"| {title} | {size:,} | " + " | ".join(values) + f" | {medians[0]/medians[1]:.2f}× | {medians[1]/medians[3]:.2f}× |")
    lines += ["", "## Machine and method", "",
              f"- {manifest['cpu_model']}; {manifest['memory_gib']:.1f} GiB; {manifest['os']}, kernel {manifest['kernel']}.",
              f"- {workers} workers on {physical_cores} physical cores via logical CPUs {cpus}; SMT siblings are {'included' if physical_cores < workers else 'not included'}. Horner uses CPU {cpus[0]}. Shared host; load {manifest['load_start']} → {manifest['load_end']}.",
              f"- {build['context']['lean_version']}; {build['context']['rust_version']}; Rust flags {build['context']['rustflags']!r}. Source `{build['context']['commit']}`, dirty={build['context']['dirty']}.",
              "- Rust evaluates with arkworks' stock `DensePolynomial::evaluate`: `ark_bn254::Fr` for BN254, and arkworks' generic Montgomery fields (`Fp64` from `#[derive(MontConfig)]`) for KoalaBear and Goldilocks, which arkworks does not ship; those two are not Plonky3-grade field arithmetic. Identical fixed-width input bytes in both languages.",
              "- Each call evaluates one prebuilt polynomial at one point. Four varying points prevent constant-result timing; there is no batched evaluation or shared power table.",
              "- Lean evalFast splits the coefficients into a binary tree of contiguous ranges, runs lazy-reduction Horner leaves and joins with square-and-multiply powers; evalHorner is CompPoly's existing sequential evaluator. ark-poly splits the coefficients into one chunk per Rayon thread, runs Horner on each and scales each chunk by a power of the point; with one thread it is plain Horner.",
              "- Task scheduling, per-call powers and joins are timed. Runtime worker pools and input decoding/construction are outside timing; validation/warmup also excludes first-use input-sharing costs. Lean uses Task.spawn; Rust uses a persistent Rayon pool of the selected size.",
              "- Four full-result digests agree across both languages and both methods before timing. Each run warms up for 200 ms, then takes 50 samples, in both languages; with the usual 50 ms, idle worker cores were often still at reduced clocks when timing began. Only the final evaluation result is consumed.", ""]
    (out / "report.md").write_text("\n".join(lines))
    print(f"Report: {out / 'report.md'}")

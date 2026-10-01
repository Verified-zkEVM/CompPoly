"""Matched scalar planned NTT suite for bench-fields.py."""
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import time


def run(args, common, allowed):
    cpu = min(allowed) if args.cpu is None else args.cpu
    if cpu not in allowed:
        raise SystemExit("--cpu is outside allowed affinity")
    os.sched_setaffinity(0, {cpu})
    os.environ["LEAN_NUM_THREADS"] = "1"
    os.environ["CARGO_BUILD_JOBS"] = "1"
    os.environ.setdefault("RUSTFLAGS", "-C target-cpu=native")
    out = (args.out_dir or common.ROOT / "bench/out" / time.strftime("ntt-%Y%m%d-%H%M%S")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    build = common.prepare_build(args.skip_build)
    lean = common.ROOT / ".lake/build/bin/CompPolyNTTBench"
    rust = common.ROOT / "bench/rust/target/release/comppoly-field-bench"
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
        "build": build, "cpu": cpu, "workers": 1, "runs": args.runs,
        "cpu_model": next(s.split(":", 1)[1].strip() for s in Path("/proc/cpuinfo").read_text().splitlines() if s.startswith("model name")),
        "memory_gib": int(Path("/proc/meminfo").read_text().splitlines()[0].split()[1]) / 1024**2,
        "os": platform.freedesktop_os_release()["PRETTY_NAME"], "kernel": platform.release(),
        "fixture_format": "field-coordinates-le-v1; canonical u32 root, then two arrays of 2^log_n coefficients",
        "roots": roots, "fixture_sha256": {str(k): common.file_hash(v) for k, v in fixtures.items()},
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "load_start": os.getloadavg(),
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    def measure(language, log_n, direction, label, validate):
        cmd = [str(lean)] if language == "lean" else [str(rust), "--ntt"]
        cmd += [str(fixtures[log_n]), str(log_n), direction, str(validate).lower()]
        result = subprocess.check_output(cmd, cwd=common.ROOT, text=True)
        (out / f"{label}-{log_n}-{direction}-{language}.jsonl").write_text(result)
        row = json.loads(result)
        if row["group_key"] != f"ntt-koalabear-{log_n}-{direction}" or row["work_units"] != 1:
            raise ValueError("unexpected NTT workload")
        return row

    results = {}
    for log_n in fixtures:
        for direction in ("forward", "inverse"):
            validated = [measure(lang, log_n, direction, "validation", True) for lang in ("lean", "rust")]
            expected = int(validated[0]["checksum"])
            if expected != int(validated[1]["checksum"]):
                raise ValueError(f"NTT checksum mismatch: log_n={log_n}, {direction}")
            print(f"Validated KoalaBear NTT: 2^{log_n}, {direction}", flush=True)
            if args.validate_only or log_n not in sizes:
                continue
            for i in range(args.runs):
                for language in (("lean", "rust") if i % 2 == 0 else ("rust", "lean")):
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
    lines = ["# KoalaBear planned NTT", "", "Milliseconds per complete transform; median of paired run medians ± between-run MAD. Both implementations use one thread. Lean / Rust > 1 means Rust is faster.", "",
             "| Elements | Direction | Lean | Rust | Lean / Rust |", "|---:|---|---:|---:|---:|"]
    for log_n in sizes:
        for direction in ("forward", "inverse"):
            medians, cells = [], []
            for language in ("lean", "rust"):
                samples = results[log_n, direction, language]
                median = statistics.median(samples)
                mad = statistics.median(abs(x - median) for x in samples)
                medians.append(median)
                cells.append(f"{median:.4f} ± {mad:.4f}")
            lines.append(f"| {2**log_n:,} | {direction} | {' | '.join(cells)} | {medians[0] / medians[1]:.2f}× |")
    lines += ["", "## Machine and method", "",
              f"- {manifest['cpu_model']}; {manifest['memory_gib']:.1f} GiB; {manifest['os']}, kernel {manifest['kernel']}; one thread pinned to CPU {cpu}.",
              f"- {build['context']['lean_version']}; {build['context']['rust_version']}; Rust flags {build['context']['rustflags']!r}. Source `{build['context']['commit']}`, dirty={build['context']['dirty']}.",
              "- Lean uses the existing proved NTTFast.Plan. Rust uses scalar Plonky3 KoalaBear arithmetic and the exact same radix-4 butterfly schedule, with radix-2 tails at odd log sizes. This is not Plonky3's packed or parallel FFT API.",
              "- Forward: natural-order coefficients to bit-reversed evaluations. Inverse: bit-reversed evaluations to natural-order coefficients, including 1/n normalization. Both use the same certified root exported by Lean.",
              "- Plan construction, twiddle tables and fixture decoding are outside timing. Each transform includes its mutable working-buffer copy, arithmetic and output disposal; inverse normalization is timed. Inputs remain reusable and unchanged on both sides.",
              "- Two deterministic inputs alternate to prevent result hoisting. Full output digests are checked outside timing; a four-position output sink is used inside timing. Native validation includes tiny odd/even sizes and zero/one/near-modulus coordinates.",
              f"- {args.runs} alternating Lean/Rust pairs, 50 ms warmup and 20 samples per invocation. Shared-host load {manifest['load_start']} → {manifest['load_end']}; other work may affect timings.", ""]
    (out / "report.md").write_text("\n".join(lines))
    print(f"Report: {out / 'report.md'}")

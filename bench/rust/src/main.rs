//! Scalar Plonky3 counterparts of CompPolyBench.Fields.Arith.
use p3_field::PrimeField64;
use serde::Deserialize;
use serde_json::json;
use std::{hint::black_box, time::Instant};

#[derive(Deserialize)]
struct Fixture {
    group_key: String,
    field: String,
    operation: String,
    modulus: u64,
    inputs: Vec<u64>,
    exponent: u64,
    latency_rounds: usize,
    throughput_rounds: usize,
}

#[inline(always)]
fn apply8<F: Copy>(op: impl Fn(F) -> F, x: F) -> F {
    op(op(op(op(op(op(op(op(x))))))))
}

#[inline(always)]
fn latency<F: Copy>(op: impl Fn(F) -> F + Copy, rounds: usize, mut x: F) -> F {
    for _ in 0..rounds / 64 {
        x = apply8(|x| apply8(op, x), x);
    }
    x
}

#[inline(always)]
fn throughput<F: Copy>(op: impl Fn(F, F) -> F, rounds: usize, xs: [F; 10]) -> F {
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h, mut i, mut j] = xs;
    macro_rules! step {
        () => {
            (a, b, c, d, e, f, g, h, i, j) = (
                op(a, b),
                op(b, c),
                op(c, d),
                op(d, e),
                op(e, f),
                op(f, g),
                op(g, h),
                op(h, i),
                op(i, j),
                op(j, a),
            );
        };
    }
    for _ in 0..rounds / 4 {
        step!();
        step!();
        step!();
        step!();
    }
    op(op(op(op(a, b), op(c, d)), op(op(e, f), op(g, h))), op(i, j))
}

fn measure<F: PrimeField64>(
    fixture: &Fixture,
    mode: &str,
    units: usize,
    validate_only: bool,
    run: impl Fn(usize) -> F,
) {
    // Strong agreement check is separate from timing. One canonical result per chain.
    let checksum = (0..64).fold(0u128, |acc, i| {
        (acc * 16777619 + run(i).as_canonical_u64() as u128 + 97) % 18446744073709551557
    });
    let mut samples = Vec::new();
    let mut sink = 0u64;
    let mut iters = 1usize;
    let mut warmup_iterations = 0usize;
    if !validate_only {
        let mut time = |iterations: usize| {
            let start = Instant::now();
            for i in 0..iterations {
                // Opaque seed index prevents caching a finite pool of chain outputs.
                let result = black_box(run(black_box(i))).as_canonical_u64();
                sink = (sink ^ result)
                    .wrapping_mul(0x9E3779B97F4A7C15)
                    .rotate_left(27);
            }
            black_box(sink);
            start.elapsed().as_nanos() as u64
        };
        let mut elapsed = 0;
        for _ in 0..40 {
            let nanos = time(iters).max(1);
            elapsed += nanos;
            warmup_iterations += iters;
            if elapsed >= 50_000_000 {
                iters = ((1_000_000u128 * iters as u128) / nanos as u128).max(1) as usize;
                break;
            }
            iters *= 2;
        }
        for _ in 0..20 {
            samples.push(time(iters) as f64 * 1000.0 / iters as f64);
        }
    }
    println!(
        "{}",
        json!({
            "group_key": fixture.group_key, "mode": mode, "work_units": units,
            "checksum": checksum.to_string(), "samples_picos": samples,
            "iters_per_sample": iters, "warmup_iterations": warmup_iterations,
            "sink_digest": sink.to_string(),
        })
    );
}

fn field<F: PrimeField64>(fixture: &Fixture, validate_only: bool) {
    assert_eq!(fixture.modulus, F::ORDER_U64);
    assert_eq!(fixture.inputs.len(), 64);
    assert!(fixture.inputs.iter().all(|x| *x < fixture.modulus));
    assert_eq!(fixture.exponent, 0x5A5A5A5A);
    assert_eq!(fixture.throughput_rounds, 128);
    let binary = matches!(fixture.operation.as_str(), "add" | "mul");
    assert_eq!(fixture.latency_rounds, if binary { 1280 } else { 64 });
    let xs: Vec<F> = fixture.inputs.iter().map(|x| F::from_u64(*x)).collect();
    let b = black_box(xs[0]);
    macro_rules! binary {
        ($op:expr) => {{
            measure(fixture, "latency", 1280, validate_only, |i| {
                latency(|x| $op(x, b), 1280, xs[i % 64])
            });
            measure(fixture, "throughput", 1280, validate_only, |i| {
                throughput($op, 128, std::array::from_fn(|k| xs[(i + k) % 64]))
            });
        }};
    }
    match fixture.operation.as_str() {
        "add" => binary!(|a, b| a + b),
        "mul" => binary!(|a, b| a * b),
        "inv" => measure(fixture, "latency", 64, validate_only, |i| {
            latency(|x| (x + b).try_inverse().unwrap_or(F::ZERO), 64, xs[i % 64])
        }),
        "pow" => measure(fixture, "latency", 64, validate_only, |i| {
            latency(|x| (x + b).exp_u64(0x5A5A5A5A), 64, xs[i % 64])
        }),
        _ => panic!("unsupported operation"),
    }
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert!(
        args.len() == 1 || (args.len() == 2 && args[1] == "--validate-only"),
        "usage: comppoly-field-bench FIXTURES.jsonl [--validate-only]"
    );
    let source = std::fs::read_to_string(&args[0]).expect("read fixtures");
    for line in source.lines() {
        let fixture: Fixture = serde_json::from_str(line).expect("parse fixture");
        match fixture.field.as_str() {
            "koalabear" => field::<p3_koala_bear::KoalaBear>(&fixture, args.len() == 2),
            "mersenne31" => field::<p3_mersenne_31::Mersenne31>(&fixture, args.len() == 2),
            "goldilocks" => field::<p3_goldilocks::Goldilocks>(&fixture, args.len() == 2),
            _ => panic!("unsupported field"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chain_shapes_match_simple_loops() {
        let modulus = 101u128;
        for multiply in [false, true] {
            let op = |a, b| {
                if multiply {
                    (a * b) % modulus
                } else {
                    (a + b) % modulus
                }
            };
            let mut expected = 7;
            for _ in 0..1280 {
                expected = op(expected, 13);
            }
            assert_eq!(latency(|x| op(x, 13), 1280, 7), expected);
            let initial = std::array::from_fn(|i| i as u128 + 1);
            let mut lanes = initial;
            for _ in 0..128 {
                lanes = std::array::from_fn(|i| op(lanes[i], lanes[(i + 1) % 10]));
            }
            let expected = lanes.into_iter().reduce(op).unwrap();
            assert_eq!(throughput(op, 128, initial), expected);
        }
    }
}

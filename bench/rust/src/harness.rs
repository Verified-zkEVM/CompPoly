use crate::Fixture;
use serde_json::json;
use std::{hint::black_box, time::Instant};

pub const DIGEST_MODULUS: u128 = 18446744073709551557;

/// Canonical digest outside timing; cheap native-word observation after each batch.
pub trait BenchValue {
    fn checksum(self) -> u128;
    fn sink(self) -> u64;
}

#[inline(always)]
fn apply8<F: Copy>(op: impl Fn(F) -> F, x: F) -> F {
    op(op(op(op(op(op(op(op(x))))))))
}

#[inline(always)]
pub fn latency<F: Copy>(op: impl Fn(F) -> F + Copy, rounds: usize, mut x: F) -> F {
    for _ in 0..rounds / 64 {
        x = apply8(|x| apply8(op, x), x);
    }
    x
}

#[inline(always)]
pub fn throughput<F: Copy>(op: impl Fn(F, F) -> F, rounds: usize, xs: [F; 10]) -> F {
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

/// Two independent chains with a shared fixed operand, for multi-limb fields.
#[inline(always)]
pub fn throughput_pair<F: Copy>(
    op: impl Fn(F, F) -> F,
    constant: F,
    rounds: usize,
    mut a: F,
    mut b: F,
) -> F {
    macro_rules! step {
        () => {
            a = op(a, constant);
            b = op(b, constant);
        };
    }
    for _ in 0..rounds / 4 {
        step!();
        step!();
        step!();
        step!();
    }
    op(a, b)
}

pub fn measure<F: BenchValue>(
    fixture: &Fixture,
    mode: &str,
    units: usize,
    validate_only: bool,
    run: impl Fn(usize) -> F,
) {
    measure_workload(
        &fixture.group_key,
        mode,
        units,
        64,
        MEDIUM,
        validate_only,
        run,
    );
}

/// Warmup and sample count, matching the Lean harness's presets of the same name.
#[derive(Clone, Copy)]
pub struct Budget {
    pub warmup_nanos: u64,
    pub samples: usize,
}
pub const MEDIUM: Budget = Budget {
    warmup_nanos: 50_000_000,
    samples: 20,
};
/// Parallel workloads need the longer warmup: idle worker cores take a few hundred
/// milliseconds of load before the frequency governor raises their clocks.
pub const LARGE: Budget = Budget {
    warmup_nanos: 200_000_000,
    samples: 50,
};

/// Shared timing and digest machinery, with workload-specific validation period.
pub fn measure_workload<F: BenchValue>(
    key: &str,
    mode: &str,
    units: usize,
    period: usize,
    budget: Budget,
    validate_only: bool,
    run: impl Fn(usize) -> F,
) {
    // Strong agreement check is separate from timing. One canonical result per chain.
    let checksum = (0..period).fold(0u128, |acc, i| {
        (acc * 16777619 + run(i).checksum() + 97) % 18446744073709551557
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
                let result = black_box(run(black_box(i))).sink();
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
            if elapsed >= budget.warmup_nanos {
                iters = ((1_000_000u128 * iters as u128) / nanos as u128).max(1) as usize;
                break;
            }
            iters *= 2;
        }
        for _ in 0..budget.samples {
            samples.push(time(iters) as f64 * 1000.0 / iters as f64);
        }
    }
    println!(
        "{}",
        json!({
            "group_key": key, "mode": mode, "work_units": units,
            "checksum": checksum.to_string(), "samples_picos": samples,
            "iters_per_sample": iters, "warmup_iterations": warmup_iterations,
            "sink_digest": sink.to_string(),
        })
    );
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
            let mut a = 7;
            let mut b = 19;
            for _ in 0..160 {
                a = op(a, 13);
                b = op(b, 13);
            }
            assert_eq!(throughput_pair(op, 13, 160, 7, 19), op(a, b));
        }
    }
}

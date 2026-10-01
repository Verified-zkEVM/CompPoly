//! CompPoly NTTFast.Plan's exact scalar radix-4 schedule over Plonky3 KoalaBear.
use crate::harness::{measure_workload, BenchValue, DIGEST_MODULUS};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::KoalaBear as F;

struct Plan {
    log_n: usize,
    forward: Vec<Vec<F>>,
    inverse: Vec<Vec<F>>,
    n_inv: F,
}

fn powers(root: F, log_n: usize) -> Vec<Vec<F>> {
    (0..log_n)
        .map(|stage| {
            let half = 1 << stage;
            let step = root.exp_u64((1 << (log_n - stage - 1)) as u64);
            let mut w = F::ONE;
            (0..half)
                .map(|_| {
                    let old = w;
                    w *= step;
                    old
                })
                .collect()
        })
        .collect()
}

impl Plan {
    fn new(root: F, log_n: usize) -> Self {
        Self {
            log_n,
            forward: powers(root, log_n),
            inverse: powers(root.inverse(), log_n),
            n_inv: F::from_u32(1 << log_n).inverse(),
        }
    }

    /// Natural input to bit-reversed output, matching Plan.forwardImpl.
    fn forward(&self, input: &[F]) -> Vec<F> {
        let mut a = input.to_vec();
        for pass in 0..self.log_n / 2 {
            let high = self.log_n - 1 - 2 * pass;
            let low = high - 1;
            let quarter = 1 << low;
            for block in a.chunks_exact_mut(4 * quarter) {
                for j in 0..quarter {
                    let [x0, x1, x2, x3] = [
                        block[j],
                        block[j + quarter],
                        block[j + 2 * quarter],
                        block[j + 3 * quarter],
                    ];
                    let a0 = x0 + x2;
                    let a2 = self.forward[high][j] * (x0 - x2);
                    let a1 = x1 + x3;
                    let a3 = self.forward[high][j + quarter] * (x1 - x3);
                    block[j] = a0 + a1;
                    block[j + quarter] = self.forward[low][j] * (a0 - a1);
                    block[j + 2 * quarter] = a2 + a3;
                    block[j + 3 * quarter] = self.forward[low][j] * (a2 - a3);
                }
            }
        }
        if self.log_n % 2 == 1 {
            for block in a.chunks_exact_mut(2) {
                let [u, v] = [block[0], block[1]];
                block[0] = u + v;
                block[1] = self.forward[0][0] * (u - v);
            }
        }
        a
    }

    /// Bit-reversed input to natural output, including the final 1/n scaling pass.
    fn inverse(&self, input: &[F]) -> Vec<F> {
        let mut a = input.to_vec();
        for pass in 0..self.log_n / 2 {
            let low = 2 * pass;
            let high = low + 1;
            let quarter = 1 << low;
            for block in a.chunks_exact_mut(4 * quarter) {
                for j in 0..quarter {
                    let [x0, x1, x2, x3] = [
                        block[j],
                        block[j + quarter],
                        block[j + 2 * quarter],
                        block[j + 3 * quarter],
                    ];
                    let t1 = self.inverse[low][j] * x1;
                    let t3 = self.inverse[low][j] * x3;
                    let a0 = x0 + t1;
                    let a1 = x0 - t1;
                    let a2 = x2 + t3;
                    let a3 = x2 - t3;
                    let u2 = self.inverse[high][j] * a2;
                    let u3 = self.inverse[high][j + quarter] * a3;
                    block[j] = a0 + u2;
                    block[j + quarter] = a1 + u3;
                    block[j + 2 * quarter] = a0 - u2;
                    block[j + 3 * quarter] = a1 - u3;
                }
            }
        }
        if self.log_n % 2 == 1 {
            let half = 1 << (self.log_n - 1);
            for j in 0..half {
                let u = a[j];
                let t = self.inverse[self.log_n - 1][j] * a[j + half];
                a[j] = u + t;
                a[j + half] = u - t;
            }
        }
        a.into_iter().map(|v| self.n_inv * v).collect()
    }
}

struct Output(Vec<F>);
impl BenchValue for Output {
    fn checksum(self) -> u128 {
        self.0.into_iter().fold(0, |acc, x| {
            (acc * 16777619 + x.as_canonical_u32() as u128 + 97) % DIGEST_MODULUS
        })
    }
    fn sink(self) -> u64 {
        let n = self.0.len();
        let mix = |acc: u64, x: u64| (acc ^ x).wrapping_mul(0x9E3779B97F4A7C15).rotate_left(27);
        [n / 3, 2 * n / 3, n - 1]
            .into_iter()
            .fold(self.0[0].as_canonical_u32() as u64, |acc, i| {
                mix(acc, self.0[i].as_canonical_u32() as u64)
            })
    }
}

pub fn run(args: &[String]) {
    assert_eq!(
        args.len(),
        4,
        "--ntt FIXTURE LOG_N forward|inverse true|false"
    );
    let log_n: usize = args[1].parse().unwrap();
    assert!(log_n <= 24);
    let n = 1 << log_n;
    assert!(matches!(args[2].as_str(), "forward" | "inverse"));
    let validate: bool = args[3].parse().unwrap();
    let bytes = std::fs::read(&args[0]).unwrap();
    assert_eq!(bytes.len(), 4 * (1 + 2 * n));
    let values: Vec<_> = bytes
        .chunks_exact(4)
        .map(|v| {
            let v = u32::from_le_bytes(v.try_into().unwrap());
            assert!(v < 2130706433);
            F::from_u32(v)
        })
        .collect();
    let root = values[0];
    assert_eq!(root.exp_u64(n as u64), F::ONE);
    if n > 1 {
        assert_ne!(root.exp_u64((n / 2) as u64), F::ONE);
    }
    let plan = Plan::new(root, log_n);
    let inputs = [&values[1..n + 1], &values[n + 1..]];
    measure_workload(
        &format!("ntt-koalabear-{log_n}-{}", args[2]),
        &args[2],
        1,
        2,
        validate,
        |i| {
            Output(if args[2] == "forward" {
                plan.forward(inputs[i % 2])
            } else {
                plan.inverse(inputs[i % 2])
            })
        },
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::TwoAdicField;

    // Independent O(n²) oracle catches root direction, bit ordering and normalization errors.
    #[test]
    fn schedule_matches_direct_transform() {
        for log_n in 0..=5 {
            let n = 1 << log_n;
            let root = F::two_adic_generator(log_n);
            let plan = Plan::new(root, log_n);
            let input: Vec<_> = (0..n)
                .map(|i| F::from_u32((i * i + 7 * i + 3) as u32))
                .collect();
            let output = plan.forward(&input);
            for (i, actual) in output.iter().enumerate() {
                let k = if log_n == 0 {
                    0
                } else {
                    i.reverse_bits() >> (usize::BITS as usize - log_n)
                };
                let expected: F = input
                    .iter()
                    .enumerate()
                    .map(|(j, x)| *x * root.exp_u64((j * k) as u64))
                    .sum();
                assert_eq!(*actual, expected);
            }
            assert_eq!(plan.inverse(&output), input);
        }
    }
}

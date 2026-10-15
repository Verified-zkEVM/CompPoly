//! Existing optimized Plonky3 NTT API, with natural-order inputs and outputs.
use crate::harness::{measure_workload, BenchValue, DIGEST_MODULUS, LARGE};
use p3_dft::{Radix2DFTSmallBatch, TwoAdicSubgroupDft};
use p3_field::{Field, PackedValue, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_koala_bear::KoalaBear as F;

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
    if args == ["--info"] {
        println!(
            "{}",
            serde_json::json!({
                "implementation": "p3_dft::Radix2DFTSmallBatch<KoalaBear>",
                "packing_width": <F as Field>::Packing::WIDTH,
                "workers": rayon::current_num_threads(),
            })
        );
        return;
    }
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
    assert_eq!(
        root,
        F::two_adic_generator(log_n),
        "fixture/library root mismatch"
    );
    // Precompute forward and inverse twiddles before validation and timing.
    // Both the parallel feature and native packed arithmetic are enabled.
    let plan = Radix2DFTSmallBatch::<F>::new(n);
    let inputs = [&values[1..n + 1], &values[n + 1..]];
    measure_workload(
        &format!("ntt-koalabear-{log_n}-{}", args[2]),
        &args[2],
        1,
        2,
        LARGE,
        validate,
        |i| {
            Output(if args[2] == "forward" {
                plan.dft(inputs[i % 2].to_vec())
            } else {
                plan.idft(inputs[i % 2].to_vec())
            })
        },
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    // Check the selected API's root, natural ordering and normalization contract.
    #[test]
    fn library_api_matches_direct_transform() {
        for log_n in 0..=5 {
            let n = 1 << log_n;
            let root = F::two_adic_generator(log_n);
            let plan = Radix2DFTSmallBatch::<F>::new(n);
            let input: Vec<_> = (0..n)
                .map(|i| F::from_u32((i * i + 7 * i + 3) as u32))
                .collect();
            let output = plan.dft(input.clone());
            for (k, actual) in output.iter().enumerate() {
                let expected: F = input
                    .iter()
                    .enumerate()
                    .map(|(j, x)| *x * root.exp_u64((j * k) as u64))
                    .sum();
                assert_eq!(*actual, expected);
            }
            assert_eq!(plan.idft(output), input);
        }
    }
}

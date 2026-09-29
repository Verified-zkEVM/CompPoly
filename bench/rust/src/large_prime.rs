//! BN254 scalar field Fr (not the curve's base field Fq).
use crate::{
    harness::{latency, measure, throughput, BenchValue, DIGEST_MODULUS},
    Fixture,
};
use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, BigInteger, Field, PrimeField};
use std::hint::black_box;

impl BenchValue for Fr {
    fn checksum(self) -> u128 {
        // Match Lean's full canonical Nat modulo the digest prime; do not truncate.
        self.into_bigint()
            .to_bytes_le()
            .iter()
            .rev()
            .fold(0, |n, b| (n * 256 + *b as u128) % DIGEST_MODULUS)
    }

    fn sink(self) -> u64 {
        // Same low/high 32-bit Montgomery words as Lean's eight-limb sink.
        // No conversion out of Montgomery form or serialization during timing.
        (self.0 .0[0] & 0xffff_ffff) ^ (self.0 .0[3] >> 32)
    }
}

pub fn run(fixture: &Fixture, validate_only: bool) {
    assert_eq!(
        fixture.group_key,
        format!("fields-bn254-{}", fixture.operation)
    );
    assert_eq!(fixture.modulus, Fr::MODULUS.to_bytes_le());
    fixture.validate_inputs(32);
    let binary = matches!(fixture.operation.as_str(), "add" | "mul");
    assert_eq!(fixture.latency_rounds, if binary { 320 } else { 64 });
    assert_eq!(fixture.throughput_rounds, 32);
    assert_eq!(fixture.exponent, 0x5A5A5A5A);
    let xs: Vec<Fr> = fixture
        .inputs
        .iter()
        .map(|x| Fr::from_le_bytes_mod_order(x))
        .collect();
    let b = black_box(xs[0]);
    macro_rules! binary {
        ($op:expr) => {{
            measure(fixture, "latency", 320, validate_only, |i| {
                latency(|x| $op(x, b), 320, xs[i % 64])
            });
            measure(fixture, "throughput", 320, validate_only, |i| {
                throughput($op, 32, std::array::from_fn(|k| xs[(i + k) % 64]))
            });
        }};
    }
    match fixture.operation.as_str() {
        "add" => binary!(|a, b| a + b),
        "mul" => binary!(|a, b| a * b),
        "inv" => measure(fixture, "latency", 64, validate_only, |i| {
            latency(|x| (x + b).inverse().unwrap_or(Fr::ZERO), 64, xs[i % 64])
        }),
        "pow" => measure(fixture, "latency", 64, validate_only, |i| {
            latency(|x| (x + b).pow([0x5A5A5A5Au64]), 64, xs[i % 64])
        }),
        _ => panic!("unsupported operation"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_boundary_roundtrips() {
        for x in [Fr::from(0u64), Fr::from(1u64), -Fr::from(1u64)] {
            let bytes = x.into_bigint().to_bytes_le();
            assert!(crate::canonical(&bytes, &Fr::MODULUS.to_bytes_le()));
            assert_eq!(Fr::from_le_bytes_mod_order(&bytes), x);
        }
        // p-1 is far above u64: check that the digest sees the whole integer.
        let expected = Fr::MODULUS
            .to_bytes_le()
            .iter()
            .rev()
            .fold(0u128, |n, b| (n * 256 + *b as u128) % DIGEST_MODULUS);
        assert_eq!(
            (-Fr::from(1u64)).checksum(),
            (expected + DIGEST_MODULUS - 1) % DIGEST_MODULUS
        );
    }
}

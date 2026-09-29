//! BN254 scalar field Fr (not the curve's base field Fq).
use crate::{
    harness::{latency, measure, throughput, BenchValue, DIGEST_MODULUS},
    Fixture,
};
use ark_bn254::Fr;
use ark_ff::{BigInteger, PrimeField};
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
    assert_eq!(fixture.group_key, "fields-bn254-mul");
    assert_eq!(fixture.operation, "mul");
    assert_eq!(fixture.modulus, Fr::MODULUS.to_bytes_le());
    fixture.validate_inputs(32);
    assert_eq!(fixture.latency_rounds, 320);
    assert_eq!(fixture.throughput_rounds, 32);
    let xs: Vec<Fr> = fixture
        .inputs
        .iter()
        .map(|x| Fr::from_le_bytes_mod_order(x))
        .collect();
    let b = black_box(xs[0]);
    measure(fixture, "latency", 320, validate_only, |i| {
        latency(|x| x * b, 320, xs[i % 64])
    });
    measure(fixture, "throughput", 320, validate_only, |i| {
        throughput(|a, b| a * b, 32, std::array::from_fn(|k| xs[(i + k) % 64]))
    });
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

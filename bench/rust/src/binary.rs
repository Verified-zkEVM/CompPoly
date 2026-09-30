//! Fan–Paar tower coefficients, matching CompPoly's ConcreteBinaryTower basis.
use crate::{
    harness::{latency, measure, throughput_pair, BenchValue, DIGEST_MODULUS},
    Fixture,
};
use binius_field::{BinaryField128b, BinaryField64b, BinaryField8b, Field};
use std::hint::black_box;

macro_rules! value {
    ($field:ty) => {
        impl BenchValue for $field {
            fn checksum(self) -> u128 {
                // Reduce the complete coordinate word, including both 128-bit limbs.
                self.val() as u128 % DIGEST_MODULUS
            }
            fn sink(self) -> u64 {
                let word = self.val() as u128;
                word as u64 ^ (word >> 64) as u64
            }
        }
    };
}
value!(BinaryField8b);
value!(BinaryField64b);
value!(BinaryField128b);

#[inline(always)]
fn square_chain<F: Field>(mut x: F) -> F {
    for _ in 0..9 {
        x = x
            .square()
            .square()
            .square()
            .square()
            .square()
            .square()
            .square();
    }
    x
}

fn run_field<F: Field + BenchValue>(fixture: &Fixture, validate_only: bool, xs: Vec<F>) {
    let constant = black_box(xs[0]);
    match fixture.operation.as_str() {
        "mul" => {
            measure(fixture, "latency", 64, validate_only, |i| {
                latency(|x| x * constant, 64, xs[i % 64])
            });
            measure(fixture, "throughput", 64, validate_only, |i| {
                throughput_pair(|a, b| a * b, constant, 32, xs[i % 64], xs[(i + 1) % 64])
            });
        }
        "square" => measure(fixture, "latency", 63, validate_only, |i| {
            square_chain(xs[i % 64])
        }),
        "inv" => measure(fixture, "latency", 64, validate_only, |i| {
            latency(|x| (x + constant).invert_or_zero(), 64, xs[i % 64])
        }),
        _ => panic!("unsupported binary operation"),
    }
}

pub fn run(fixture: &Fixture, validate_only: bool) {
    let bits = match fixture.field.as_str() {
        "tower-bt8" => 8,
        "tower-bt64" => 64,
        "tower-bt128" => 128,
        _ => panic!("unsupported tower"),
    };
    assert_eq!(fixture.encoding, "field-coordinates-le-v1");
    assert_eq!(fixture.basis, "fan-paar-tower");
    assert!(fixture.modulus.is_empty());
    assert_eq!(
        fixture.group_key,
        format!("fields-{}-{}", fixture.field, fixture.operation)
    );
    assert_eq!(fixture.inputs.len(), 64);
    assert_eq!(fixture.exponent, 0);
    assert_eq!(fixture.throughput_rounds, 32);
    assert_eq!(
        fixture.latency_rounds,
        if fixture.operation == "square" { 63 } else { 64 }
    );
    let words: Vec<u128> = fixture
        .inputs
        .iter()
        .map(|bytes| {
            assert_eq!(bytes.len(), bits / 8);
            let mut word = [0; 16];
            word[..bytes.len()].copy_from_slice(bytes);
            let word = u128::from_le_bytes(word);
            assert!(word >= 2, "trivial multiplication input");
            word
        })
        .collect();
    match bits {
        8 => run_field(
            fixture,
            validate_only,
            words
                .into_iter()
                .map(|x| BinaryField8b::new(x as u8))
                .collect(),
        ),
        64 => run_field(
            fixture,
            validate_only,
            words
                .into_iter()
                .map(|x| BinaryField64b::new(x as u64))
                .collect(),
        ),
        128 => run_field(
            fixture,
            validate_only,
            words.into_iter().map(BinaryField128b::new).collect(),
        ),
        _ => unreachable!(),
    }
}

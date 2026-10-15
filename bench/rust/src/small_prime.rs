use crate::{
    harness::{latency, measure, throughput, BenchValue},
    Fixture,
};
use p3_field::PrimeField64;
use std::hint::black_box;

macro_rules! value {
    ($field:ty) => {
        impl BenchValue for $field {
            fn checksum(self) -> u128 {
                self.as_canonical_u64() as u128
            }
            fn sink(self) -> u64 {
                self.as_canonical_u64()
            }
        }
    };
}
value!(p3_koala_bear::KoalaBear);
value!(p3_mersenne_31::Mersenne31);
value!(p3_goldilocks::Goldilocks);

pub fn run<F: PrimeField64 + BenchValue>(fixture: &Fixture, validate_only: bool) {
    let width = if F::ORDER_U64 > u32::MAX as u64 { 8 } else { 4 };
    assert_eq!(fixture.modulus, F::ORDER_U64.to_le_bytes()[..width]);
    assert_eq!(fixture.inputs.len(), 64);
    fixture.validate_inputs(width);
    assert_eq!(fixture.exponent, 0x5A5A5A5A);
    assert_eq!(fixture.throughput_rounds, 128);
    let binary = matches!(fixture.operation.as_str(), "add" | "mul");
    assert_eq!(fixture.latency_rounds, if binary { 1280 } else { 64 });
    let xs: Vec<F> = fixture
        .inputs
        .iter()
        .map(|x| {
            F::from_u64(u64::from_le_bytes({
                let mut word = [0; 8];
                word[..width].copy_from_slice(x);
                word
            }))
        })
        .collect();
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

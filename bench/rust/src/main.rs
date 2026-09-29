//! Matched CompPoly field workloads using Plonky3 and arkworks.
mod harness;
mod large_prime;
mod small_prime;
use serde::Deserialize;

#[derive(Deserialize)]
struct Fixture {
    encoding: String,
    group_key: String,
    field: String,
    operation: String,
    modulus: Vec<u8>,
    inputs: Vec<Vec<u8>>,
    exponent: u64,
    latency_rounds: usize,
    throughput_rounds: usize,
}

impl Fixture {
    fn validate_inputs(&self, width: usize) {
        assert_eq!(self.encoding, "canonical-le-bytes-v1");
        assert_eq!(self.modulus.len(), width);
        assert_eq!(self.inputs.len(), 64);
        for bytes in &self.inputs {
            assert!(canonical(bytes, &self.modulus), "noncanonical field input");
        }
    }
}

/// Fixed-width, little-endian integer in [0, modulus), never silently reduced.
fn canonical(bytes: &[u8], modulus: &[u8]) -> bool {
    bytes.len() == modulus.len() && bytes.iter().rev().cmp(modulus.iter().rev()).is_lt()
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
            "koalabear" => small_prime::run::<p3_koala_bear::KoalaBear>(&fixture, args.len() == 2),
            "mersenne31" => {
                small_prime::run::<p3_mersenne_31::Mersenne31>(&fixture, args.len() == 2)
            }
            "goldilocks" => {
                small_prime::run::<p3_goldilocks::Goldilocks>(&fixture, args.len() == 2)
            }
            "bn254-scalar" => large_prime::run(&fixture, args.len() == 2),
            _ => panic!("unsupported field"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_encoding_checks_width_order_and_range() {
        assert!(canonical(&[255, 0], &[0, 1]));
        assert!(canonical(&[0, 0], &[0, 1]));
        assert!(!canonical(&[0, 1], &[0, 1]));
        assert!(!canonical(&[1, 1], &[0, 1]));
        assert!(!canonical(&[1], &[0, 1]));
    }
}

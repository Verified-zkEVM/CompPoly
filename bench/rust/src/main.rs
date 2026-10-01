//! Matched CompPoly field workloads using Plonky3 and arkworks.
mod binary;
mod harness;
mod large_prime;
mod ntt;
mod poly_eval;
mod small_prime;
use serde::Deserialize;

#[derive(Deserialize)]
struct Fixture {
    encoding: String,
    basis: String,
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
        assert_eq!(self.encoding, "field-coordinates-le-v1");
        assert_eq!(self.basis, "canonical-integer");
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
    if args.first().map(String::as_str) == Some("--poly-eval") {
        poly_eval::run(&args[1..]);
        return;
    }
    if args.first().map(String::as_str) == Some("--ntt") {
        ntt::run(&args[1..]);
        return;
    }
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
            "tower-bt8" | "tower-bt64" | "tower-bt128" => binary::run(&fixture, args.len() == 2),
            _ => panic!("unsupported field"),
        }
    }
}

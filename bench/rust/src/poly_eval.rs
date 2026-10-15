//! One polynomial at one point with arkworks' stock `DensePolynomial::evaluate`.
use crate::harness::{measure_workload, BenchValue, LARGE};
use ark_ff::{Fp64, MontBackend, MontConfig, PrimeField};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use std::hint::black_box;

// arkworks ships no KoalaBear or Goldilocks; these are its generic Montgomery fields.
#[derive(MontConfig)]
#[modulus = "2130706433"]
#[generator = "3"]
pub struct KoalaBearConfig;
type KoalaBear = Fp64<MontBackend<KoalaBearConfig, 1>>;

#[derive(MontConfig)]
#[modulus = "18446744069414584321"]
#[generator = "7"]
pub struct GoldilocksConfig;
type Goldilocks = Fp64<MontBackend<GoldilocksConfig, 1>>;

macro_rules! value64 {
    ($field:ty) => {
        impl BenchValue for $field {
            fn checksum(self) -> u128 {
                self.into_bigint().0[0] as u128
            }
            fn sink(self) -> u64 {
                // Montgomery word; no conversion during timing.
                self.0 .0[0]
            }
        }
    };
}
value64!(KoalaBear);
value64!(Goldilocks);

fn bench<F: PrimeField + BenchValue>(
    field: &str,
    bytes: &[u8],
    width: usize,
    n: usize,
    workers: usize,
    mode: &str,
    validate: bool,
) {
    assert!(bytes.len() >= (n + 4) * width);
    let values: Vec<F> = bytes
        .chunks_exact(width)
        .take(n + 4)
        .map(F::from_le_bytes_mod_order)
        .collect();
    let points = values[..4].to_vec();
    let poly = DensePolynomial::from_coefficients_vec(values[4..].to_vec());
    let key = format!("poly-eval-{field}-{n}");
    // Persistent worker pool, like Lean's runtime; one thread gives the stock Horner path.
    let threads = if mode == "horner" { 1 } else { workers };
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build()
        .unwrap();
    measure_workload(&key, mode, 1, 4, LARGE, validate, |i| {
        let x = black_box(points[i % 4]);
        pool.install(|| black_box(&poly).evaluate(&x))
    });
}

pub fn run(args: &[String]) {
    assert_eq!(
        args.len(),
        6,
        "FIELD FIXTURE COUNT LOG_WORKERS MODE VALIDATE"
    );
    let field = args[0].as_str();
    let n: usize = args[2].parse().unwrap();
    let depth: usize = args[3].parse().unwrap();
    let mode = args[4].as_str();
    assert!(matches!(mode, "horner" | "parallel"));
    assert!(depth <= 8);
    let validate = args[5] == "true";
    let bytes = std::fs::read(&args[1]).unwrap();
    match field {
        "koalabear" => bench::<KoalaBear>(field, &bytes, 4, n, 1 << depth, mode, validate),
        "goldilocks" => bench::<Goldilocks>(field, &bytes, 8, n, 1 << depth, mode, validate),
        "bn254" => bench::<ark_bn254::Fr>(field, &bytes, 32, n, 1 << depth, mode, validate),
        _ => panic!("unsupported field"),
    }
}

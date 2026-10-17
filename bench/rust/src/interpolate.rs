//! Plonky3's stock `interpolate_coset`: evaluate the columns of a matrix of coset values at an
//! extension-field point.
use crate::harness::{measure_workload, BenchValue, DIGEST_MODULUS, LARGE};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_interpolation::interpolate_coset;
use p3_koala_bear::KoalaBear as F;
use p3_matrix::dense::RowMajorMatrix;

type E = BinomialExtensionField<F, 4>;

struct Output(Vec<E>);
impl BenchValue for Output {
    fn checksum(self) -> u128 {
        self.0.iter().fold(0, |acc, e| {
            let coords: &[F] = e.as_basis_coefficients_slice();
            coords.iter().fold(acc, |acc, x| {
                (acc * 16777619 + x.as_canonical_u32() as u128 + 97) % DIGEST_MODULUS
            })
        })
    }
    fn sink(self) -> u64 {
        let coords: &[F] = self.0[0].as_basis_coefficients_slice();
        coords[0].as_canonical_u32() as u64 ^ ((self.0.len() as u64) << 32)
    }
}

pub fn run(args: &[String]) {
    assert_eq!(
        args.len(),
        4,
        "--interpolate FIXTURE LOG_N WIDTH true|false"
    );
    let log_n: usize = args[1].parse().unwrap();
    assert!(log_n <= 24);
    let n = 1 << log_n;
    let width: usize = args[2].parse().unwrap();
    let validate: bool = args[3].parse().unwrap();
    let bytes = std::fs::read(&args[0]).unwrap();
    assert_eq!(bytes.len(), 4 * (10 + n * width));
    let words: Vec<F> = bytes
        .chunks_exact(4)
        .map(|v| {
            let v = u32::from_le_bytes(v.try_into().unwrap());
            assert!(v < 2130706433);
            F::from_u32(v)
        })
        .collect();
    assert_eq!(
        words[0],
        F::two_adic_generator(log_n),
        "fixture/library root mismatch"
    );
    let shift = words[1];
    let point = |k: usize| E::from_basis_coefficients_slice(&words[2 + 4 * k..6 + 4 * k]).unwrap();
    let points = [point(0), point(1)];
    let matrix = RowMajorMatrix::new(words[10..].to_vec(), width);
    measure_workload(
        &format!("interpolate-koalabear-{log_n}-{width}"),
        "interpolate",
        1,
        2,
        LARGE,
        validate,
        |i| Output(interpolate_coset(&matrix, shift, points[i % 2])),
    );
}

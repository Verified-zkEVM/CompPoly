//! Plonky3's stock `coset_lde_batch`, returning rows in the bit-reversed order that
//! `TwoAdicFriPcs::commit` commits.
use crate::harness::{measure_workload, BenchValue, DIGEST_MODULUS, LARGE};
use p3_dft::{Radix2DFTSmallBatch, Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_koala_bear::KoalaBear as F;
use p3_matrix::bitrev::BitReversibleMatrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_monty_31::dft::RecursiveDft;

struct Output(RowMajorMatrix<F>);
impl BenchValue for Output {
    fn checksum(self) -> u128 {
        self.0.values.iter().fold(0, |acc, x| {
            (acc * 16777619 + x.as_canonical_u32() as u128 + 97) % DIGEST_MODULUS
        })
    }
    fn sink(self) -> u64 {
        let v = &self.0.values;
        v[0].as_canonical_u32() as u64 ^ ((v[v.len() - 1].as_canonical_u32() as u64) << 32)
    }
}

/// The LDE in commitment order, as `TwoAdicFriPcs::commit` computes it.
fn committed<D: TwoAdicSubgroupDft<F>>(
    dft: &D,
    m: RowMajorMatrix<F>,
    added_bits: usize,
    shift: F,
) -> Output {
    Output(dft.coset_lde_batch(m, added_bits, shift).bit_reverse_rows().to_row_major_matrix())
}

pub fn run(args: &[String]) {
    assert_eq!(
        args.len(),
        6,
        "--lde FIXTURE LOG_H WIDTH ADDED_BITS dit-parallel|recursive|small-batch true|false"
    );
    let log_h: usize = args[1].parse().unwrap();
    let width: usize = args[2].parse().unwrap();
    let added_bits: usize = args[3].parse().unwrap();
    assert!(log_h + added_bits <= 24);
    let h = 1 << log_h;
    let validate: bool = args[5].parse().unwrap();
    let bytes = std::fs::read(&args[0]).unwrap();
    assert_eq!(bytes.len(), 4 * (2 + 2 * h * width));
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
        F::two_adic_generator(log_h + added_bits),
        "fixture/library root mismatch"
    );
    let shift = words[1];
    let inputs = [
        RowMajorMatrix::new(words[2..2 + h * width].to_vec(), width),
        RowMajorMatrix::new(words[2 + h * width..].to_vec(), width),
    ];
    let name = format!("lde-koalabear-{log_h}-{width}-{added_bits}");
    // Twiddles are precomputed (or cached by the warmup) outside timing; the input copy each
    // call consumes is timed, like the NTT comparison's.
    let measure = |run: &dyn Fn(RowMajorMatrix<F>) -> Output| {
        measure_workload(&name, "lde", 1, 2, LARGE, validate, |i| run(inputs[i % 2].clone()))
    };
    match args[4].as_str() {
        "dit-parallel" => {
            let dft = Radix2DitParallel::<F>::default();
            measure(&|m| committed(&dft, m, added_bits, shift))
        }
        "recursive" => {
            let dft = RecursiveDft::<F>::new(h << added_bits);
            measure(&|m| committed(&dft, m, added_bits, shift))
        }
        "small-batch" => {
            let dft = Radix2DFTSmallBatch::<F>::new(h << added_bits);
            measure(&|m| committed(&dft, m, added_bits, shift))
        }
        other => panic!("unknown DFT {other}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::Field;

    // Committed row r of every DFT is column j's interpolant at shift · ω^bitrev(r).
    #[test]
    fn committed_rows_are_bit_reversed_coset_evaluations() {
        for (log_h, width, added_bits) in [(0, 1, 1), (1, 3, 1), (3, 2, 2), (4, 5, 1)] {
            let h = 1usize << log_h;
            let log_n = log_h + added_bits;
            let values: Vec<F> = (0..h * width).map(|k| F::from_u32(7 * k as u32 + 1)).collect();
            let m = RowMajorMatrix::new(values.clone(), width);
            let shift = F::from_u32(3);
            let wh = F::two_adic_generator(log_h);
            let w = F::two_adic_generator(log_n);
            let outputs = [
                committed(&Radix2DitParallel::<F>::default(), m.clone(), added_bits, shift).0,
                committed(&RecursiveDft::<F>::new(h << added_bits), m.clone(), added_bits, shift).0,
                committed(&Radix2DFTSmallBatch::<F>::new(h << added_bits), m, added_bits, shift).0,
            ];
            for r in 0..h << added_bits {
                let i = r.reverse_bits() >> (usize::BITS as usize - log_n);
                let x = shift * w.exp_u64(i as u64);
                for j in 0..width {
                    // Lagrange interpolation of column j on ⟨ω_h⟩, evaluated at x.
                    let mut sum = F::ZERO;
                    for k in 0..h {
                        let xk = wh.exp_u64(k as u64);
                        let mut basis = F::ONE;
                        for l in (0..h).filter(|&l| l != k) {
                            let xl = wh.exp_u64(l as u64);
                            basis *= (x - xl) * (xk - xl).inverse();
                        }
                        sum += basis * values[k * width + j];
                    }
                    for out in &outputs {
                        assert_eq!(out.values[r * width + j], sum, "log_h={log_h} r={r} j={j}");
                    }
                }
            }
        }
    }
}

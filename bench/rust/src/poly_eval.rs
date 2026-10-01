//! One polynomial at one point: identical Horner leaves and binary partition tree to Lean.
use crate::harness::{measure_workload, BenchValue};
use ark_ff::PrimeField;
use p3_field::PrimeCharacteristicRing;
use std::{
    hint::black_box,
    ops::{Add, Mul},
};

fn power<F: Copy + Mul<Output = F>>(x: F, n: usize, one: F) -> F {
    match n {
        0 => one,
        1 => x,
        _ => {
            let half = power(x, n / 2, one);
            let square = half * half;
            if n % 2 == 0 {
                square
            } else {
                square * x
            }
        }
    }
}

fn horner<F: Copy + Add<Output = F> + Mul<Output = F>>(p: &[F], x: F, zero: F) -> F {
    p.iter().rev().fold(zero, |acc, &a| acc * x + a)
}

fn parallel<F: Copy + Send + Sync + Add<Output = F> + Mul<Output = F>>(
    p: &[F],
    x: F,
    depth: usize,
    zero: F,
    one: F,
) -> F {
    if depth == 0 || p.len() < 2 {
        return horner(p, x, zero);
    }
    let mid = p.len() / 2;
    let (low, high) = rayon::join(
        || parallel(&p[..mid], x, depth - 1, zero, one),
        || parallel(&p[mid..], x, depth - 1, zero, one),
    );
    high * power(x, mid, one) + low
}

fn bench<F: BenchValue + Send + Sync + Add<Output = F> + Mul<Output = F>>(
    field: &str,
    values: Vec<F>,
    n: usize,
    depth: usize,
    mode: &str,
    validate: bool,
    zero: F,
    one: F,
) {
    let points = &values[..4];
    let p = black_box(&values[4..n + 4]);
    let key = format!("poly-eval-{field}-{n}");
    // Persistent worker pool, like Lean's runtime. Scheduling and joins stay inside timing.
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1 << depth)
        .build()
        .unwrap();
    measure_workload(&key, mode, 1, 4, validate, |i| {
        let x = black_box(points[i % 4]);
        if mode == "horner" {
            horner(p, x, zero)
        } else {
            pool.install(|| parallel(p, x, depth, zero, one))
        }
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
    macro_rules! go {
        ($f:ty, $width:expr, $decode:expr, $zero:expr, $one:expr) => {{
            assert!(bytes.len() >= (n + 4) * $width);
            let values: Vec<$f> = bytes
                .chunks_exact($width)
                .take(n + 4)
                .map($decode)
                .collect();
            bench(field, values, n, depth, mode, validate, $zero, $one);
        }};
    }
    match field {
        "koalabear" => {
            type F = p3_koala_bear::KoalaBear;
            go!(
                F,
                4,
                |b: &[u8]| F::from_u32(u32::from_le_bytes(b.try_into().unwrap())),
                F::ZERO,
                F::ONE
            );
        }
        "goldilocks" => {
            type F = p3_goldilocks::Goldilocks;
            go!(
                F,
                8,
                |b: &[u8]| F::from_u64(u64::from_le_bytes(b.try_into().unwrap())),
                F::ZERO,
                F::ONE
            );
        }
        "bn254" => {
            use ark_ff::{AdditiveGroup, Field};
            type F = ark_bn254::Fr;
            go!(F, 32, F::from_le_bytes_mod_order, F::ZERO, F::ONE);
        }
        "tower-bt128" => {
            use binius_field::Field;
            type F = binius_field::BinaryField128b;
            go!(
                F,
                16,
                |b: &[u8]| F::new(u128::from_le_bytes(b.try_into().unwrap())),
                F::ZERO,
                F::ONE
            );
        }
        _ => panic!("unsupported field"),
    }
}

//! One polynomial at one point: identical Horner leaves and binary partition tree to Lean.
use crate::harness::{measure_workload, BenchValue};
use ark_ff::PrimeField;
use p3_field::PrimeCharacteristicRing;
use std::{
    hint::black_box,
    ops::{Add, Mul},
};

// Parallel leaves may retain redundant residues; input conversion stays outside timing.
trait EvalKernel: Copy + Send + Sync {
    type Raw: Copy + Send + Sync;
    fn raw(self) -> Self::Raw;
    fn leaf(p: &[Self::Raw], x: Self::Raw, zero: Self) -> Self;
}

macro_rules! canonical_kernel {
    ($f:ty) => {
        impl EvalKernel for $f {
            type Raw = Self;
            fn raw(self) -> Self {
                self
            }
            fn leaf(p: &[Self], x: Self, zero: Self) -> Self {
                horner(p, x, zero)
            }
        }
    };
}
impl EvalKernel for p3_koala_bear::KoalaBear {
    type Raw = u32;
    fn raw(self) -> u32 {
        use p3_field::PrimeField32;
        ((self.as_canonical_u32() as u64 * (1u64 << 32)) % 0x7f000001) as u32
    }
    fn leaf(p: &[u32], x: u32, _: Self) -> Self {
        const P: u64 = 0x7f000001;
        let x = x as u64;
        let mut acc = 0u32;
        for &a in p.iter().rev() {
            let product = acc as u64 * x;
            let m = (product as u32).wrapping_mul(0x7effffff) as u64;
            let quotient = (product + m * P) >> 32;
            let sum = quotient + a as u64;
            acc = (if sum < 2 * P { sum } else { sum - P }) as u32;
        }
        if acc as u64 >= P {
            acc -= P as u32;
        }
        // Plonky3's public serde format stores Montgomery words. The accumulator
        // is canonical here; this typed deserializer wraps it without arithmetic.
        use serde::Deserialize;
        Self::deserialize(serde::de::value::U32Deserializer::<serde::de::value::Error>::new(acc))
            .expect("u32 deserialization is infallible")
    }
}
impl EvalKernel for ark_bn254::Fr {
    type Raw = [u64; 4];
    fn raw(self) -> Self::Raw {
        self.0 .0
    }
    fn leaf(p: &[Self::Raw], x: Self::Raw, _: Self) -> Self {
        const Q: [u64; 4] = [
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ];
        let mut acc = [0u64; 4];
        for a in p.iter().rev() {
            // Same four CIOS rounds as Lean, with the canonical point as multiplicand.
            let mut t = [0u64; 5];
            for &bi in &acc {
                let mut s = [0u64; 6];
                let mut carry = 0u64;
                for j in 0..4 {
                    let v = t[j] as u128 + x[j] as u128 * bi as u128 + carry as u128;
                    s[j] = v as u64;
                    carry = (v >> 64) as u64;
                }
                let top = t[4] as u128 + carry as u128;
                s[4] = top as u64;
                s[5] = (top >> 64) as u64;
                let m = s[0].wrapping_mul(0xc2e1f593efffffff);
                carry = 0;
                for j in 0..4 {
                    let v = s[j] as u128 + m as u128 * Q[j] as u128 + carry as u128;
                    if j != 0 {
                        t[j - 1] = v as u64;
                    }
                    carry = (v >> 64) as u64;
                }
                let top = s[4] as u128 + carry as u128;
                t[3] = top as u64;
                t[4] = s[5] + (top >> 64) as u64;
            }
            let mut carry = 0u64;
            for j in 0..4 {
                let sum = t[j] as u128 + a[j] as u128 + carry as u128;
                acc[j] = sum as u64;
                carry = (sum >> 64) as u64;
            }
        }
        for _ in 0..2 {
            let mut d = [0; 4];
            let mut borrow = false;
            for j in 0..4 {
                let (v, b1) = acc[j].overflowing_sub(Q[j]);
                let (v, b2) = v.overflowing_sub(borrow as u64);
                d[j] = v;
                borrow = b1 || b2;
            }
            if !borrow {
                acc = d;
            }
        }
        Self::new_unchecked(ark_ff::BigInt(acc))
    }
}
canonical_kernel!(binius_field::BinaryField128b);

#[inline(always)]
fn gold_add(a: u64, b: u64) -> u64 {
    let (sum, carry) = a.overflowing_add(b);
    if carry {
        sum.wrapping_add(0xffff_ffff)
    } else {
        sum
    }
}

#[inline(never)]
fn gold_borrow(lo: u64, hi_hi: u64, hi_lo: u64) -> u64 {
    gold_add(
        lo.wrapping_sub(hi_hi).wrapping_sub(0xffff_ffff),
        hi_lo * 0xffff_ffff,
    )
}

#[inline(always)]
fn gold_mul(a: u64, b: u64) -> u64 {
    let product = a as u128 * b as u128;
    let lo = product as u64;
    let hi = (product >> 64) as u64;
    let hi_hi = hi >> 32;
    let hi_lo = hi & 0xffff_ffff;
    if lo < hi_hi {
        gold_borrow(lo, hi_hi, hi_lo)
    } else {
        gold_add(lo - hi_hi, (hi << 32).wrapping_sub(hi_lo))
    }
}

impl EvalKernel for p3_goldilocks::Goldilocks {
    type Raw = u64;
    fn raw(self) -> u64 {
        use p3_field::PrimeField64;
        self.as_canonical_u64()
    }
    fn leaf(p: &[u64], x: u64, _: Self) -> Self {
        let acc = p
            .iter()
            .rev()
            .fold(0, |acc, &a| gold_add(gold_mul(acc, x), a));
        const P: u64 = 0xffff_ffff_0000_0001;
        Self::new(if acc < P { acc } else { acc - P })
    }
}

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

fn parallel<F: EvalKernel + Add<Output = F> + Mul<Output = F>>(
    p: &[F::Raw],
    x: F,
    raw_x: F::Raw,
    depth: usize,
    zero: F,
    one: F,
) -> F {
    if depth == 0 || p.len() < 2 {
        return F::leaf(p, raw_x, zero);
    }
    let mid = p.len() / 2;
    let (low, high) = rayon::join(
        || parallel(&p[..mid], x, raw_x, depth - 1, zero, one),
        || parallel(&p[mid..], x, raw_x, depth - 1, zero, one),
    );
    high * power(x, mid, one) + low
}

fn bench<F: BenchValue + EvalKernel + Add<Output = F> + Mul<Output = F>>(
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
    let raw_points: Vec<F::Raw> = points.iter().map(|x| x.raw()).collect();
    let lazy: Vec<F::Raw> = p.iter().map(|a| a.raw()).collect();
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
            pool.install(|| parallel(&lazy, x, black_box(raw_points[i % 4]), depth, zero, one))
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

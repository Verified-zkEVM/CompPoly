/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Bivariate.ToPoly

import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
/-!
# Factorisation of Computable Bivariate Polynomials

Defines `evalYPoly` (substitute `Y ↦ f(X)`), `isLinearYFactor` (test
divisibility by `Y - f(X)`), and `divByLinearY` (synthetic division of a
bivariate polynomial by the monic linear factor `Y - f(X)`).

`divByLinearY` is the computable factor theorem for the nested representation
`CBivariate R = CPolynomial (CPolynomial R)`: given a root `f(X)`, it deflates
`Q` by `Y - f(X)` over an arbitrary commutative ring. It is
the degree-one special case of monic Euclidean division; division by an
arbitrary monic divisor in `Y` is available generically through
`CPolynomial.divByMonic` / `CPolynomial.modByMonic` over the coefficient ring
`CPolynomial R` (see `CPolynomial.modByMonic_add_mul_divByMonic`).
-/

namespace CompPoly

namespace CBivariate

/-- Substitute `Y ↦ f(X)` into a bivariate polynomial `Q`, i.e. evaluate `Q` at
`f` in the `Y` variable. The result is the univariate polynomial `Q(X, f(X))`. -/
def evalYPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) (Q : CBivariate R) : CPolynomial R :=
  Q.val.eval f

/-- Decide whether `Y - f(X)` divides `Q`, i.e. whether `Q(X, f(X)) = 0`. By the
factor theorem this is exactly the test for `f(X)` being a `Y`-root of `Q`. -/
def isLinearYFactor [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) : Bool :=
  evalYPoly f Q == 0

/-- `evalYPoly` sends the zero polynomial to `0`. -/
theorem evalYPoly_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) :
    evalYPoly f (0 : CBivariate R) = 0 := by
  show (0 : CBivariate R).val.eval f = 0
  have h : (0 : CBivariate R).val = (0 : CPolynomial.Raw (CPolynomial R)) := rfl
  rw [h, ← CPolynomial.Raw.eval_toPoly_eq_eval f (0 : CPolynomial.Raw (CPolynomial R)),
    CPolynomial.Raw.toPoly_zero, Polynomial.eval_zero]

/-- `evalYPoly` is additive in the polynomial being evaluated. -/
theorem evalYPoly_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) (P Q : CBivariate R) :
    evalYPoly f (P + Q) = evalYPoly f P + evalYPoly f Q := by
  show (P + Q).val.eval f = P.val.eval f + Q.val.eval f
  have h : (P + Q).val = P.val + Q.val := rfl
  rw [h, ← CPolynomial.Raw.eval_toPoly_eq_eval f (P.val + Q.val),
    ← CPolynomial.Raw.eval_toPoly_eq_eval f P.val,
    ← CPolynomial.Raw.eval_toPoly_eq_eval f Q.val,
    CPolynomial.Raw.toPoly_add, Polynomial.eval_add]

/-- The `isLinearYFactor` boolean test agrees with the proposition `Q(X, f(X)) = 0`. -/
theorem isLinearYFactor_iff [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    isLinearYFactor Q f = true ↔ evalYPoly f Q = 0 := by
  simp [isLinearYFactor, beq_iff_eq]

/-- Bridge to Mathlib: evaluating `Q` at `f` and mapping to `Polynomial R` agrees
with evaluating the mapped `toPoly Q : R[X][Y]` at `f.toPoly`. -/
theorem evalYPoly_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CPolynomial R) (Q : CBivariate R) :
    (evalYPoly f Q).toPoly = (toPoly Q).eval (f.toPoly) := by
  show (Q.val.eval f).toPoly = (toPoly Q).eval (f.toPoly)
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval f Q.val]
  rw [toPoly_eq_map, Polynomial.eval_map]
  change (CPolynomial.ringEquiv (R := R)).toRingHom ((CPolynomial.toPoly Q).eval f) =
    (CPolynomial.toPoly Q).eval₂ (CPolynomial.ringEquiv (R := R)).toRingHom (f.toPoly)
  rw [show Polynomial.eval f (CPolynomial.toPoly Q) =
    (CPolynomial.toPoly Q).eval₂ (RingHom.id _) f from rfl]
  rw [Polynomial.hom_eval₂, RingHom.comp_id]
  rfl

/-- Synthetic (Horner) division of a bivariate polynomial `Q` by the linear factor
`Y - f(X)`, performed in the `Y` variable. Returns the pair `(quotient, remainder)`
where the quotient is a `CBivariate R` and the remainder is a `CPolynomial R`.

Writing `Q = Σ_{j=0}^n aⱼ Yʲ` with `aⱼ = coeff Q j`, the quotient coefficients
`bⱼ` and the remainder `r` satisfy the synthetic-division recurrence
`b_{n-1} = aₙ`, `b_{j-1} = aⱼ + f · bⱼ`, `r = a₀ + f · b₀`, so that
`Q = quotient · (Y - f) + r`. See `divByLinearY_spec`. -/
def divByLinearY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (f : CPolynomial R) : CBivariate R × CPolynomial R :=
  let n := natDegreeY Q
  if n = 0 then (0, CPolynomial.coeff Q 0)
  else
    let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
    let b_init := a n
    let (b_last, coeffs) := (List.range (n - 1)).foldl
      (fun (b, acc) k =>
        let bj := a (n - 1 - k) + f * b
        (bj, acc.push bj))
      (b_init, #[b_init])
    let rem := a 0 + f * b_last
    let quotArr : CPolynomial.Raw (CPolynomial R) := coeffs.reverse
    (⟨quotArr.trim, CPolynomial.Raw.Trim.isCanonical_trim quotArr⟩, rem)

theorem divByLinearY_const [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (a f : CPolynomial R) :
  divByLinearY (CPolynomial.C a : CBivariate R) f = (0, a) := by
  unfold divByLinearY
  have hdeg : natDegreeY (CPolynomial.C a : CBivariate R) = 0 := by
    rw [CBivariate.natDegreeY, CPolynomial.natDegree_toPoly, CPolynomial.C_toPoly]
    by_cases ha : a = 0
    · subst ha
      simp
    · simp
  simp [hdeg]
  simpa [CPolynomial.coeff] using (CPolynomial.coeff_C (R := CPolynomial R) (r := a) (i := 0))

theorem divByLinearY_fold_split [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (f : CPolynomial R) (h : 1 < natDegreeY Q) :
  let n := natDegreeY Q
  let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
  let step : CPolynomial R × Array (CPolynomial R) → ℕ → CPolynomial R × Array (CPolynomial R) :=
    fun x k =>
      let bj := a (n - 1 - k) + f * x.1
      (bj, x.2.push bj)
  let res1 := (List.range (n - 2)).foldl step (a n, #[(a n)])
  (List.range (n - 1)).foldl step (a n, #[(a n)]) =
    (a 1 + f * res1.1, res1.2.push (a 1 + f * res1.1)) := by
  dsimp
  have hn2 : 2 ≤ natDegreeY Q := by omega
  rw [show natDegreeY Q - 1 = (natDegreeY Q - 2) + 1 by omega]
  rw [List.range_succ]
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  congr <;> omega

theorem divByLinearY_pair_of_one_lt [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R]
  (Q : CBivariate R) (f : CPolynomial R) (h : 1 < natDegreeY Q) :
  let n := natDegreeY Q
  let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
  let step : CPolynomial R × Array (CPolynomial R) → ℕ → CPolynomial R × Array (CPolynomial R) :=
    fun x k =>
      let bj := a (n - 1 - k) + f * x.1
      (bj, x.2.push bj)
  let res1 := (List.range (n - 2)).foldl step (a n, #[(a n)])
  let r1 := a 1 + f * res1.1
  divByLinearY Q f =
    (⟨CPolynomial.Raw.trim ((res1.2.push r1).reverse),
      CPolynomial.Raw.Trim.isCanonical_trim ((res1.2.push r1).reverse)⟩, a 0 + f * r1) := by
  let n := natDegreeY Q
  let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
  let step : CPolynomial R × Array (CPolynomial R) → ℕ → CPolynomial R × Array (CPolynomial R) :=
    fun x k =>
      let bj := a (n - 1 - k) + f * x.1
      (bj, x.2.push bj)
  let res1 := (List.range (n - 2)).foldl step (a n, #[(a n)])
  let r1 := a 1 + f * res1.1
  have h0 : natDegreeY Q ≠ 0 := by
    omega
  have hsplit :
      (List.range (n - 1)).foldl step (a n, #[(a n)]) = (r1, res1.2.push r1) := by
    simpa [n, a, step, res1, r1] using (divByLinearY_fold_split (Q := Q) (f := f) h)
  unfold divByLinearY
  rw [if_neg h0]
  dsimp [n, a, step, res1, r1]
  rw [hsplit]

theorem divByLinearY_quot_of_natDegreeY_one [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (f : CPolynomial R) (h : natDegreeY Q = 1) :
  (divByLinearY Q f).1 = CPolynomial.C (CPolynomial.coeff Q 1) := by
  simp [divByLinearY, h, CPolynomial.C]
  rfl

theorem divByLinearY_quot_of_natDegreeY_zero [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (f : CPolynomial R) (h : natDegreeY Q = 0) :
  (divByLinearY Q f).1 = 0 := by
  simp [divByLinearY, h]

theorem divByLinearY_rem_formula [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (f : CPolynomial R) :
  let quot := (divByLinearY Q f).1
  let rem := (divByLinearY Q f).2
  rem = CPolynomial.coeff Q 0 + f * CPolynomial.coeff quot 0 := by
  unfold divByLinearY
  by_cases h0 : natDegreeY Q = 0
  · simp [h0]
    change f * ((0 : CPolynomial.Raw (CPolynomial R)).coeff 0) = 0
    simp [CPolynomial.Raw.coeff]
  · simp [h0]
    let n := Q.natDegreeY
    let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
    let step : CPolynomial R × Array (CPolynomial R) → ℕ → CPolynomial R × Array (CPolynomial R) :=
      fun x k =>
        let bj := a (n - 1 - k) + f * x.1
        (bj, x.2.push bj)
    let res := (List.range (n - 1)).foldl step (a n, #[a n])
    have hfold : ∀ l (b : CPolynomial R) (acc : Array (CPolynomial R)),
        ((List.foldl step (b, acc.push b) l).2.reverse)[0]?.getD 0 =
          (List.foldl step (b, acc.push b) l).1 := by
      intro l
      induction l with
      | nil =>
          intro b acc
          simp [step]
      | cons k l ih =>
          intro b acc
          simpa [List.foldl_cons, step] using ih (a (n - 1 - k) + f * b) (acc.push b)
    have hres : (res.2.reverse)[0]?.getD 0 = res.1 := by
      simpa [res, step] using hfold (List.range (n - 1)) (a n) (#[])
    have htrim0 : (CPolynomial.Raw.trim res.2.reverse)[0]?.getD 0 = (res.2.reverse)[0]?.getD 0 := by
      simpa [CPolynomial.Raw.coeff] using (CPolynomial.Raw.Trim.coeff_eq_coeff (res.2.reverse) 0)
    have hmain : f * res.1 = f * (CPolynomial.Raw.trim res.2.reverse)[0]?.getD 0 := by
      rw [htrim0, hres]
    simpa [n, a, step, res] using hmain

theorem divByLinearY_zero [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (f : CPolynomial R) :
  divByLinearY (0 : CBivariate R) f = (0, 0) := by
  change divByLinearY (⟨#[], CPolynomial.Raw.Trim.isCanonical_empty⟩ : CBivariate R) f = (0, 0)
  simp [divByLinearY, CBivariate.natDegreeY, CPolynomial.natDegree, CPolynomial.coeff]

theorem divX_eq_C_coeff_one_of_natDegreeY_one [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (h : natDegreeY Q = 1) :
  CPolynomial.divX Q = CPolynomial.C (CPolynomial.coeff Q 1) := by
  apply CPolynomial.eq_iff_coeff.mpr
  intro i
  rw [CPolynomial.coeff_divX, CPolynomial.coeff_C]
  cases i with
  | zero =>
      simp
  | succ k =>
      have hdeg : (CBivariate.toPoly Q).natDegree = 1 := by
        simpa [h] using (CBivariate.natDegreeY_toPoly (f := Q))
      have hlt : (CBivariate.toPoly Q).natDegree < k + 2 := by
        rw [hdeg]
        omega
      have hzero_toPoly : (CPolynomial.coeff Q (k + 2)).toPoly = 0 := by
        simpa [CBivariate.toPoly_coeff] using
          (Polynomial.coeff_eq_zero_of_natDegree_lt (p := CBivariate.toPoly Q) (n := k + 2) hlt)
      have hzero : CPolynomial.coeff Q (k + 2) = 0 := by
        exact (CPolynomial.toPoly_eq_zero_iff (CPolynomial.coeff Q (k + 2))).mp hzero_toPoly
      simpa using hzero

theorem divX_zero_of_natDegreeY_zero [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (h : natDegreeY Q = 0) :
  CPolynomial.divX Q = 0 := by
  rw [CPolynomial.eq_zero_iff_coeff_zero]
  intro i
  rw [CPolynomial.coeff_divX]
  apply (CPolynomial.toPoly_eq_zero_iff (p := CPolynomial.coeff Q (i + 1))).mp
  rw [← CBivariate.toPoly_coeff]
  have hdeg : (toPoly Q).natDegree = 0 := by
    rw [CBivariate.natDegreeY_toPoly, h]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)

theorem natDegreeY_divX_of_one_lt [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (h : 1 < natDegreeY Q) :
  natDegreeY (CPolynomial.divX Q) = natDegreeY Q - 1 := by
  unfold CBivariate.natDegreeY CPolynomial.natDegree at h ⊢
  cases hs : Q.val.size with
  | zero =>
      simp [hs] at h
  | succ m =>
      cases m with
      | zero =>
          simp [hs] at h
      | succ k =>
          simp [CPolynomial.divX, hs, Array.size_extract]

theorem divByLinearY_divX_pair_of_one_lt [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R]
  (Q : CBivariate R) (f : CPolynomial R) (h : 1 < natDegreeY Q) :
  let n := natDegreeY Q
  let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
  let step : CPolynomial R × Array (CPolynomial R) → ℕ → CPolynomial R × Array (CPolynomial R) :=
    fun x k =>
      let bj := a (n - 1 - k) + f * x.1
      (bj, x.2.push bj)
  let res1 := (List.range (n - 2)).foldl step (a n, #[(a n)])
  let r1 := a 1 + f * res1.1
  divByLinearY (CPolynomial.divX Q) f =
    (⟨CPolynomial.Raw.trim (res1.2.reverse),
      CPolynomial.Raw.Trim.isCanonical_trim (res1.2.reverse)⟩, r1) := by
  let n := natDegreeY Q
  let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
  let step : CPolynomial R × Array (CPolynomial R) → ℕ → CPolynomial R × Array (CPolynomial R) :=
    fun x k =>
      let bj := a (n - 1 - k) + f * x.1
      (bj, x.2.push bj)
  let res1 := (List.range (n - 2)).foldl step (a n, #[(a n)])
  let r1 := a 1 + f * res1.1
  have hn : 1 < n := by
    simpa [n] using h
  have hdivX : natDegreeY (CPolynomial.divX Q) = n - 1 := by
    simpa [n] using (natDegreeY_divX_of_one_lt (Q := Q) h)
  have hdivX0 : natDegreeY (CPolynomial.divX Q) ≠ 0 := by
    rw [hdivX]
    omega
  unfold divByLinearY
  simp only [hdivX0, if_false]
  rw [hdivX]
  simp only [CPolynomial.coeff_divX]
  let step1 : CPolynomial R × Array (CPolynomial R) → ℕ → CPolynomial R × Array (CPolynomial R) :=
    fun x k =>
      let bj := CPolynomial.coeff Q (n - 1 - 1 - k + 1) + f * x.1
      (bj, x.2.push bj)
  let step2 : CPolynomial R × Array (CPolynomial R) → ℕ → CPolynomial R × Array (CPolynomial R) :=
    fun x k =>
      let bj := CPolynomial.coeff Q (n - 1 - k) + f * x.1
      (bj, x.2.push bj)
  have hfold :
      List.foldl step1 (CPolynomial.coeff Q (n - 1 + 1), #[CPolynomial.coeff Q (n - 1 + 1)])
        (List.range (n - 1 - 1)) =
      res1 := by
    have hfold₁ :
        List.foldl step1 (CPolynomial.coeff Q (n - 1 + 1), #[CPolynomial.coeff Q (n - 1 + 1)])
          (List.range (n - 1 - 1)) =
        List.foldl step2 (CPolynomial.coeff Q (n - 1 + 1), #[CPolynomial.coeff Q (n - 1 + 1)])
          (List.range (n - 1 - 1)) := by
      apply List.foldl_ext
      intro x k hk
      have hklt : k < n - 1 - 1 := List.mem_range.mp hk
      have hidx : n - 1 - 1 - k + 1 = n - 1 - k := by
        omega
      dsimp [step1, step2]
      rw [hidx]
    calc
      List.foldl step1 (CPolynomial.coeff Q (n - 1 + 1), #[CPolynomial.coeff Q (n - 1 + 1)])
          (List.range (n - 1 - 1))
          = List.foldl step2 (CPolynomial.coeff Q (n - 1 + 1), #[CPolynomial.coeff Q (n - 1 + 1)])
              (List.range (n - 1 - 1)) := hfold₁
      _ = List.foldl step2 (CPolynomial.coeff Q n, #[CPolynomial.coeff Q n])
            (List.range (n - 2)) := by
            have hinit : n - 1 + 1 = n := by
              omega
            have hrange : n - 1 - 1 = n - 2 := by
              omega
            simp [hinit, hrange]
      _ = res1 := by
            dsimp [res1, step, a, step2]
  let g : (CPolynomial R × Array (CPolynomial R)) → CBivariate R × CPolynomial R :=
    fun z =>
      (⟨CPolynomial.Raw.trim (z.2.reverse),
        CPolynomial.Raw.Trim.isCanonical_trim (z.2.reverse)⟩,
        CPolynomial.coeff Q (0 + 1) + f * z.1)
  have hpair :
      g (List.foldl step1 (CPolynomial.coeff Q (n - 1 + 1), #[CPolynomial.coeff Q (n - 1 + 1)])
          (List.range (n - 1 - 1))) = g res1 := by
    exact congrArg g hfold
  simpa [g, n, a, step, step1, res1, r1] using hpair

theorem raw_trim_reverse_push_coeff_succ [Zero R] [BEq R] [LawfulBEq R]
    (arr : Array R) (a : R) (j : ℕ) :
  CPolynomial.Raw.coeff (CPolynomial.Raw.trim ((arr.push a).reverse)) (j + 1) =
    CPolynomial.Raw.coeff (CPolynomial.Raw.trim (arr.reverse)) j := by
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff, CPolynomial.Raw.Trim.coeff_eq_coeff]
  rw [Array.reverse_push]
  unfold CPolynomial.Raw.coeff
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  have h1 : (#[a] : Array R).size ≤ j + 1 := by simp
  rw [Array.getElem?_append_right (xs := #[a]) (ys := arr.reverse) (i := j + 1) h1]
  simp

theorem divByLinearY_divX_quot_coeff [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (f : CPolynomial R) (j : ℕ) :
  let quot := (divByLinearY Q f).1
  CPolynomial.coeff ((divByLinearY (CPolynomial.divX Q) f).1) j
      = CPolynomial.coeff quot (j + 1) := by
  classical
  change CPolynomial.coeff ((divByLinearY (CPolynomial.divX Q) f).1) j =
    CPolynomial.coeff ((divByLinearY Q f).1) (j + 1)
  by_cases h0 : natDegreeY Q = 0
  · have hzeroquot : (divByLinearY (0 : CBivariate R) f).1 = 0 := by
      simpa using congrArg Prod.fst (divByLinearY_zero (R := R) (f := f))
    calc
      CPolynomial.coeff ((divByLinearY (CPolynomial.divX Q) f).1) j
          = CPolynomial.coeff ((divByLinearY (0 : CBivariate R) f).1) j := by
              rw [divX_zero_of_natDegreeY_zero (Q := Q) h0]
              rfl
      _ = 0 := by
            simpa using congrArg (fun p : CBivariate R => CPolynomial.coeff p j) hzeroquot
      _ = CPolynomial.coeff ((divByLinearY Q f).1) (j + 1) := by
            rw [divByLinearY_quot_of_natDegreeY_zero (Q := Q) (f := f) h0]
            simpa using (CPolynomial.coeff_zero (R := CPolynomial R) (i := j + 1)).symm
  · by_cases h1 : natDegreeY Q = 1
    · have hconstquot :
          (divByLinearY (CPolynomial.C (CPolynomial.coeff Q 1) : CBivariate R) f).1 = 0 := by
        simpa using
          congrArg Prod.fst (divByLinearY_const (R := R) (a := CPolynomial.coeff Q 1) (f := f))
      calc
        CPolynomial.coeff ((divByLinearY (CPolynomial.divX Q) f).1) j
            = CPolynomial.coeff
                ((divByLinearY (CPolynomial.C (CPolynomial.coeff Q 1) : CBivariate R) f).1) j := by
                rw [divX_eq_C_coeff_one_of_natDegreeY_one (Q := Q) h1]
        _ = 0 := by
              simpa using congrArg (fun p : CBivariate R => CPolynomial.coeff p j) hconstquot
        _ = CPolynomial.coeff ((divByLinearY Q f).1) (j + 1) := by
              rw [divByLinearY_quot_of_natDegreeY_one (Q := Q) (f := f) h1]
              simpa [Nat.succ_ne_zero] using
                (CPolynomial.coeff_C (R := CPolynomial R)
                  (r := CPolynomial.coeff Q 1) (i := j + 1)).symm
    · have hgt : 1 < natDegreeY Q := by
        omega
      let n := natDegreeY Q
      let a : ℕ → CPolynomial R := fun k => CPolynomial.coeff Q k
      let step : CPolynomial R × Array (CPolynomial R) → ℕ →
          CPolynomial R × Array (CPolynomial R) :=
        fun x k =>
          let bj := a (n - 1 - k) + f * x.1
          (bj, x.2.push bj)
      let res1 := (List.range (n - 2)).foldl step (a n, #[(a n)])
      let r1 := a 1 + f * res1.1
      have hshort :
          divByLinearY (CPolynomial.divX Q) f =
            (⟨CPolynomial.Raw.trim (res1.2.reverse),
              CPolynomial.Raw.Trim.isCanonical_trim (res1.2.reverse)⟩, r1) := by
        simpa [n, a, step, res1, r1] using
          (divByLinearY_divX_pair_of_one_lt (R := R) (Q := Q) (f := f) hgt)
      have hlong :
          divByLinearY Q f =
            (⟨CPolynomial.Raw.trim ((res1.2.push r1).reverse),
              CPolynomial.Raw.Trim.isCanonical_trim ((res1.2.push r1).reverse)⟩, a 0 + f * r1) := by
        simpa [n, a, step, res1, r1] using
          (divByLinearY_pair_of_one_lt (R := R) (Q := Q) (f := f) hgt)
      rw [hshort, hlong]
      simpa [CPolynomial.coeff] using
        (raw_trim_reverse_push_coeff_succ (R := CPolynomial R)
          (arr := res1.2) (a := r1) (j := j)).symm

theorem raw_trim_reverse_push_coeff_zero [Zero R] [BEq R] [LawfulBEq R]
    (arr : Array R) (a : R) :
  CPolynomial.Raw.coeff (CPolynomial.Raw.trim ((arr.push a).reverse)) 0 = a := by
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  rw [Array.reverse_push]
  simp [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]

theorem divByLinearY_divX_rem [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (f : CPolynomial R) :
  let quot := (divByLinearY Q f).1
  (divByLinearY (CPolynomial.divX Q) f).2 = CPolynomial.coeff quot 0 := by
  classical
  dsimp
  by_cases h0 : natDegreeY Q = 0
  · rw [divX_zero_of_natDegreeY_zero Q h0, divByLinearY_quot_of_natDegreeY_zero Q f h0]
    have hrem0 : (divByLinearY (0 : CBivariate R) f).2 = (0 : CPolynomial R) := by
      exact congrArg Prod.snd (divByLinearY_zero (R := R) (f := f))
    simpa [CPolynomial.coeff_zero] using hrem0
  · by_cases h1 : natDegreeY Q = 1
    · rw [divX_eq_C_coeff_one_of_natDegreeY_one Q h1]
      have hrem1 :
          (divByLinearY (CPolynomial.C (CPolynomial.coeff Q 1) : CBivariate R) f).2 =
            CPolynomial.coeff Q 1 := by
        exact congrArg Prod.snd (divByLinearY_const (a := CPolynomial.coeff Q 1) (f := f))
      rw [divByLinearY_quot_of_natDegreeY_one Q f h1]
      have hcoeffC0 :
          CPolynomial.coeff (CPolynomial.C (CPolynomial.coeff Q 1)) 0 = CPolynomial.coeff Q 1 := by
        rw [CPolynomial.coeff_C]
        simp
      exact hrem1.trans hcoeffC0.symm
    · have hgt : 1 < natDegreeY Q := by
        omega
      let n := natDegreeY Q
      let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
      let step : CPolynomial R × Array (CPolynomial R) → ℕ →
          CPolynomial R × Array (CPolynomial R) :=
        fun x k =>
          let bj := a (n - 1 - k) + f * x.1
          (bj, x.2.push bj)
      let res1 := (List.range (n - 2)).foldl step (a n, #[(a n)])
      let r1 := a 1 + f * res1.1
      have hshort : divByLinearY (CPolynomial.divX Q) f =
          (⟨CPolynomial.Raw.trim (res1.2.reverse),
            CPolynomial.Raw.Trim.isCanonical_trim (res1.2.reverse)⟩, r1) := by
        simpa [n, a, step, res1, r1] using (divByLinearY_divX_pair_of_one_lt (Q := Q) (f := f) hgt)
      have hlong : divByLinearY Q f =
          (⟨CPolynomial.Raw.trim ((res1.2.push r1).reverse),
            CPolynomial.Raw.Trim.isCanonical_trim ((res1.2.push r1).reverse)⟩, a 0 + f * r1) := by
        simpa [n, a, step, res1, r1] using (divByLinearY_pair_of_one_lt (Q := Q) (f := f) hgt)
      rw [hshort, hlong]
      simpa [CPolynomial.coeff] using
        (raw_trim_reverse_push_coeff_zero (arr := res1.2) (a := r1)).symm

theorem divByLinearY_quot_recurrence [CommRing R] [BEq R] [LawfulBEq R]
    [Nontrivial R] [DecidableEq R] (Q : CBivariate R) (f : CPolynomial R) (j : ℕ) :
  let quot := (divByLinearY Q f).1
  CPolynomial.coeff quot j = CPolynomial.coeff Q (j + 1) + f * CPolynomial.coeff quot (j + 1) := by
  dsimp
  induction j generalizing Q with
  | zero =>
      have h := divByLinearY_rem_formula (Q := CPolynomial.divX Q) (f := f)
      dsimp at h
      rw [divByLinearY_divX_rem (Q := Q) (f := f)] at h
      rw [divByLinearY_divX_quot_coeff (Q := Q) (f := f) 0] at h
      rw [CPolynomial.coeff_divX] at h
      simpa using h
  | succ j ih =>
      have h := ih (Q := CPolynomial.divX Q)
      rw [divByLinearY_divX_quot_coeff (Q := Q) (f := f) j,
        divByLinearY_divX_quot_coeff (Q := Q) (f := f) (j + 1),
        CPolynomial.coeff_divX] at h
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Correctness of `divByLinearY`: in `R[X][Y]` the computed quotient and
remainder satisfy the Euclidean division identity
`Q = quotient · (Y - f) + remainder`, over any commutative ring. -/
theorem divByLinearY_spec [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    let quot := (divByLinearY Q f).1
    let rem := (divByLinearY Q f).2
    toPoly Q = toPoly quot * (Polynomial.X - Polynomial.C (f.toPoly)) +
        Polynomial.C (rem.toPoly) := by
  classical
  dsimp
  apply Polynomial.ext
  intro n
  cases n with
  | zero =>
      -- coefficient 0: from the remainder formula `rem = a₀ + f · quot₀`
      have hcoeff0 : (toPoly Q).coeff 0 =
          (divByLinearY Q f).2.toPoly - (toPoly (divByLinearY Q f).1).coeff 0 * f.toPoly := by
        have hrem := divByLinearY_rem_formula Q f
        dsimp at hrem
        have hrem' := congrArg CPolynomial.toPoly hrem
        rw [CPolynomial.toPoly_add, CPolynomial.toPoly_mul] at hrem'
        rw [CBivariate.toPoly_coeff, CBivariate.toPoly_coeff]
        rw [hrem']
        ring_nf
      simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C,
        Polynomial.coeff_X_zero, sub_eq_add_neg, add_comm]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcoeff0
  | succ j =>
      -- coefficient j+1: from the quotient recurrence `quotⱼ = a_{j+1} + f · quot_{j+1}`
      have hcoeffS : (toPoly Q).coeff (j + 1) =
          (toPoly (divByLinearY Q f).1).coeff j -
            (toPoly (divByLinearY Q f).1).coeff (j + 1) * f.toPoly := by
        have hraw : CPolynomial.coeff (divByLinearY Q f).1 j =
            CPolynomial.coeff Q (j + 1) + f * CPolynomial.coeff (divByLinearY Q f).1 (j + 1) := by
          simpa using divByLinearY_quot_recurrence (Q := Q) (f := f) (j := j)
        have hpoly : (toPoly (divByLinearY Q f).1).coeff j =
            (toPoly Q).coeff (j + 1) + f.toPoly * (toPoly (divByLinearY Q f).1).coeff (j + 1) := by
          rw [CBivariate.toPoly_coeff, CBivariate.toPoly_coeff, CBivariate.toPoly_coeff]
          simpa [CPolynomial.toPoly_add, CPolynomial.toPoly_mul] using
            congrArg CPolynomial.toPoly hraw
        rw [eq_sub_iff_add_eq]
        simpa [mul_comm] using hpoly.symm
      simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_mul_X_sub_C]
      simpa using hcoeffS


/-- The remainder of dividing `Q` by `Y - f` is the substitution `Q(X, f(X))`
(`evalYPoly f Q`), by the factor/remainder theorem. -/
theorem divByLinearY_rem_eq_eval [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    (divByLinearY Q f).2 = evalYPoly f Q := by
  -- Evaluate `toPoly Q = toPoly quot * (X - C f.toPoly) + C rem.toPoly` at `Y = f.toPoly`.
  have hspec := divByLinearY_spec Q f
  dsimp only at hspec
  have hev := congrArg (Polynomial.eval f.toPoly) hspec
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, mul_zero, zero_add, Polynomial.eval_C] at hev
  -- hev : (toPoly Q).eval f.toPoly = (divByLinearY Q f).2.toPoly
  apply CPolynomial.eq_iff_coeff.2
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, evalYPoly_toPoly, hev]

/-- If `Y - f` divides `Q` (`isLinearYFactor Q f`), the division is exact:
the remainder is `0`. -/
theorem divByLinearY_exact [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) (h : isLinearYFactor Q f = true) :
    (divByLinearY Q f).2 = 0 := by
  rw [divByLinearY_rem_eq_eval]
  exact (isLinearYFactor_iff Q f).mp h

end CBivariate

end CompPoly

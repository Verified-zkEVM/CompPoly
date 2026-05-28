/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Bivariate.ToPoly

/-!
# Factorisation of Computable Bivariate Polynomials

Defines `evalYPoly` (substitute Y ↦ f(X)), `isLinearYFactor` (check
divisibility by Y - f(X)), and `divByLinearY` (synthetic division in Y).
These operations support the Roth-Ruckenstein root-finding step in
Guruswami–Sudan interpolation.
-/

namespace CompPoly

namespace CBivariate

def evalYPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  (f : CPolynomial R) (Q : CBivariate R) : CPolynomial R :=
  Q.val.eval f

def isLinearYFactor [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) : Bool :=
  evalYPoly f Q == 0

theorem evalYPoly_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) :
    evalYPoly f (0 : CBivariate R) = 0 := by
  show (0 : CBivariate R).val.eval f = 0
  have h : (0 : CBivariate R).val = (0 : CPolynomial.Raw (CPolynomial R)) := rfl
  rw [h, ← CPolynomial.Raw.eval_toPoly_eq_eval f (0 : CPolynomial.Raw (CPolynomial R)),
    CPolynomial.Raw.toPoly_zero, Polynomial.eval_zero]

theorem evalYPoly_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CPolynomial R) (P Q : CBivariate R) :
    evalYPoly f (P + Q) = evalYPoly f P + evalYPoly f Q := by
  show (P + Q).val.eval f = P.val.eval f + Q.val.eval f
  have h : (P + Q).val = P.val + Q.val := rfl
  rw [h, ← CPolynomial.Raw.eval_toPoly_eq_eval f (P.val + Q.val),
    ← CPolynomial.Raw.eval_toPoly_eq_eval f P.val,
    ← CPolynomial.Raw.eval_toPoly_eq_eval f Q.val,
    CPolynomial.Raw.toPoly_add, Polynomial.eval_add]

theorem isLinearYFactor_iff [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    isLinearYFactor Q f = true ↔ evalYPoly f Q = 0 := by
  simp [isLinearYFactor, beq_iff_eq]

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

/-
Proof strategy for divByLinearY_spec (approach A — via Mathlib division theorem):

Step 1: Prove `divByLinearY_rem_eq_eval`: the remainder of synthetic division
equals `evalYPoly f Q`. Both compute Σ aⱼ fʲ (Horner's method = synthetic
division remainder). This is an induction on the fold, showing the running
accumulator `b` satisfies `b = Σ_{j≥k} a_j * f^{j-k}` after processing
coefficient k.

Step 2: Combine `divByLinearY_rem_eq_eval` with `evalYPoly_toPoly` to get
  `rem.toPoly = (toPoly Q).eval (f.toPoly)`
which is also
  `rem.toPoly = ((toPoly Q) %ₘ (X - C f.toPoly)).coeff 0`  (by modByMonic_X_sub_C_eq_C_eval)

Step 3: Use Mathlib's `modByMonic_add_div` to get
  `toPoly Q = (X - C f.toPoly) * ((toPoly Q) /ₘ (X - C f.toPoly)) + C ((toPoly Q).eval f.toPoly)`

Step 4: Subtract our decomposition from the Mathlib decomposition. This gives
  `(toPoly quot - (toPoly Q) /ₘ (X - C f.toPoly)) * (X - C f.toPoly) = 0`
Since `X - C f.toPoly` is monic (hence nonzero), and `R[X]` is an integral
domain (assuming `IsDomain R`), the other factor is zero, proving
  `toPoly quot = (toPoly Q) /ₘ (X - C f.toPoly)`
and thus the spec.

Note: Step 4 uses `IsDomain R` (or `IsDomain R[X]`). If we want to avoid that,
the alternative is to show `degree (toPoly quot) < degree (X - C f.toPoly)` is
impossible, so the factor must be zero by Mathlib's uniqueness of divByMonic.
Alternatively, use `Polynomial.eq_of_dvd_of_degree_le_of_leadingCoeff` or
`divByMonic_eq_of_lt_and_lt` if available.
-/

-- Helper: fold on Q aligns with fold on divX Q via coeff_divX
theorem divByLinearY_prefix_fold_eq_divX_fold [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (f : CPolynomial R) (k : ℕ) :
    List.foldl
      (fun x k_1 =>
        (CPolynomial.coeff Q (k + 1 - k_1) + f * x.1,
          x.2.push (CPolynomial.coeff Q (k + 1 - k_1) + f * x.1)))
      (CPolynomial.coeff Q (k + 2), #[CPolynomial.coeff Q (k + 2)])
      (List.range k) =
    List.foldl
      (fun x k_1 =>
        ((CPolynomial.divX Q).coeff (k - k_1) + f * x.1,
          x.2.push ((CPolynomial.divX Q).coeff (k - k_1) + f * x.1)))
      ((CPolynomial.divX Q).coeff (k + 1), #[(CPolynomial.divX Q).coeff (k + 1)])
      (List.range k) := by
  rw [show (CPolynomial.coeff Q (k + 2), #[CPolynomial.coeff Q (k + 2)]) =
      ((CPolynomial.divX Q).coeff (k + 1), #[(CPolynomial.divX Q).coeff (k + 1)]) by
    simpa using congrArg (fun c => (c, #[c]))
      ((CPolynomial.coeff_divX (p := Q) (i := k + 1)).symm)]
  apply List.foldl_ext
  intro a i hi
  rcases a with ⟨b, acc⟩
  have hi' : i < k := List.mem_range.mp hi
  have hidx : k + 1 - i = (k - i) + 1 := by omega
  simpa [hidx] using congrArg (fun c => (c + f * b, acc.push (c + f * b)))
    ((CPolynomial.coeff_divX (p := Q) (i := k - i)).symm)

-- Helper: Horner step for evalYPoly via divX
theorem evalYPoly_divX_step [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (f : CPolynomial R) :
    evalYPoly f Q = CPolynomial.coeff Q 0 + f * evalYPoly f (CPolynomial.divX Q) := by
  change CPolynomial.eval f Q =
    CPolynomial.coeff Q 0 + f * CPolynomial.eval f (CPolynomial.divX Q)
  conv_lhs => rw [CPolynomial.X_mul_divX_add (p := Q)]
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add]
  rw [CPolynomial.toPoly_mul, Polynomial.eval_mul]
  rw [CPolynomial.X_toPoly, Polynomial.eval_X]
  rw [CPolynomial.C_toPoly, Polynomial.eval_C]
  rw [← CPolynomial.eval_toPoly (x := f) (p := CPolynomial.divX Q)]
  rw [add_comm]

-- Helper: natDegreeY decreases under divX
theorem natDegreeY_divX [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) :
    natDegreeY (CPolynomial.divX Q) = natDegreeY Q - 1 := by
  show CPolynomial.natDegree (CPolynomial.divX Q) = CPolynomial.natDegree Q - 1
  rw [CPolynomial.natDegree_toPoly (p := CPolynomial.divX Q)]
  rw [CPolynomial.divX_toPoly (p := Q)]
  rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  rw [← CPolynomial.natDegree_toPoly (p := Q)]

-- Helper: remainder recursion via divX
theorem divByLinearY_rem_recursion [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (f : CPolynomial R) (hQ : natDegreeY Q ≠ 0) :
    (divByLinearY Q f).2 =
      CPolynomial.coeff Q 0 + f * (divByLinearY (CPolynomial.divX Q) f).2 := by
  cases hdeg : natDegreeY Q with
  | zero => exact (hQ hdeg).elim
  | succ m =>
    cases m with
    | zero =>
      have hdivdeg : natDegreeY (CPolynomial.divX Q) = 0 := by
        simpa [hdeg] using (natDegreeY_divX (Q := Q))
      rw [divByLinearY, hdeg, if_neg (Nat.succ_ne_zero 0)]
      conv_rhs => rw [divByLinearY, hdivdeg, if_pos rfl]
      change CPolynomial.coeff Q 0 + f * CPolynomial.coeff Q 1 =
        CPolynomial.coeff Q 0 + f * CPolynomial.coeff (CPolynomial.divX Q) 0
      rw [CPolynomial.coeff_divX]
    | succ k =>
      have hdeg' : natDegreeY Q = k + 2 := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdeg
      have hdivdeg : natDegreeY (CPolynomial.divX Q) = k + 1 := by
        simpa [hdeg', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (natDegreeY_divX (Q := Q))
      have hk2nz : k + 2 ≠ 0 := by omega
      have hk1nz : k + 1 ≠ 0 := by omega
      have hk21 : k + 2 - 1 = k + 1 := by omega
      rw [divByLinearY, hdeg', if_neg hk2nz]
      rw [hk21]
      conv_rhs => rw [divByLinearY, hdivdeg, if_neg hk1nz]
      change
        CPolynomial.coeff Q 0 +
            f *
              (List.foldl
                  (fun x k_1 =>
                    (CPolynomial.coeff Q (k + 1 - k_1) + f * x.1,
                      x.2.push (CPolynomial.coeff Q (k + 1 - k_1) + f * x.1)))
                  (CPolynomial.coeff Q (k + 2), #[CPolynomial.coeff Q (k + 2)])
                  (List.range (k + 1))).1
          =
        CPolynomial.coeff Q 0 +
            f *
              (CPolynomial.coeff (CPolynomial.divX Q) 0 +
                f *
                  (List.foldl
                      (fun x k_1 =>
                        (CPolynomial.coeff (CPolynomial.divX Q) (k - k_1) + f * x.1,
                          x.2.push
                            (CPolynomial.coeff (CPolynomial.divX Q) (k - k_1) + f * x.1)))
                      (CPolynomial.coeff (CPolynomial.divX Q) (k + 1),
                        #[CPolynomial.coeff (CPolynomial.divX Q) (k + 1)])
                      (List.range k)).1)
      congr 1
      congr 1
      rw [List.range_succ]
      simp only [List.foldl_concat]
      rw [divByLinearY_prefix_fold_eq_divX_fold (Q := Q) (f := f) (k := k)]
      have hlast : k + 1 - k = 1 := by omega
      rw [hlast]
      have hcoeff0 : CPolynomial.coeff (CPolynomial.divX Q) 0 = CPolynomial.coeff Q 1 := by
        simpa using (CPolynomial.coeff_divX (p := Q) (i := 0))
      rw [hcoeff0]

-- Step 1: remainder of synthetic division = evaluation at f
theorem divByLinearY_rem_eq_eval [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    (divByLinearY Q f).2 = evalYPoly f Q := by
  refine Nat.strong_induction_on
    (p := fun n => ∀ Q : CBivariate R, Q.val.size = n →
      (divByLinearY Q f).2 = evalYPoly f Q)
    Q.val.size ?_ Q rfl
  intro n ih Q hsize
  by_cases hdeg : natDegreeY Q = 0
  · rw [divByLinearY, if_pos hdeg]
    change CPolynomial.coeff Q 0 = CPolynomial.eval f Q
    rw [CPolynomial.eval_toPoly]
    have hQnat : Q.natDegree = 0 := by
      simpa [CBivariate.natDegreeY] using hdeg
    have hdeg_toPoly : (CPolynomial.toPoly Q).natDegree = 0 := by
      simpa [hQnat] using (CPolynomial.natDegree_toPoly (p := Q)).symm
    rcases Polynomial.natDegree_eq_zero.mp hdeg_toPoly with ⟨a, ha⟩
    have ha0 : a = (CPolynomial.toPoly Q).coeff 0 := by
      have hcoeff := congrArg (fun p : Polynomial (CPolynomial R) => p.coeff 0) ha
      simpa using hcoeff
    rw [← ha, Polynomial.eval_C, CPolynomial.coeff_toPoly]
    exact ha0.symm
  · have hpos : 0 < Q.val.size := by
      by_contra hzero
      have hs : Q.val.size = 0 := Nat.eq_zero_of_not_pos hzero
      have hval : Q.val = (#[] : CPolynomial.Raw (CPolynomial R)) :=
        Array.eq_empty_of_size_eq_zero hs
      have hQ0 : Q = 0 := by
        apply CPolynomial.ext
        simpa using hval
      have hdeg0 : natDegreeY Q = 0 := by
        rw [hQ0]
        rfl
      exact hdeg hdeg0
    have hlt : (CPolynomial.divX Q).val.size < n := by
      rw [← hsize]
      exact CPolynomial.divX_size_lt Q hpos
    have hrec := ih (CPolynomial.divX Q).val.size hlt (CPolynomial.divX Q) rfl
    rw [divByLinearY_rem_recursion Q f hdeg]
    rw [hrec]
    exact (evalYPoly_divX_step Q f).symm

-- Helpers for divByLinearY_spec (coefficient-by-coefficient approach)

theorem divByLinearY_const [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : CPolynomial R) (f : CPolynomial R) :
    divByLinearY (CPolynomial.C a : CBivariate R) f = (0, a) := by
  unfold divByLinearY
  have hdeg : natDegreeY (CPolynomial.C a : CBivariate R) = 0 := by
    rw [CBivariate.natDegreeY, CPolynomial.natDegree_toPoly, CPolynomial.C_toPoly]
    by_cases ha : a = 0
    · subst ha; simp only [map_zero, Polynomial.natDegree_zero]
    · simp [ha]
  simp [hdeg]
  simpa [CPolynomial.coeff] using (CPolynomial.coeff_C (R := CPolynomial R) (r := a) (i := 0))

theorem divByLinearY_fold_split [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) (h : 1 < natDegreeY Q) :
    let n := natDegreeY Q
    let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
    let step : CPolynomial R × Array (CPolynomial R) → ℕ →
        CPolynomial R × Array (CPolynomial R) :=
      fun x k =>
        let bj := a (n - 1 - k) + f * x.1
        (bj, x.2.push bj)
    let res1 := (List.range (n - 2)).foldl step (a n, #[(a n)])
    (List.range (n - 1)).foldl step (a n, #[(a n)]) =
      (a 1 + f * res1.1, res1.2.push (a 1 + f * res1.1)) := by
  dsimp
  rw [show natDegreeY Q - 1 = (natDegreeY Q - 2) + 1 by omega]
  rw [List.range_succ]
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  congr <;> omega

theorem divByLinearY_quot_of_natDegreeY_one [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) (h : natDegreeY Q = 1) :
    (divByLinearY Q f).1 = CPolynomial.C (CPolynomial.coeff Q 1) := by
  simp [divByLinearY, h, CPolynomial.C]
  rfl

theorem divX_zero_of_natDegreeY_zero [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R]
    (Q : CBivariate R) (h : natDegreeY Q = 0) :
    CPolynomial.divX Q = 0 := by
  rw [CPolynomial.eq_zero_iff_coeff_zero]
  intro i
  rw [CPolynomial.coeff_divX]
  apply (CPolynomial.toPoly_eq_zero_iff (p := CPolynomial.coeff Q (i + 1))).mp
  rw [← CBivariate.toPoly_coeff]
  have hdeg : (toPoly Q).natDegree = 0 := by
    rw [CBivariate.natDegreeY_toPoly, h]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)

theorem divX_eq_C_coeff_one_of_natDegreeY_one [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R]
    (Q : CBivariate R) (h : natDegreeY Q = 1) :
    CPolynomial.divX Q = CPolynomial.C (CPolynomial.coeff Q 1) := by
  apply CPolynomial.eq_iff_coeff.mpr
  intro i
  rw [CPolynomial.coeff_divX, CPolynomial.coeff_C]
  cases i with
  | zero => simp
  | succ k =>
    have hdeg : (CBivariate.toPoly Q).natDegree = 1 := by
      simpa [h] using (CBivariate.natDegreeY_toPoly (f := Q))
    have hlt : (CBivariate.toPoly Q).natDegree < k + 2 := by
      rw [hdeg]; omega
    have hzero_toPoly : (CPolynomial.coeff Q (k + 2)).toPoly = 0 := by
      simpa [CBivariate.toPoly_coeff] using
        (Polynomial.coeff_eq_zero_of_natDegree_lt
          (p := CBivariate.toPoly Q) (n := k + 2) hlt)
    have hzero : CPolynomial.coeff Q (k + 2) = 0 := by
      exact (CPolynomial.toPoly_eq_zero_iff (CPolynomial.coeff Q (k + 2))).mp hzero_toPoly
    simpa using hzero

theorem raw_trim_reverse_push_coeff_succ {S : Type*} [Zero S] [BEq S] [LawfulBEq S]
    (arr : Array S) (a : S) (j : ℕ) :
    CPolynomial.Raw.coeff (CPolynomial.Raw.trim ((arr.push a).reverse)) (j + 1) =
      CPolynomial.Raw.coeff (CPolynomial.Raw.trim (arr.reverse)) j := by
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff, CPolynomial.Raw.Trim.coeff_eq_coeff]
  rw [Array.reverse_push]
  unfold CPolynomial.Raw.coeff
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  have h1 : (#[a] : Array S).size ≤ j + 1 := by simp
  rw [Array.getElem?_append_right (xs := #[a]) (ys := arr.reverse) (i := j + 1) h1]
  simp

theorem raw_trim_reverse_push_coeff_zero {S : Type*} [Zero S] [BEq S] [LawfulBEq S]
    (arr : Array S) (a : S) :
    CPolynomial.Raw.coeff (CPolynomial.Raw.trim ((arr.push a).reverse)) 0 = a := by
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  rw [Array.reverse_push]
  simp [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?]

theorem divByLinearY_rem_formula [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
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
    let step : CPolynomial R × Array (CPolynomial R) → ℕ →
        CPolynomial R × Array (CPolynomial R) :=
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
    have htrim0 : (CPolynomial.Raw.trim res.2.reverse)[0]?.getD 0 =
        (res.2.reverse)[0]?.getD 0 := by
      simpa [CPolynomial.Raw.coeff] using
        (CPolynomial.Raw.Trim.coeff_eq_coeff (res.2.reverse) 0)
    have hmain : f * res.1 = f * (CPolynomial.Raw.trim res.2.reverse)[0]?.getD 0 := by
      rw [htrim0, hres]
    simpa [n, a, step, res] using hmain

-- Key: coefficient j of divX-quotient = coefficient j+1 of original quotient
theorem divByLinearY_divX_quot_coeff [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) (j : ℕ) :
    let quot := (divByLinearY Q f).1
    CPolynomial.coeff ((divByLinearY (CPolynomial.divX Q) f).1) j =
      CPolynomial.coeff quot (j + 1) := by
  sorry

-- Key: remainder of divX-division = coefficient 0 of original quotient
theorem divByLinearY_divX_rem [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    let quot := (divByLinearY Q f).1
    (divByLinearY (CPolynomial.divX Q) f).2 = CPolynomial.coeff quot 0 := by
  sorry

theorem divByLinearY_quot_recurrence [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) (j : ℕ) :
    let quot := (divByLinearY Q f).1
    CPolynomial.coeff quot j =
      CPolynomial.coeff Q (j + 1) + f * CPolynomial.coeff quot (j + 1) := by
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

theorem divByLinearY_coeff_zero [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    let quot := (divByLinearY Q f).1
    let rem := (divByLinearY Q f).2
    (toPoly Q).coeff 0 = rem.toPoly - (toPoly quot).coeff 0 * f.toPoly := by
  dsimp
  let quot := (divByLinearY Q f).1
  let rem := (divByLinearY Q f).2
  have hrem := divByLinearY_rem_formula Q f
  dsimp at hrem
  have hrem' := congrArg CPolynomial.toPoly hrem
  rw [CPolynomial.toPoly_add, CPolynomial.toPoly_mul] at hrem'
  rw [CBivariate.toPoly_coeff, CBivariate.toPoly_coeff]
  rw [hrem']
  ring_nf

theorem divByLinearY_coeff_succ [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) (j : ℕ) :
    let quot := (divByLinearY Q f).1
    (toPoly Q).coeff (j + 1) =
      (toPoly quot).coeff j - (toPoly quot).coeff (j + 1) * f.toPoly := by
  classical
  dsimp
  let quot := (divByLinearY Q f).1
  have hraw : CPolynomial.coeff quot j =
      CPolynomial.coeff Q (j + 1) + f * CPolynomial.coeff quot (j + 1) := by
    simpa [quot] using divByLinearY_quot_recurrence (Q := Q) (f := f) (j := j)
  have hpoly : (toPoly quot).coeff j =
      (toPoly Q).coeff (j + 1) + f.toPoly * (toPoly quot).coeff (j + 1) := by
    rw [CBivariate.toPoly_coeff, CBivariate.toPoly_coeff, CBivariate.toPoly_coeff]
    simpa [CPolynomial.toPoly_add, CPolynomial.toPoly_mul] using
      congrArg CPolynomial.toPoly hraw
  rw [eq_sub_iff_add_eq]
  simpa [quot, mul_comm] using hpoly.symm

-- Step 2-4: main correctness theorem
theorem divByLinearY_spec [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) :
    let quot := (divByLinearY Q f).1
    let rem := (divByLinearY Q f).2
    toPoly Q = toPoly quot * (Polynomial.X - Polynomial.C (f.toPoly)) +
        Polynomial.C (rem.toPoly) := by
  dsimp
  apply Polynomial.ext
  intro n
  cases n with
  | zero =>
    simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.coeff_C,
      Polynomial.coeff_X_zero, sub_eq_add_neg, add_comm]
    simpa [sub_eq_add_neg, add_comm] using
      divByLinearY_coeff_zero Q f
  | succ j =>
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_mul_X_sub_C]
    simpa using divByLinearY_coeff_succ Q f j

-- Follows from divByLinearY_rem_eq_eval + isLinearYFactor_iff:
-- isLinearYFactor Q f = true ↔ evalYPoly f Q = 0, and rem = evalYPoly f Q
theorem divByLinearY_exact [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (f : CPolynomial R) (h : isLinearYFactor Q f = true) :
    (divByLinearY Q f).2 = 0 := by
  rw [divByLinearY_rem_eq_eval]
  exact (isLinearYFactor_iff Q f).mp h

end CBivariate

end CompPoly

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Basic
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Correctness.Multiplicity
import CompPoly.Univariate.DivisionCorrectness

/-!
# Executable GS Modular-Data Bridges

Semantic characterizations of the executable approximant-basis modular data:
the modulus array `gsModuli`, the incrementally built binomial relation matrix
`gsRelationColumn` / `gsRelationMatrixWithModuli`, and the executable row
predicate `rowSatisfiesModularBool`.  The main result identifies the modular
row predicate over the GS data with divisibility of every sheared coefficient
`(hasseDeriv b Q.toPoly).eval R` by `G^(s-b)`.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace ApproximantBasis

open Polynomial
open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-! ## Generic helpers -/

omit [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
private theorem foldl_add_eq_sum {M : Type*} [AddCommMonoid M] (f : Nat → M) :
    ∀ n : Nat,
      (List.range n).foldl (fun acc k ↦ acc + f k) 0 = ∑ k ∈ Finset.range n, f k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ]

omit [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
/-- First component of an `MProd`-state fold whose second component evolves
independently of the first, as a `Prod`-state fold. -/
private theorem foldl_mprod_fst {α β : Type u} {γ : Type*}
    (f : α → β → γ → α) (g : β → γ → β) :
    ∀ (l : List γ) (a : α) (b : β),
      (l.foldl (fun s c ↦ (⟨f s.fst s.snd c, g s.snd c⟩ : MProd α β)) ⟨a, b⟩).fst =
        (l.foldl (fun s c ↦ (f s.1 s.2 c, g s.2 c)) (a, b)).1 := by
  intro l
  induction l with
  | nil =>
      intro a b
      rfl
  | cons c l ih =>
      intro a b
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _

omit [Nontrivial F] [DecidableEq F] in
private theorem toPoly_finset_sum (f : Nat → CPolynomial F) (n : Nat) :
    (∑ k ∈ Finset.range n, f k).toPoly = ∑ k ∈ Finset.range n, (f k).toPoly := by
  induction n with
  | zero =>
      simp [CPolynomial.toPoly_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, CPolynomial.toPoly_add, ih]

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
/-- A common modulus of differences identifies the two divisibility facts. -/
private theorem dvd_iff_dvd_of_dvd_sub {M a b : Polynomial F} (h : M ∣ a - b) :
    M ∣ a ↔ M ∣ b := by
  constructor
  · intro ha
    have hb : M ∣ a - (a - b) := dvd_sub ha h
    simpa using hb
  · intro hb
    have ha : M ∣ (a - b) + b := dvd_add h hb
    simpa using ha

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
/-- Entry access for `PolynomialMatrix.ofFn`. -/
theorem ofFn_rowGet (rows width : Nat) (entry : Nat → Nat → CPolynomial F)
    {i j : Nat} (hi : i < rows) (hj : j < width) :
    rowGet ((PolynomialMatrix.ofFn rows width entry).getD i #[]) j = entry i j := by
  have hrow : (PolynomialMatrix.ofFn rows width entry).getD i #[] =
      ((List.range width).map (entry i)).toArray := by
    rw [PolynomialMatrix.ofFn, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
  rw [hrow, rowGet, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
/-- Row count of `PolynomialMatrix.ofFn`. -/
theorem ofFn_size (rows width : Nat) (entry : Nat → Nat → CPolynomial F) :
    (PolynomialMatrix.ofFn rows width entry).size = rows := by
  simp [PolynomialMatrix.ofFn]

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
/-- Width of `PolynomialMatrix.ofFn` with at least one row. -/
theorem ofFn_matrixWidth (rows width : Nat) (entry : Nat → Nat → CPolynomial F)
    (hrows : 0 < rows) :
    MatrixWidth (PolynomialMatrix.ofFn rows width entry) = width := by
  rw [PolynomialMatrix.ofFn, MatrixWidth]
  rw [show ((List.range rows).map
      (fun i ↦ ((List.range width).map (entry i)).toArray)).toArray[0]? =
      some ((List.range width).map (entry 0)).toArray from by
    rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hrows]
    simp]
  simp

/-! ## Modular reduction semantics -/

omit [Nontrivial F] [DecidableEq F] in
/-- `modByMonicWith` computes the Mathlib monic remainder under `toPoly`. -/
theorem modByMonicWith_toPoly (modCtx : CPolynomial.ModContext F)
    {p M : CPolynomial F} (hM : Polynomial.Monic M.toPoly) :
    (PolynomialMatrix.modByMonicWith modCtx p M).toPoly = p.toPoly %ₘ M.toPoly := by
  have hMne : M ≠ 0 := by
    intro hzero
    have : M.toPoly = 0 := by
      rw [hzero, CPolynomial.toPoly_zero]
    exact hM.ne_zero this
  rw [PolynomialMatrix.modByMonicWith, if_neg (by simpa using hMne),
    modCtx.modByMonic_eq_modByMonic]
  exact CPolynomial.modByMonic_toPoly_eq_modByMonic p M
    ((CPolynomial.monic_toPoly_iff M).mpr hM)

omit [Nontrivial F] [DecidableEq F] in
/-- `modByMonicWith` is congruent to the identity modulo the modulus. -/
theorem dvd_modByMonicWith_sub (modCtx : CPolynomial.ModContext F)
    {p M : CPolynomial F} (hM : Polynomial.Monic M.toPoly) :
    M.toPoly ∣ (PolynomialMatrix.modByMonicWith modCtx p M).toPoly - p.toPoly := by
  rw [modByMonicWith_toPoly modCtx hM]
  have hdecomp := Polynomial.modByMonic_add_div p.toPoly M.toPoly
  refine ⟨-(p.toPoly /ₘ M.toPoly), ?_⟩
  linear_combination hdecomp

omit [Nontrivial F] [DecidableEq F] in
/-- The executable remainder vanishes exactly on multiples of the modulus. -/
theorem modByMonicWith_eq_zero_iff_dvd (modCtx : CPolynomial.ModContext F)
    {p M : CPolynomial F} (hM : Polynomial.Monic M.toPoly) :
    PolynomialMatrix.modByMonicWith modCtx p M = 0 ↔ M.toPoly ∣ p.toPoly := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hM]
  rw [← modByMonicWith_toPoly modCtx hM]
  constructor
  · intro h
    rw [h, CPolynomial.toPoly_zero]
  · intro h
    have := (CPolynomial.toPoly_eq_zero_iff _).mp h
    exact this

/-! ## The GS modulus array -/

omit [DecidableEq F] in
private theorem gsModuli_loop (mulCtx : CPolynomial.MulContext F) (G : CPolynomial F) :
    ∀ (l : List Nat) (k : Nat),
      l.foldl
        (fun ascending _ ↦
          ascending.push (mulCtx.mul (ascending.getD (ascending.size - 1) 0) G))
        (((List.range (k + 1)).map fun i ↦ G ^ (i + 1)).toArray) =
      ((List.range (k + 1 + l.length)).map fun i ↦ G ^ (i + 1)).toArray := by
  intro l
  induction l with
  | nil =>
      intro k
      simp
  | cons a l ih =>
      intro k
      rw [List.foldl_cons]
      have hsize : (((List.range (k + 1)).map fun i ↦ G ^ (i + 1)).toArray).size = k + 1 := by
        simp
      have hget : (((List.range (k + 1)).map fun i ↦ G ^ (i + 1)).toArray).getD k 0 =
          G ^ (k + 1) := by
        rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
          List.getElem?_range (by omega)]
        simp
      rw [hsize]
      simp only [Nat.add_sub_cancel]
      rw [hget, mulCtx.mul_eq_mul, ← pow_succ]
      have hpush : (((List.range (k + 1)).map fun i ↦ G ^ (i + 1)).toArray).push
            (G ^ (k + 1 + 1)) =
          ((List.range (k + 2)).map fun i ↦ G ^ (i + 1)).toArray := by
        rw [List.push_toArray]
        congr 1
        rw [show k + 2 = (k + 1) + 1 from rfl, List.range_succ]
        simp [List.range_succ]
      rw [hpush, ih (k + 1)]
      have harg : k + 1 + 1 + l.length = k + 1 + (a :: l).length := by
        simp
        omega
      rw [harg]

omit [DecidableEq F] in
/-- Closed form for the GS modulus array before reversal. -/
theorem gsModuli_eq (mulCtx : CPolynomial.MulContext F) (G : CPolynomial F) (s : Nat) :
    gsModuli mulCtx G s = (((List.range s).map fun i ↦ G ^ (i + 1)).toArray).reverse := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    rfl
  · rw [gsModuli]
    simp only [beq_iff_eq, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one,
      List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure,
      Id.run_pure, Nat.ne_of_gt hs, if_false]
    congr 1
    have hstart : (#[G] : Array (CPolynomial F)) =
        ((List.range 1).map fun i ↦ G ^ (i + 1)).toArray := by
      simp
    rw [hstart, gsModuli_loop mulCtx G (List.range' 1 (s - 1)) 0]
    rw [List.length_range']
    congr 2
    congr 1
    omega

omit [DecidableEq F] in
/-- The GS modulus array has one modulus per multiplicity level. -/
theorem gsModuli_size (mulCtx : CPolynomial.MulContext F) (G : CPolynomial F) (s : Nat) :
    (gsModuli mulCtx G s).size = s := by
  rw [gsModuli_eq]
  simp

omit [DecidableEq F] in
/-- The `b`-th GS modulus is `G^(s-b)`. -/
theorem gsModuli_getD (mulCtx : CPolynomial.MulContext F) (G : CPolynomial F)
    {b s : Nat} (hb : b < s) :
    (gsModuli mulCtx G s).getD b 0 = G ^ (s - b) := by
  rw [gsModuli_eq]
  have hsize : ((((List.range s).map fun i ↦ G ^ (i + 1)).toArray).reverse).size = s := by
    simp
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  rw [Array.getElem_reverse]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range,
    List.size_toArray, List.length_map, List.length_range]
  congr 1
  omega

/-! ## The GS relation column -/

private def relationColumnStep (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (reducedR modulus : CPolynomial F) (b : Nat)
    (state : Array (CPolynomial F) × CPolynomial F) (j : Nat) :
    Array (CPolynomial F) × CPolynomial F :=
  (state.1.setIfInBounds j (CPolynomial.C ((j.choose b : F)) * state.2),
   PolynomialMatrix.modByMonicWith modCtx (mulCtx.mul state.2 reducedR) modulus)

omit [DecidableEq F] in
private theorem gsRelationColumn_eq_foldl (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F)
    (R modulus : CPolynomial F) (width b : Nat) :
    gsRelationColumn mulCtx modCtx R modulus width b =
      ((List.range' b (width - b)).foldl
        (relationColumnStep mulCtx modCtx
          (PolynomialMatrix.modByMonicWith modCtx R modulus) modulus b)
        (Array.replicate width (0 : CPolynomial F), 1)).1 := by
  rw [gsRelationColumn]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl,
    bind_pure_comp, map_pure, Id.run_pure]
  exact foldl_mprod_fst
    (fun col pow j ↦ col.setIfInBounds j (CPolynomial.C ((j.choose b : F)) * pow))
    (fun pow _j ↦ PolynomialMatrix.modByMonicWith modCtx
      (mulCtx.mul pow (PolynomialMatrix.modByMonicWith modCtx R modulus)) modulus)
    (List.range' b (width - b)) (Array.replicate width 0) 1

omit [Nontrivial F] [DecidableEq F] in
private theorem relationColumn_foldl_size_untouched (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (reducedR modulus : CPolynomial F) (b : Nat) :
    ∀ (n j₀ : Nat) (col : Array (CPolynomial F)) (pow : CPolynomial F),
      (((List.range' j₀ n).foldl
          (relationColumnStep mulCtx modCtx reducedR modulus b) (col, pow)).1.size =
        col.size) ∧
      (∀ j, j < j₀ →
        ((List.range' j₀ n).foldl
          (relationColumnStep mulCtx modCtx reducedR modulus b) (col, pow)).1.getD j 0 =
          col.getD j 0) := by
  intro n
  induction n with
  | zero =>
      intro j₀ col pow
      exact ⟨rfl, fun j _hj ↦ rfl⟩
  | succ n ih =>
      intro j₀ col pow
      rw [List.range'_succ, List.foldl_cons]
      have hstep : relationColumnStep mulCtx modCtx reducedR modulus b (col, pow) j₀ =
          (col.setIfInBounds j₀ (CPolynomial.C ((j₀.choose b : F)) * pow),
           PolynomialMatrix.modByMonicWith modCtx (mulCtx.mul pow reducedR) modulus) := rfl
      rw [hstep]
      rcases ih (j₀ + 1) (col.setIfInBounds j₀ (CPolynomial.C ((j₀.choose b : F)) * pow))
          (PolynomialMatrix.modByMonicWith modCtx (mulCtx.mul pow reducedR) modulus)
        with ⟨hsize, huntouched⟩
      refine ⟨by rw [hsize]; simp, ?_⟩
      intro j hj
      rw [huntouched j (by omega)]
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_ne (by omega)]

omit [Nontrivial F] [DecidableEq F] in
private theorem relationColumn_foldl_spec (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F)
    {R reducedR modulus : CPolynomial F}
    (hM : Polynomial.Monic modulus.toPoly)
    (hred : modulus.toPoly ∣ reducedR.toPoly - R.toPoly) (b : Nat) :
    ∀ (n j₀ : Nat) (col : Array (CPolynomial F)) (pow : CPolynomial F),
      b ≤ j₀ →
      modulus.toPoly ∣ pow.toPoly - R.toPoly ^ (j₀ - b) →
      (((List.range' j₀ n).foldl
          (relationColumnStep mulCtx modCtx reducedR modulus b) (col, pow)).1.size =
        col.size) ∧
      (∀ j, j < j₀ ∨ j₀ + n ≤ j →
        ((List.range' j₀ n).foldl
          (relationColumnStep mulCtx modCtx reducedR modulus b) (col, pow)).1.getD j 0 =
          col.getD j 0) ∧
      (∀ j, j₀ ≤ j → j < j₀ + n → j < col.size →
        modulus.toPoly ∣
          (((List.range' j₀ n).foldl
            (relationColumnStep mulCtx modCtx reducedR modulus b) (col, pow)).1.getD j 0).toPoly -
            Polynomial.C ((j.choose b : F)) * R.toPoly ^ (j - b)) := by
  intro n
  induction n with
  | zero =>
      intro j₀ col pow _hb _hpow
      refine ⟨rfl, fun j _hj ↦ rfl, fun j hj₁ hj₂ _hj₃ ↦ ?_⟩
      omega
  | succ n ih =>
      intro j₀ col pow hb hpow
      rw [List.range'_succ, List.foldl_cons]
      set col' := col.setIfInBounds j₀ (CPolynomial.C ((j₀.choose b : F)) * pow) with hcol'
      set pow' := PolynomialMatrix.modByMonicWith modCtx (mulCtx.mul pow reducedR) modulus
        with hpow'
      have hstep : relationColumnStep mulCtx modCtx reducedR modulus b (col, pow) j₀ =
          (col', pow') := rfl
      rw [hstep]
      have hpow'spec : modulus.toPoly ∣ pow'.toPoly - R.toPoly ^ (j₀ + 1 - b) := by
        have hmul : modulus.toPoly ∣
            (mulCtx.mul pow reducedR).toPoly - R.toPoly ^ (j₀ - b) * R.toPoly := by
          rw [mulCtx.mul_eq_mul, CPolynomial.toPoly_mul]
          have hexpand : pow.toPoly * reducedR.toPoly -
              R.toPoly ^ (j₀ - b) * R.toPoly =
              pow.toPoly * (reducedR.toPoly - R.toPoly) +
                (pow.toPoly - R.toPoly ^ (j₀ - b)) * R.toPoly := by
            ring
          rw [hexpand]
          exact dvd_add (Dvd.dvd.mul_left hred _) (Dvd.dvd.mul_right hpow _)
        have hmod := dvd_modByMonicWith_sub modCtx
          (p := mulCtx.mul pow reducedR) (M := modulus) hM
        have hcomb := dvd_add hmod hmul
        have hrw : (PolynomialMatrix.modByMonicWith modCtx (mulCtx.mul pow reducedR)
            modulus).toPoly - (mulCtx.mul pow reducedR).toPoly +
            ((mulCtx.mul pow reducedR).toPoly - R.toPoly ^ (j₀ - b) * R.toPoly) =
            (PolynomialMatrix.modByMonicWith modCtx (mulCtx.mul pow reducedR)
              modulus).toPoly - R.toPoly ^ (j₀ - b) * R.toPoly := by
          ring
        rw [hrw] at hcomb
        rw [hpow']
        have hpowsucc : R.toPoly ^ (j₀ - b) * R.toPoly = R.toPoly ^ (j₀ + 1 - b) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [← hpowsucc]
        exact hcomb
      rcases ih (j₀ + 1) col' pow' (by omega) hpow'spec with ⟨hsize, huntouched, hspec⟩
      have hcol'size : col'.size = col.size := by
        rw [hcol']
        simp
      refine ⟨by rw [hsize, hcol'size], ?_, ?_⟩
      · intro j hj
        have hj' : j < j₀ + 1 ∨ j₀ + 1 + n ≤ j := by omega
        rw [huntouched j hj']
        rw [hcol']
        rcases hj with hj | hj
        · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
          rw [Array.getElem?_setIfInBounds_ne (by omega)]
        · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
          rw [Array.getElem?_setIfInBounds_ne (by omega)]
      · intro j hj₁ hj₂ hj₃
        by_cases hj : j = j₀
        · subst hj
          have huntouchedj : ((List.range' (j + 1) n).foldl
              (relationColumnStep mulCtx modCtx reducedR modulus b) (col', pow')).1.getD j 0 =
              col'.getD j 0 := huntouched j (by omega)
          rw [huntouchedj, hcol']
          have hset : (col.setIfInBounds j
              (CPolynomial.C ((j.choose b : F)) * pow)).getD j 0 =
              CPolynomial.C ((j.choose b : F)) * pow := by
            rw [Array.getD_eq_getD_getElem?,
              Array.getElem?_setIfInBounds_self_of_lt (by omega)]
            simp
          rw [hset]
          rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly]
          have hfactor : Polynomial.C ((j.choose b : F)) * pow.toPoly -
              Polynomial.C ((j.choose b : F)) * R.toPoly ^ (j - b) =
              Polynomial.C ((j.choose b : F)) * (pow.toPoly - R.toPoly ^ (j - b)) := by
            ring
          rw [hfactor]
          exact Dvd.dvd.mul_left hpow _
        · exact hspec j (by omega) (by omega) (by rw [hcol'size]; exact hj₃)

omit [DecidableEq F] in
/-- Size of the GS relation column. -/
theorem gsRelationColumn_size (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R modulus : CPolynomial F) (width b : Nat) :
    (gsRelationColumn mulCtx modCtx R modulus width b).size = width := by
  rw [gsRelationColumn_eq_foldl]
  rw [(relationColumn_foldl_size_untouched mulCtx modCtx
      (PolynomialMatrix.modByMonicWith modCtx R modulus) modulus b (width - b) b
      (Array.replicate width 0) 1).1]
  simp

omit [DecidableEq F] in
/-- Entries of the GS relation column below the diagonal vanish. -/
theorem gsRelationColumn_getD_of_lt (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R modulus : CPolynomial F)
    {width b j : Nat} (hj : j < b) :
    (gsRelationColumn mulCtx modCtx R modulus width b).getD j 0 = 0 := by
  rw [gsRelationColumn_eq_foldl]
  rw [(relationColumn_foldl_size_untouched mulCtx modCtx
      (PolynomialMatrix.modByMonicWith modCtx R modulus) modulus b (width - b) b
      (Array.replicate width 0) 1).2 j hj]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

omit [DecidableEq F] in
/-- Entries of the GS relation column are congruent to the binomial powers. -/
theorem gsRelationColumn_getD_congr (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) {R modulus : CPolynomial F}
    (hM : Polynomial.Monic modulus.toPoly)
    {width b j : Nat} (hbj : b ≤ j) (hj : j < width) :
    modulus.toPoly ∣
      ((gsRelationColumn mulCtx modCtx R modulus width b).getD j 0).toPoly -
        Polynomial.C ((j.choose b : F)) * R.toPoly ^ (j - b) := by
  rw [gsRelationColumn_eq_foldl]
  have hred := dvd_modByMonicWith_sub modCtx (p := R) (M := modulus) hM
  rcases relationColumn_foldl_spec mulCtx modCtx (R := R)
      (reducedR := PolynomialMatrix.modByMonicWith modCtx R modulus)
      (modulus := modulus) hM hred b (width - b) b (Array.replicate width 0) 1
      le_rfl (by simp [CPolynomial.toPoly_one]) with ⟨_, _, hspec⟩
  exact hspec j hbj (by omega) (by simpa using hj)

/-! ## The GS relation matrix and the modular row predicate -/

omit [DecidableEq F] in
/-- The `b`-th GS modulus is `G^(s-b)`, with default value `1`. -/
theorem gsModuli_getD_one (mulCtx : CPolynomial.MulContext F) (G : CPolynomial F)
    {b s : Nat} (hb : b < s) :
    (gsModuli mulCtx G s).getD b 1 = G ^ (s - b) := by
  have hsize : (gsModuli mulCtx G s).size = s := gsModuli_size mulCtx G s
  have h0 := gsModuli_getD mulCtx G hb
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
    Option.getD_some] at h0 ⊢
  exact h0

omit [DecidableEq F] in
/-- Entry access for the GS relation matrix. -/
theorem gsRelationMatrixWithModuli_entry (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R : CPolynomial F)
    (moduli : Array (CPolynomial F)) (params : GSInterpParams) {k b : Nat}
    (hk : k < interpolationWidth params) (hb : b < params.multiplicity) :
    rowGet ((gsRelationMatrixWithModuli mulCtx modCtx R moduli params).getD k #[]) b =
      (gsRelationColumn mulCtx modCtx R (moduli.getD b 1)
        (interpolationWidth params) b).getD k 0 := by
  rw [gsRelationMatrixWithModuli, ofFn_rowGet _ _ _ hk hb]
  congr 1
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hb, Option.map_some, Option.getD_some]

omit [DecidableEq F] in
/-- The GS relation matrix has one row per interpolation coefficient. -/
theorem gsRelationMatrixWithModuli_size (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R : CPolynomial F)
    (moduli : Array (CPolynomial F)) (params : GSInterpParams) :
    (gsRelationMatrixWithModuli mulCtx modCtx R moduli params).size =
      interpolationWidth params :=
  ofFn_size _ _ _

omit [DecidableEq F] in
/-- The GS relation matrix has one column per multiplicity level. -/
theorem gsRelationMatrixWithModuli_matrixWidth (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R : CPolynomial F)
    (moduli : Array (CPolynomial F)) (params : GSInterpParams) :
    MatrixWidth (gsRelationMatrixWithModuli mulCtx modCtx R moduli params) =
      params.multiplicity :=
  ofFn_matrixWidth _ _ _ (Nat.succ_pos _)

omit [Nontrivial F] [DecidableEq F] in
/-- Outer-coefficient expansion of a coefficient row under `toPoly`. -/
private theorem toPoly_ofCoeffRow_eq_sum (row : PolynomialRow F) :
    (CBivariate.ofCoeffRow row).toPoly =
      ∑ k ∈ Finset.range row.size,
        Polynomial.monomial k ((row.getD k 0).toPoly) := by
  ext n
  rw [CBivariate.toPoly_coeff, Polynomial.finsetSum_coeff]
  by_cases hn : n < row.size
  · rw [Finset.sum_eq_single n
      (fun k _hk hkn ↦ by rw [Polynomial.coeff_monomial, if_neg hkn])
      (fun hnotin ↦ absurd (Finset.mem_range.mpr hn) hnotin)]
    rw [Polynomial.coeff_monomial, if_pos rfl, CBivariate.ofCoeffRow,
      CPolynomial.coeff_ofArray]
  · rw [Finset.sum_eq_zero
      (fun k hk ↦ by
        rw [Polynomial.coeff_monomial,
          if_neg (by rcases Finset.mem_range.mp hk with h; omega)])]
    rw [CBivariate.ofCoeffRow, CPolynomial.coeff_ofArray,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp [CPolynomial.toPoly_zero]

omit [Nontrivial F] [DecidableEq F] in
/-- Sheared coefficients of a coefficient row: the outer Hasse derivative of
`ofCoeffRow row` evaluated at `R` is the binomial-weighted power sum. -/
theorem hasseDeriv_toPoly_ofCoeffRow_eval (row : PolynomialRow F)
    (R : Polynomial F) (b : Nat) :
    (Polynomial.hasseDeriv b (CBivariate.ofCoeffRow row).toPoly).eval R =
      ∑ k ∈ Finset.range row.size,
        Polynomial.C ((k.choose b : F)) * (row.getD k 0).toPoly * R ^ (k - b) := by
  rw [toPoly_ofCoeffRow_eq_sum, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _hk ↦ ?_
  rw [Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial,
    Polynomial.C_eq_natCast]

omit [Nontrivial F] [DecidableEq F] in
/-- Column entries of a row-by-matrix product as binomial sums. -/
private theorem rowGet_rowMulMatrixWith_eq_sum (mulCtx : CPolynomial.MulContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F) {j : Nat}
    (hj : j < MatrixWidth M) :
    rowGet (rowMulMatrixWith mulCtx row M) j =
      ∑ k ∈ Finset.range row.size, rowGet row k * rowGet (M.getD k #[]) j := by
  rw [rowMulMatrixWith, rowGet]
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]
  rw [foldl_add_eq_sum (fun k ↦ mulCtx.mul (rowGet row k) (rowGet (M.getD k #[]) j))]
  refine Finset.sum_congr rfl fun k _hk ↦ ?_
  rw [mulCtx.mul_eq_mul]

omit [Nontrivial F] [DecidableEq F] in
/-- One product-entry fold as a sum over the matrix height. -/
private theorem rowMulMatrix_foldl_eq_sum_size (mulCtx : CPolynomial.MulContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F) (j : Nat) :
    (List.range row.size).foldl
        (fun acc k ↦ acc + mulCtx.mul (rowGet row k) (rowGet (M.getD k #[]) j)) 0 =
      ∑ k ∈ Finset.range M.size, rowGet row k * rowGet (M.getD k #[]) j := by
  rw [foldl_add_eq_sum (fun k ↦ mulCtx.mul (rowGet row k) (rowGet (M.getD k #[]) j))]
  have hterm : ∀ k, mulCtx.mul (rowGet row k) (rowGet (M.getD k #[]) j) =
      rowGet row k * rowGet (M.getD k #[]) j := fun k ↦ mulCtx.mul_eq_mul _ _
  simp only [hterm]
  rcases Nat.le_total row.size M.size with h | h
  · refine Finset.sum_subset
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) fun k _hk hknot ↦ ?_
    have hk : row.size ≤ k := by simpa using hknot
    have hzero : rowGet row k = 0 := by
      rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hk]
      rfl
    rw [hzero, zero_mul]
  · symm
    refine Finset.sum_subset
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) fun k _hk hknot ↦ ?_
    have hk : M.size ≤ k := by simpa using hknot
    have hzero : M.getD k #[] = #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hk]
      rfl
    rw [hzero, show rowGet (#[] : PolynomialRow F) j = 0 from rfl, mul_zero]

omit [Nontrivial F] [DecidableEq F] in
/-- The row-by-matrix product only sees the first `M.size` row entries. -/
theorem rowMulMatrixWith_congr_of_agree (mulCtx : CPolynomial.MulContext F)
    {row row' : PolynomialRow F} (M : PolynomialMatrix F)
    (hagree : ∀ k, k < M.size → rowGet row k = rowGet row' k) :
    rowMulMatrixWith mulCtx row M = rowMulMatrixWith mulCtx row' M := by
  rw [rowMulMatrixWith, rowMulMatrixWith]
  congr 1
  refine List.map_congr_left fun j _hj ↦ ?_
  rw [rowMulMatrix_foldl_eq_sum_size, rowMulMatrix_foldl_eq_sum_size]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [hagree k (Finset.mem_range.mp hk)]

omit [Nontrivial F] [DecidableEq F] in
/-- The modular row predicate only sees the first `M.size` row entries. -/
theorem rowSatisfiesModularBool_congr_of_agree (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) {row row' : PolynomialRow F}
    (M : PolynomialMatrix F) (moduli : Array (CPolynomial F))
    (hagree : ∀ k, k < M.size → rowGet row k = rowGet row' k) :
    rowSatisfiesModularBool mulCtx modCtx row M moduli =
      rowSatisfiesModularBool mulCtx modCtx row' M moduli := by
  rw [rowSatisfiesModularBool, rowSatisfiesModularBool, rowMulMatrixModDiagonalWith,
    rowMulMatrixModDiagonalWith, rowMulMatrixWith_congr_of_agree mulCtx M hagree]

omit [Nontrivial F] [DecidableEq F] in
/-- The executable modular row predicate, columnwise. -/
private theorem rowSatisfiesModularBool_iff_forall (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (row : PolynomialRow F)
    (M : PolynomialMatrix F) (moduli : Array (CPolynomial F)) :
    rowSatisfiesModularBool mulCtx modCtx row M moduli = true ↔
      ∀ b, b < moduli.size →
        PolynomialMatrix.modByMonicWith modCtx
          (rowGet (rowMulMatrixWith mulCtx row M) b) (moduli.getD b 0) = 0 := by
  rw [rowSatisfiesModularBool, rowMulMatrixModDiagonalWith, rowModDiagonalWith]
  rw [Array.all_eq_true]
  constructor
  · intro h b hb
    have hb' : b < (((List.range moduli.size).map fun j ↦
        PolynomialMatrix.modByMonicWith modCtx
          (rowGet (rowMulMatrixWith mulCtx row M) j) (moduli.getD j 0)).toArray).size := by
      simpa using hb
    have := h b hb'
    simpa using this
  · intro h b hb
    have hb' : b < moduli.size := by simpa using hb
    simpa using h b hb'

omit [DecidableEq F] in
/-- The executable GS modular row predicate over the relation matrix and
modulus array is exactly divisibility of every sheared coefficient
`(hasseDeriv b (ofCoeffRow row).toPoly).eval R` by `G^(s-b)`. -/
theorem rowSatisfiesModularBool_gsRelationMatrix_iff
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    {G : CPolynomial F} (hG : Polynomial.Monic G.toPoly)
    (R : CPolynomial F) (params : GSInterpParams) {row : PolynomialRow F}
    (hwidth : row.size ≤ interpolationWidth params) :
    rowSatisfiesModularBool mulCtx modCtx row
        (gsRelationMatrixWithRG mulCtx modCtx R G params)
        (gsModuli mulCtx G params.multiplicity) = true ↔
      ∀ b, b < params.multiplicity →
        G.toPoly ^ (params.multiplicity - b) ∣
          (Polynomial.hasseDeriv b (CBivariate.ofCoeffRow row).toPoly).eval R.toPoly := by
  set s := params.multiplicity with hs
  set width := interpolationWidth params with hwidthdef
  set M := gsRelationMatrixWithRG mulCtx modCtx R G params with hM
  have hMsize : MatrixWidth M = s :=
    gsRelationMatrixWithModuli_matrixWidth mulCtx modCtx R _ params
  have hmodsize : (gsModuli mulCtx G s).size = s := gsModuli_size mulCtx G s
  rw [rowSatisfiesModularBool_iff_forall, hmodsize]
  refine forall_congr' fun b ↦ ?_
  refine imp_congr_right fun hb ↦ ?_
  have hmonic : Polynomial.Monic ((G ^ (s - b)).toPoly) := by
    rw [CPolynomial.toPoly_pow]
    exact hG.pow _
  rw [gsModuli_getD mulCtx G hb]
  rw [modByMonicWith_eq_zero_iff_dvd modCtx hmonic]
  rw [CPolynomial.toPoly_pow]
  rw [hasseDeriv_toPoly_ofCoeffRow_eval]
  have hentry : ∀ k, k < row.size →
      G.toPoly ^ (s - b) ∣
        (rowGet row k * rowGet (M.getD k #[]) b).toPoly -
          Polynomial.C ((k.choose b : F)) * (rowGet row k).toPoly *
            R.toPoly ^ (k - b) := by
    intro k hk
    have hkwidth : k < width := by omega
    have hMk : rowGet (M.getD k #[]) b =
        (gsRelationColumn mulCtx modCtx R (G ^ (s - b)) width b).getD k 0 := by
      rw [hM, gsRelationMatrixWithRG,
        gsRelationMatrixWithModuli_entry mulCtx modCtx R _ params hkwidth hb,
        gsModuli_getD_one mulCtx G hb]
    rw [hMk, CPolynomial.toPoly_mul]
    rcases Nat.lt_or_ge k b with hkb | hkb
    · rw [gsRelationColumn_getD_of_lt mulCtx modCtx R (G ^ (s - b)) hkb]
      rw [Nat.choose_eq_zero_of_lt hkb]
      simp [CPolynomial.toPoly_zero]
    · have hcongr := gsRelationColumn_getD_congr mulCtx modCtx
        (R := R) (modulus := G ^ (s - b)) hmonic hkb hkwidth
      have hmul := Dvd.dvd.mul_left hcongr (rowGet row k).toPoly
      have hexpand : (rowGet row k).toPoly *
          (((gsRelationColumn mulCtx modCtx R (G ^ (s - b)) width b).getD k 0).toPoly -
            Polynomial.C ((k.choose b : F)) * R.toPoly ^ (k - b)) =
          (rowGet row k).toPoly *
            ((gsRelationColumn mulCtx modCtx R (G ^ (s - b)) width b).getD k 0).toPoly -
            Polynomial.C ((k.choose b : F)) * (rowGet row k).toPoly *
              R.toPoly ^ (k - b) := by
        ring
      rw [hexpand] at hmul
      rwa [CPolynomial.toPoly_pow] at hmul
  have hsum : G.toPoly ^ (s - b) ∣
      (rowGet (rowMulMatrixWith mulCtx row M) b).toPoly -
        ∑ k ∈ Finset.range row.size,
          Polynomial.C ((k.choose b : F)) * (rowGet row k).toPoly *
            R.toPoly ^ (k - b) := by
    rw [rowGet_rowMulMatrixWith_eq_sum mulCtx row M (by omega)]
    rw [toPoly_finset_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun k hk ↦ hentry k (Finset.mem_range.mp hk)
  rw [dvd_iff_dvd_of_dvd_sub hsum]
  congr! 1

end ApproximantBasis

end GuruswamiSudan

end CompPoly

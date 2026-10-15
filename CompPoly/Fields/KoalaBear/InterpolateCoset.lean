/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.KoalaBear.FastExt4
public import CompPoly.Data.List.BatchInv
public import CompPoly.Univariate.NTT.CosetBarycentric

/-!
# Evaluating KoalaBear polynomials from coset values at an extension point

`KoalaBear.Fast.interpolateCoset` is Plonky3's `interpolate_coset` for KoalaBear and its quartic
extension. Given a row-major `2^logN × width` matrix whose column `j` holds the values of a
polynomial `pⱼ` of degree below `2^logN` on the coset `s · ⟨ω⟩`, it returns `pⱼ(z)` for every
column, for a point `z` of the extension outside the coset:

`pⱼ(z) = (zⁿ - sⁿ) / (n sⁿ) · ∑ᵢ xᵢ / (z - xᵢ) · pⱼ(xᵢ)`, with `xᵢ = s ωⁱ`.

The weights `xᵢ / (z - xᵢ)` are shared by all columns and need one batch inversion.
`toSpec_interpolateCoset` proves the result equal to `aeval z pⱼ`.
-/

@[expose] public section

namespace KoalaBear.Fast

open CompPoly CompPoly.Extension Montgomery.Native32 Polynomial

namespace Ext4

/-- `z ^ 2 ^ k`, by squaring. -/
def powTwo (z : Ext4) : ℕ → Ext4
  | 0 => z
  | k + 1 => powTwo (z * z) k

theorem toSpec_powTwo (z : Ext4) (k : ℕ) : toSpec (powTwo z k) = toSpec z ^ 2 ^ k := by
  induction k generalizing z with
  | zero => rw [powTwo, pow_zero, pow_one]
  | succ k ih =>
    rw [powTwo, ih, toSpec_mul]
    apply Ext.toQuot_injective
    rw [Ext.toQuot_pow, Ext.toQuot_pow, Ext.toQuot_mul, ← pow_two, ← pow_mul, Nat.pow_succ']

theorem toSpec_foldl_add (n : ℕ) (g : Fin n → Ext4) (a : Ext4) :
    toSpec (Fin.foldl n (fun acc i ↦ acc + g i) a) = toSpec a + ∑ i, toSpec (g i) := by
  induction n generalizing a with
  | zero => simp only [Fin.foldl_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, ih, Fin.sum_univ_succ, toSpec_add, add_assoc]

end Ext4

/-- The nodes `s, s ω, s ω², …` of a coset. -/
def cosetNodes (ω s : Field) (n : ℕ) : List Field := List.prefixProducts s (List.replicate n ω)

/-- The weights `xᵢ / (z - xᵢ)` of the coset nodes, with one batch inversion. -/
def cosetWeights (ω s : Field) (n : ℕ) (z : Ext4) : List Ext4 :=
  List.zipWith Ext4.smul (cosetNodes ω s n)
    (List.batchInv ((cosetNodes ω s n).map fun x ↦ z - Ext4.ofBase x))

/-- The scale `(zⁿ - sⁿ) / (n sⁿ)` for `n = 2^logN`. -/
def cosetFactor (logN : ℕ) (s : Field) (z : Ext4) : Ext4 :=
  let sn := Montgomery.Native32.pow s (2 ^ logN)
  (Ext4.powTwo z logN - Ext4.ofBase sn) * (Ext4.ofBase (((2 ^ logN : ℕ) : Field) * sn))⁻¹

/-- Evaluate each column of a row-major `2^logN × width` matrix of values on the coset `s · ⟨ω⟩`
at `z`. -/
def interpolateCoset (logN : ℕ) (ω s : Field) (width : ℕ) (evals : Array Field) (z : Ext4) :
    Array Ext4 :=
  let n := 2 ^ logN
  let weights := (cosetWeights ω s n z).toArray
  let factor := cosetFactor logN s z
  Array.ofFn (n := width) fun j ↦
    factor * Fin.foldl n
      (fun acc i ↦ acc + Ext4.smul (evals.getD (i * width + j) 0) (weights.getD i 0)) 0

/-! ### Correctness -/

section Nodes

variable {M : Type*} [CommMonoid M]

theorem getElem_prefixProducts_replicate (q w : M) (n i : ℕ)
    (hi : i < (List.prefixProducts q (List.replicate n w)).length) :
    (List.prefixProducts q (List.replicate n w))[i] = q * w ^ i := by
  induction n generalizing q i with
  | zero => simp [List.prefixProducts] at hi
  | succ n ih =>
    cases i with
    | zero => simp only [List.replicate_succ, List.prefixProducts, List.getElem_cons_zero,
        pow_zero, mul_one]
    | succ i =>
      simp only [List.replicate_succ, List.prefixProducts, List.getElem_cons_succ]
      rw [ih, pow_succ', mul_assoc]

end Nodes

theorem length_cosetNodes (ω s : Field) (n : ℕ) : (cosetNodes ω s n).length = n := by
  rw [cosetNodes, List.length_prefixProducts, List.length_replicate]

theorem toField_getElem_cosetNodes (ω s : Field) (n i : ℕ) (hi : i < (cosetNodes ω s n).length) :
    FastField.toField (cosetNodes ω s n)[i] = FastField.toField s * FastField.toField ω ^ i := by
  have h := List.prefixProducts_map FastField.toField (fun a b ↦ toField_mul a b) s
    (List.replicate n ω)
  rw [List.map_replicate] at h
  have hi' : i < (List.prefixProducts (FastField.toField s)
      (List.replicate n (FastField.toField ω))).length := by
    rw [List.length_prefixProducts, List.length_replicate]; rwa [length_cosetNodes] at hi
  have e := congrArg (·[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi'] at e
  rw [List.getElem?_eq_getElem (by rwa [cosetNodes] at hi), Option.map_some, Option.some.injEq,
    getElem_prefixProducts_replicate] at e
  exact e.symm

theorem length_cosetWeights (ω s : Field) (n : ℕ) (z : Ext4) :
    (cosetWeights ω s n z).length = n := by
  rw [cosetWeights, List.length_zipWith, List.length_batchInv, List.length_map, length_cosetNodes,
    min_self]

/-- The `i`-th coset node in the spec field. -/
abbrev specNode (ω s : Field) (i : ℕ) : KoalaBear.Field :=
  FastField.toField s * FastField.toField ω ^ i

theorem toSpec_getElem_cosetWeights (ω s : Field) (n : ℕ) (z : Ext4)
    (hz : ∀ i < n, Ext4.toSpec z ≠ Ext.ofBase (specNode ω s i)) (i : ℕ)
    (hi : i < (cosetWeights ω s n z).length) :
    Ext4.toSpec (cosetWeights ω s n z)[i] =
      Ext.ofBase (specNode ω s i) * (Ext4.toSpec z - Ext.ofBase (specNode ω s i))⁻¹ := by
  have hin : i < n := by rwa [length_cosetWeights] at hi
  have hnode : i < (cosetNodes ω s n).length := by rw [length_cosetNodes]; exact hin
  set diffs := (cosetNodes ω s n).map fun x ↦ z - Ext4.ofBase x
  have hdiffs : ∀ k (hk : k < diffs.length),
      Ext4.toSpec diffs[k] = Ext4.toSpec z - Ext.ofBase (specNode ω s k) := by
    intro k hk
    simp only [diffs, List.getElem_map, Ext4.toSpec_sub, Ext4.toSpec_ofBase]
    rw [toField_getElem_cosetNodes]
  have hne : ∀ x ∈ diffs.map Ext4.toSpec, x ≠ 0 := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.getElem_map, hdiffs, sub_ne_zero]
    apply hz
    simpa [diffs, length_cosetNodes] using hk
  have hb := List.batchInv_map Ext4.toSpec Ext4.toSpec_mul Ext4.toSpec_inv Ext4.toSpec_one diffs
  rw [List.batchInv_eq _ hne] at hb
  have hdi : i < diffs.length := by simpa [diffs] using hnode
  have hbi : i < (List.batchInv diffs).length := by rwa [List.length_batchInv]
  have e := congrArg (·[i]?) hb
  simp only [List.getElem?_map, List.getElem?_eq_getElem hdi, List.getElem?_eq_getElem hbi,
    Option.map_some, Option.some.injEq] at e
  simp only [cosetWeights, List.getElem_zipWith, Ext4.toSpec_smul, Algebra.smul_def,
    Ext.algebraMap_eq_ofBase, toField_getElem_cosetNodes]
  rw [← e, hdiffs]

theorem size_interpolateCoset (logN : ℕ) (ω s : Field) (width : ℕ) (evals : Array Field)
    (z : Ext4) : (interpolateCoset logN ω s width evals z).size = width := by
  simp only [interpolateCoset, Array.size_ofFn]

/-- Each output of `interpolateCoset` is the scale times a sum over the rows, for `z` off the
nodes. -/
theorem toSpec_getElem_interpolateCoset (logN : ℕ) (ω s : Field) (width : ℕ)
    (evals : Array Field) (z : Ext4)
    (hz : ∀ i < 2 ^ logN, Ext4.toSpec z ≠ Ext.ofBase (specNode ω s i)) (j : ℕ) (hj : j < width) :
    Ext4.toSpec ((interpolateCoset logN ω s width evals z)[j]'(by
      rw [size_interpolateCoset]; exact hj)) =
      Ext4.toSpec (cosetFactor logN s z) * ∑ i ∈ Finset.range (2 ^ logN),
        FastField.toField (evals.getD (i * width + j) 0) •
          (Ext.ofBase (specNode ω s i) * (Ext4.toSpec z - Ext.ofBase (specNode ω s i))⁻¹) := by
  simp only [interpolateCoset]
  rw [Array.getElem_ofFn, Ext4.toSpec_mul, Ext4.toSpec_foldl_add, Ext4.toSpec_zero, zero_add,
    Fin.sum_univ_eq_sum_range (fun i ↦ Ext4.toSpec (Ext4.smul (evals.getD (i * width + j) 0)
      ((cosetWeights ω s (2 ^ logN) z).toArray.getD i 0)))]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun i hi ↦ ?_)
  have hi' : i < (cosetWeights ω s (2 ^ logN) z).length := by
    rw [length_cosetWeights]; exact Finset.mem_range.mp hi
  have hw : (cosetWeights ω s (2 ^ logN) z).toArray.getD i 0 =
      (cosetWeights ω s (2 ^ logN) z)[i] := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hi',
      Option.getD_some]
  rw [hw, Ext4.toSpec_smul, toSpec_getElem_cosetWeights ω s _ z hz i hi']

/-- A point whose `n`-th power differs from `sⁿ` is off every node of the coset `s · ⟨ω⟩`. -/
theorem toSpec_ne_specNode (D : CPolynomial.NTT.Domain KoalaBear.Field) (ω s : Field)
    (hω : FastField.toField ω = D.omega) (z : Ext4)
    (hz : Ext4.toSpec z ^ D.n ≠
      algebraMap KoalaBear.Field KoalaBear.Ext4 (FastField.toField s) ^ D.n) :
    ∀ i < D.n, Ext4.toSpec z ≠ Ext.ofBase (specNode ω s i) := by
  intro i hi h
  apply hz
  have := D.cosetNode_pow_n (E := KoalaBear.Ext4) (FastField.toField s) ⟨i, hi⟩
  rw [h, ← Ext.algebraMap_eq_ofBase, ← this]
  simp only [CPolynomial.NTT.Domain.cosetNode, CPolynomial.NTT.Domain.node, hω, specNode]

/-- **Correctness of `interpolateCoset`.** If column `j` holds the values of `pⱼ`, of degree below
`n`, on the coset `s · ⟨ω⟩`, and `z` lies outside the coset, then output `j` is `pⱼ(z)`. -/
theorem toSpec_interpolateCoset (D : CPolynomial.NTT.Domain KoalaBear.Field) (ω s : Field)
    (hω : FastField.toField ω = D.omega) (hs : FastField.toField s ≠ 0) (width : ℕ)
    (evals : Array Field) (z : Ext4)
    (hz : Ext4.toSpec z ^ D.n ≠
      algebraMap KoalaBear.Field KoalaBear.Ext4 (FastField.toField s) ^ D.n)
    (p : Fin width → KoalaBear.Field[X]) (hp : ∀ j, (p j).degree < D.n)
    (hevals : ∀ (i : D.Idx) (j : Fin width),
      FastField.toField (evals.getD (i * width + j) 0) =
        (p j).eval (FastField.toField s * D.node i))
    (j : Fin width) :
    Ext4.toSpec ((interpolateCoset D.logN ω s width evals z)[j.val]'(by
      rw [size_interpolateCoset]; exact j.isLt)) = aeval (Ext4.toSpec z) (p j) := by
  have hz' := toSpec_ne_specNode D ω s hω z hz
  rw [CPolynomial.NTT.Domain.aeval_eq_cosetBarycentric D hs (p j) (hp j) _ hz]
  simp only [interpolateCoset, cosetFactor]
  rw [Array.getElem_ofFn, Ext4.toSpec_mul, Ext4.toSpec_foldl_add, Ext4.toSpec_zero, zero_add,
    Ext4.toSpec_mul, Ext4.toSpec_sub, Ext4.toSpec_powTwo, Ext4.toSpec_ofBase, Ext4.toSpec_inv,
    Ext4.toSpec_ofBase,
    toField_mul, toField_natCast, toField_pow]
  simp only [← Ext.algebraMap_eq_ofBase, map_mul, map_pow, map_natCast]
  refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun i _ ↦ ?_)
  have hi : (i : ℕ) < (cosetWeights ω s (2 ^ D.logN) z).length := by
    rw [length_cosetWeights]; exact i.isLt
  have hw : (cosetWeights ω s (2 ^ D.logN) z).toArray.getD i 0 =
      (cosetWeights ω s (2 ^ D.logN) z)[(i : ℕ)] := by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hi,
      Option.getD_some]
  rw [hw, Ext4.toSpec_smul, Algebra.smul_def,
    toSpec_getElem_cosetWeights ω s (2 ^ D.logN) z hz' i hi, hevals i j]
  simp only [Ext.algebraMap_eq_ofBase, CPolynomial.NTT.Domain.cosetNode, specNode, hω,
    CPolynomial.NTT.Domain.node]
  ring

end KoalaBear.Fast

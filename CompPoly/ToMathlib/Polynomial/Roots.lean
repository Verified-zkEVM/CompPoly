/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
import Mathlib.Algebra.Polynomial.Roots

/-!
# Root sets of products of distinct linear factors

- `∏ i ∈ s, (X - C (a i))` over injectively indexed points: it divides every polynomial
vanishing on the points (`prod_X_sub_C_dvd`)
- A nonzero polynomial vanishes at boundedly many of the points (`card_eval_zero_le_natDegree`)
- The product divides `(∏ i ∈ E, (X - C (a i))) * (f - b)` whenever `f` and `b` agree off `E`
(`prod_X_sub_C_dvd_prod_mul_sub`).
-/

namespace Polynomial

variable {R : Type*}

/-- `∏ i ∈ s, (X - aᵢ)` divides `p` when the distinct `aᵢ` are all roots of `p`. -/
lemma prod_X_sub_C_dvd [Field R]
    {ι : Type*} (s : Finset ι) (a : ι → R) (hinj : Set.InjOn a s)
    (p : R[X]) (hr : ∀ i ∈ s, p.eval (a i) = 0) :
    (∏ i ∈ s, (X - C (a i))) ∣ p :=
  Finset.prod_dvd_of_coprime
    (fun _ hi _ hj hij =>
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hij <| hinj hi hj ·)).isUnit)
    (fun i hi => dvd_iff_isRoot.mpr (hr i hi))

/-- A nonzero `v` vanishes at at most `v.natDegree` of the distinct points. -/
lemma card_eval_zero_le_natDegree [CommRing R] [IsDomain R]
    {ι : Type*} [DecidableEq R] (s : Finset ι) (a : ι → R)
    (hinj : Set.InjOn a s) (v : R[X]) (hv : v ≠ 0) :
    {i ∈ s | v.eval (a i) = 0}.card ≤ v.natDegree := by
  rw [← Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
  refine card_le_degree_of_subset_roots fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact (mem_roots hv).mpr (Finset.mem_filter.mp hi).2

/-- When `f, b` agree off `E ⊆ s`, the product `∏_{i∈s}(X−aᵢ)` divides
`(∏_{i∈E}(X−aᵢ))·(f − b)`. -/
lemma prod_X_sub_C_dvd_prod_mul_sub [Field R] {ι : Type*} [DecidableEq ι]
    (s E : Finset ι) (hE : E ⊆ s) (a : ι → R) (hinj : Set.InjOn a s)
    (f b : R[X]) (hagree : ∀ i ∈ s \ E, f.eval (a i) = b.eval (a i)) :
    (∏ i ∈ s, (X - C (a i))) ∣ (∏ i ∈ E, (X - C (a i))) * (f - b) := by
  rw [← Finset.prod_sdiff hE, mul_comm]
  exact mul_dvd_mul_left _ (prod_X_sub_C_dvd _ _
    (hinj.mono (Finset.coe_subset.mpr Finset.sdiff_subset)) _
    fun i hi => by rw [eval_sub, hagree i hi, sub_self])

end Polynomial

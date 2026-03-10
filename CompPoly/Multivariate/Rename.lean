/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Multivariate.Operations
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Properties of variable renaming for `CMvPolynomial`

This file proves properties of the `rename` function defined in `CMvPolynomial.lean`,
by transferring results from Mathlib's `MvPolynomial.rename` through the
`polyRingEquiv : CMvPolynomial n R ≃+* MvPolynomial (Fin n) R` equivalence.

## Main results

* `fromCMvPolynomial_rename` — correspondence between `CMvPolynomial.rename` and
  `MvPolynomial.rename`
* `rename_C`, `rename_X`, `rename_add`, `rename_mul`, `rename_id`, `rename_rename`
  — algebraic properties
* `CMvPolynomial.renameEquiv` — ring isomorphism for bijective variable renaming

-/

namespace CPoly

open Std CMvPolynomial

variable {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-! ### Helper lemmas for `fromCMvPolynomial_rename` -/

/-- In a commutative additive monoid, the order of addition in a list fold
does not matter. -/
lemma list_foldl_add_comm {β K V : Type} [AddCommMonoid β]
    (g : K → V → β) (l : List (K × V)) (init : β) :
    List.foldl (fun acc pair => acc + g pair.1 pair.2) init l =
    List.foldl (fun acc pair => g pair.1 pair.2 + acc) init l := by
  induction l generalizing init with
  | nil => rfl
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [show init + g h.1 h.2 = g h.1 h.2 + init from add_comm _ _]
    exact ih _

/-- Swapping addition order in `ExtTreeMap.foldl` does not change the result. -/
lemma foldl_add_comm' {β : Type} [AddCommMonoid β] {k : ℕ}
    {R' : Type} (g : CMvMonomial k → R' → β)
    (t : Std.ExtTreeMap (CMvMonomial k) R') :
    Std.ExtTreeMap.foldl (fun acc m c => acc + g m c) (0 : β) t =
    Std.ExtTreeMap.foldl (fun acc m c => g m c + acc) (0 : β) t := by
  simp only [Std.ExtTreeMap.foldl_eq_foldl_toList]
  exact list_foldl_add_comm g t.toList 0

/-- Applying `CMvMonomial.toFinsupp` at index `i` equals `Vector.get`. -/
lemma toFinsupp_apply (mono : CMvMonomial n) (i : Fin n) :
    (CMvMonomial.toFinsupp mono) i = mono.get i := rfl

/-- Monomial renaming via `Vector.ofFn` corresponds to `Finsupp.mapDomain`
on the `Finsupp` side. -/
lemma renameMonomial_eq (f : Fin n → Fin m) (mono : CMvMonomial n) :
    (Vector.ofFn (fun j => (Finset.univ.filter (fun i => f i = j)).sum
      (fun i => mono.get i)) : CMvMonomial m) =
    CMvMonomial.ofFinsupp
      (Finsupp.mapDomain f (CMvMonomial.toFinsupp mono)) := by
  unfold CMvMonomial.ofFinsupp
  congr 1; funext j
  simp only [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_filter]
  rw [Finsupp.sum]
  -- Extend the sum from `support` to `Finset.univ`
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hxs
  rw [Finsupp.notMem_support_iff] at hxs
  simp [hxs]

/-- `fromCMvPolynomial` maps `CMvPolynomial.monomial` to
`MvPolynomial.monomial`. -/
lemma fromCMvPolynomial_monomial {k : ℕ} (mono : CMvMonomial k) (c : R) :
    fromCMvPolynomial (CMvPolynomial.monomial mono c) =
    MvPolynomial.monomial (CMvMonomial.toFinsupp mono) c := by
  by_cases hc : c = 0
  · subst hc; simp [CMvPolynomial.monomial, map_zero]
  · ext μ
    rw [coeff_eq, MvPolynomial.coeff_monomial]
    unfold CMvPolynomial.coeff CMvPolynomial.monomial
    simp only [show (c == (0 : R)) = false from by simp [hc]]
    unfold Lawful.fromUnlawful
    erw [Unlawful.filter_get]
    simp only [Unlawful.ofList]
    by_cases hm : CMvMonomial.toFinsupp mono = μ
    · subst hm; rw [if_pos rfl, CMvMonomial.ofFinsupp_toFinsupp]
      erw [ExtTreeMap.getElem?_ofList_of_mem
        (k := mono) (k_eq := compare_self) (v := c)
        (mem := by simp) (distinct := ?distinct)]
      · simp
      case distinct => simp
    · rw [if_neg hm]
      have hne : CMvMonomial.ofFinsupp μ ≠ mono :=
        fun h => hm (h ▸ CMvMonomial.toFinsupp_ofFinsupp)
      erw [ExtTreeMap.getElem?_ofList_of_contains_eq_false
        (by simp [hne])]
      rfl

/-- `fromCMvPolynomial` distributes over `Finsupp.sum`. -/
lemma fromCMvPolynomial_finsupp_sum {k : ℕ}
    (g : (Fin n →₀ ℕ) → R → CMvPolynomial k R)
    (a : CMvPolynomial n R) :
    fromCMvPolynomial (Finsupp.sum (fromCMvPolynomial a) g) =
    Finsupp.sum (fromCMvPolynomial a)
      (fun μ c => fromCMvPolynomial (g μ c)) := by
  unfold Finsupp.sum; ext
  simp [MvPolynomial.coeff_sum, coeff_eq, coeff_sum]

/-! ### Main correspondence lemma -/

/-- `CMvPolynomial.rename` agrees with `MvPolynomial.rename` under the
`fromCMvPolynomial` equivalence. -/
lemma fromCMvPolynomial_rename (f : Fin n → Fin m)
    (p : CMvPolynomial n R) :
    fromCMvPolynomial (CMvPolynomial.rename f p) =
    MvPolynomial.rename f (fromCMvPolynomial p) := by
  -- Express rename as a `Finsupp.sum` via `foldl_eq_sum`
  have step1 : CMvPolynomial.rename f p =
      Finsupp.sum (fromCMvPolynomial p) (fun μ c =>
        CMvPolynomial.monomial
          (CMvMonomial.ofFinsupp (Finsupp.mapDomain f μ)) c) := by
    show Std.ExtTreeMap.foldl
        (fun acc mono c => acc + CMvPolynomial.monomial
          (Vector.ofFn fun j =>
            (Finset.univ.filter fun i => f i = j).sum
              fun i => mono.get i) c)
        0 p.1 = _
    simp_rw [renameMonomial_eq f]
    rw [foldl_add_comm' (fun mono c =>
      CMvPolynomial.monomial (CMvMonomial.ofFinsupp
        (Finsupp.mapDomain f (CMvMonomial.toFinsupp mono))) c)]
    rw [foldl_eq_sum]
    congr 1; ext μ c
    simp only [Function.comp_def, CMvMonomial.toFinsupp_ofFinsupp]
  rw [step1]
  rw [fromCMvPolynomial_finsupp_sum]
  simp only [fromCMvPolynomial_monomial,
    CMvMonomial.toFinsupp_ofFinsupp]
  -- Conclude using Mathlib's `MvPolynomial.rename_monomial`
  conv_rhs =>
    rw [← MvPolynomial.support_sum_monomial_coeff
      (fromCMvPolynomial p)]
    rw [map_sum (MvPolynomial.rename f)]
  simp only [MvPolynomial.rename_monomial]
  rfl

/-! ### Bridging lemmas for `C` and `X` -/

/-- `CMvPolynomial.C c` equals `CMvPolynomial.monomial 0 c`. -/
lemma C_eq_monomial {k : ℕ} (c : R) :
    CMvPolynomial.C (n := k) c = CMvPolynomial.monomial 0 c := by
  by_cases hc : c = 0
  · subst hc; ext m
    unfold CMvPolynomial.coeff CMvPolynomial.C CMvPolynomial.monomial
      Lawful.C Unlawful.C
    grind
  · ext m
    show (CMvPolynomial.C c).coeff m =
      (CMvPolynomial.monomial (0 : CMvMonomial k) c).coeff m
    unfold CMvPolynomial.coeff CMvPolynomial.C Lawful.C
      CMvPolynomial.monomial Unlawful.C
    simp only [show (c == (0 : R)) = false from by simp [hc],
      hc, ite_false, MonoR.C]
    show (Unlawful.ofList [(CMvMonomial.zero, c)])[m]?.getD 0 =
      (Lawful.fromUnlawful
        (Unlawful.ofList [(CMvMonomial.zero, c)])).1[m]?.getD 0
    unfold Lawful.fromUnlawful
    erw [Unlawful.filter_get]

/-- The `Finsupp` of the zero monomial is zero. -/
lemma toFinsupp_zero {k : ℕ} :
    CMvMonomial.toFinsupp (0 : CMvMonomial k) = 0 := by
  ext i
  simp [CMvMonomial.toFinsupp, Vector.get]

/-- `fromCMvPolynomial` maps `CMvPolynomial.C` to `MvPolynomial.C`. -/
lemma fromCMvPolynomial_C {k : ℕ} (c : R) :
    fromCMvPolynomial (CMvPolynomial.C (n := k) c) =
    MvPolynomial.C c := by
  rw [C_eq_monomial, fromCMvPolynomial_monomial, toFinsupp_zero,
      ← MvPolynomial.C_apply]

/-! ### Algebraic properties of rename -/

/-- Constants are unchanged under renaming. -/
@[simp]
lemma rename_C (f : Fin n → Fin m) (c : R) :
    CMvPolynomial.rename f (CMvPolynomial.C c) =
    CMvPolynomial.C (n := m) c := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_rename, fromCMvPolynomial_C,
    fromCMvPolynomial_C]
  exact MvPolynomial.rename_C f c

/-- `CMvPolynomial.X i` equals `CMvPolynomial.monomial eᵢ 1`
where `eᵢ` is the `i`-th standard basis vector. -/
lemma X_eq_monomial {k : ℕ} (i : Fin k) :
    CMvPolynomial.X (R := R) i = CMvPolynomial.monomial
      (Vector.ofFn (fun j => if j = i then 1 else 0))
      (1 : R) := by
  unfold CMvPolynomial.X CMvPolynomial.monomial
  by_cases h : (1 : R) = 0
  · ext m; unfold CMvPolynomial.coeff Lawful.fromUnlawful
    erw [Unlawful.filter_get]; simp [h]; grind
  · simp only [show ((1 : R) == 0) = false from by simp [h]]
    exact (if_neg (by decide)).symm

/-- The `Finsupp` of the `i`-th standard basis monomial is
`Finsupp.single i 1`. -/
lemma toFinsupp_unitMono {k : ℕ} (i : Fin k) :
    CMvMonomial.toFinsupp
      (Vector.ofFn (fun j : Fin k =>
        if j = i then 1 else 0)) =
    Finsupp.single i 1 := by
  ext j
  simp [CMvMonomial.toFinsupp, Vector.get,
    Finsupp.single_apply, eq_comm]

/-- `fromCMvPolynomial` maps `CMvPolynomial.X i` to
`MvPolynomial.X i`. -/
lemma fromCMvPolynomial_X {k : ℕ} (i : Fin k) :
    fromCMvPolynomial (CMvPolynomial.X (R := R) i) =
    MvPolynomial.X i := by
  rw [X_eq_monomial, fromCMvPolynomial_monomial,
    toFinsupp_unitMono]
  rfl

/-- Renaming maps variable `X i` to `X (f i)`. -/
@[simp]
lemma rename_X (f : Fin n → Fin m) (i : Fin n) :
    CMvPolynomial.rename f (CMvPolynomial.X (R := R) i) =
    CMvPolynomial.X (f i) := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_rename, fromCMvPolynomial_X,
    fromCMvPolynomial_X]
  exact MvPolynomial.rename_X f i

/-- Renaming preserves addition. -/
@[simp]
lemma rename_add (f : Fin n → Fin m)
    (p q : CMvPolynomial n R) :
    CMvPolynomial.rename f (p + q) =
    CMvPolynomial.rename f p +
    CMvPolynomial.rename f q := by
  apply fromCMvPolynomial_injective
  simp only [fromCMvPolynomial_rename, CPoly.map_add]
  exact _root_.map_add (MvPolynomial.rename f)
    (fromCMvPolynomial p) (fromCMvPolynomial q)

/-- Renaming preserves multiplication. -/
@[simp]
lemma rename_mul (f : Fin n → Fin m)
    (p q : CMvPolynomial n R) :
    CMvPolynomial.rename f (p * q) =
    CMvPolynomial.rename f p *
    CMvPolynomial.rename f q := by
  apply fromCMvPolynomial_injective
  simp only [fromCMvPolynomial_rename, CPoly.map_mul]
  exact _root_.map_mul (MvPolynomial.rename f)
    (fromCMvPolynomial p) (fromCMvPolynomial q)

/-- Renaming by the identity function is the identity. -/
@[simp]
lemma rename_id (p : CMvPolynomial n R) :
    CMvPolynomial.rename id p = p := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_rename]
  exact MvPolynomial.rename_id_apply (fromCMvPolynomial p)

/-- Composing two renamings equals renaming by the composition. -/
@[simp]
lemma rename_rename {k : ℕ} (f : Fin n → Fin m)
    (g : Fin m → Fin k) (p : CMvPolynomial n R) :
    CMvPolynomial.rename g (CMvPolynomial.rename f p) =
    CMvPolynomial.rename (g ∘ f) p := by
  apply fromCMvPolynomial_injective
  rw [fromCMvPolynomial_rename, fromCMvPolynomial_rename,
    fromCMvPolynomial_rename]
  exact MvPolynomial.rename_rename f g (fromCMvPolynomial p)

/-- Ring equivalence for variable renaming when the function is
a bijection. -/
noncomputable def CMvPolynomial.renameEquiv
    (f : Fin n ≃ Fin m) :
    CMvPolynomial n R ≃+* CMvPolynomial m R where
  toFun := CMvPolynomial.rename f
  invFun := CMvPolynomial.rename f.symm
  left_inv p := by
    rw [rename_rename, f.symm_comp_self, rename_id]
  right_inv q := by
    rw [rename_rename, f.self_comp_symm, rename_id]
  map_add' p q := rename_add f p q
  map_mul' p q := rename_mul f p q

end CPoly

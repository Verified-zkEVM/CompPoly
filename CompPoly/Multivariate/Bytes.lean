/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Multivariate.Basic
public import CompPoly.Data.Bytes.Delimited
import all CompPoly.Multivariate.CMvMonomial

/-!
# Serialization of multivariate polynomials

A `CMvPolynomial n R` is a sorted map from exponent vectors to nonzero coefficients, so its
`toList` is already a canonical sequence of terms. It encodes as a `u64` term count followed
by the terms in key order, each term its `n` exponents as `u64` words and then its coefficient.
Decoding rebuilds the map and drops zero coefficients, so it lands on the polynomial. There is
no fixed-width multivariate codec: genuinely multivariate protocol messages are multilinear,
and those have the dense codec of `CompPoly.Multilinear.Bytes`.

A polynomial is `Valid` when its term count and every exponent fit in a `u64` and its
coefficients are valid.
-/

@[expose] public section

namespace CPoly

open CompPoly CompPoly.DelimitedCodec Std

/-! ## Monomials: `n` exponents, no count -/

instance CMvMonomial.instDelimitedCodec (n : ℕ) : DelimitedCodec (CMvMonomial n) :=
  DelimitedCodec.vector (α := ℕ) n

/-- The same codec at `Vector ℕ n`, the underlying type of `CMvMonomial n`, for goals that
instance search sees only after unfolding (the `#m[…]` notation elaborates to a `Vector`). -/
instance CMvMonomial.instDelimitedCodecVector (n : ℕ) : DelimitedCodec (Vector ℕ n) :=
  DelimitedCodec.vector (α := ℕ) n

theorem CMvMonomial.valid_iff {n : ℕ} (m : CMvMonomial n) :
    Valid m ↔ ∀ e ∈ (m : Vector ℕ n).toList, e < 2 ^ 64 := Iff.rfl

theorem CMvMonomial.encode_eq {n : ℕ} (m : CMvMonomial n) :
    encode m = encodeList (m : Vector ℕ n).toList := rfl

/-! ## Rebuilding a map from its own term list -/

/-- `compare` and `==` agree on monomials: both decide equality. Built from `LawfulEqCmp` and
`LawfulBEq` rather than transported from `Vector.compareLex`, whose instance body is not
available to the kernel here. -/
instance CMvMonomial.instLawfulBEqCmp (n : ℕ) :
    LawfulBEqCmp (Ord.compare (α := CMvMonomial n)) where
  compare_eq_iff_beq := by
    intro a b
    rw [LawfulEqCmp.compare_eq_iff_eq, beq_iff_eq]

variable {n : ℕ} {R : Type*} [Zero R]

omit [Zero R] in
/-- A tree map is the map of its own term list. -/
theorem Unlawful.ofList_toList (p : Unlawful n R) : Unlawful.ofList p.toList = p := by
  apply ExtTreeMap.ext_getElem?
  intro k
  cases h : p[k]? with
  | some v =>
    exact ExtTreeMap.getElem?_ofList_of_mem (ReflCmp.compare_self) ExtTreeMap.distinct_keys_toList
      (ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr h)
  | none =>
    apply ExtTreeMap.getElem?_ofList_of_contains_eq_false
    rw [Bool.eq_false_iff]
    intro hcont
    rw [List.contains_iff_mem] at hcont
    obtain ⟨⟨k', v⟩, hkv, hk⟩ := List.mem_map.mp hcont
    simp only at hk
    subst hk
    rw [ExtTreeMap.mem_toList_iff_getElem?_eq_some] at hkv
    rw [hkv] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-! ## Polynomials -/

variable [BEq R] [LawfulBEq R]

/-- A `u64` term count, then each term as `n` exponents and a coefficient. -/
instance CMvPolynomial.instDelimitedCodec [DelimitedCodec R] :
    DelimitedCodec (CMvPolynomial n R) where
  encode p := encode p.1.toList
  decode? l := (decode? (α := List (CMvMonomial n × R)) l).map fun tl =>
    (Lawful.fromUnlawful (Unlawful.ofList tl.1), tl.2)
  Valid p := Valid p.1.toList
  decode?_encode_append p rest h := by
    rw [decode?_encode_append _ _ h, Option.map_some, Unlawful.ofList_toList,
      Lawful.fromUnlawful_cast]

theorem CMvPolynomial.valid_iff [DelimitedCodec R] (p : CMvPolynomial n R) :
    Valid p ↔ p.1.toList.length < 2 ^ 64 ∧
      ∀ t ∈ p.1.toList, (∀ e ∈ (t.1 : Vector ℕ n).toList, e < 2 ^ 64) ∧ Valid t.2 := Iff.rfl

theorem CMvPolynomial.encode_eq [DelimitedCodec R] (p : CMvPolynomial n R) :
    encode p = encodeU64 p.1.toList.length ++ encodeList p.1.toList := rfl

end CPoly

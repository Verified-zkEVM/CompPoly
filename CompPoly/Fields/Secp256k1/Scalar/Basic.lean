/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.PrattCertificate

/-!
  # secp256k1 Scalar Field

  Canonical scalar field, its cardinality, and its primality certificate.

  Represented as `n` in https://www.secg.org/sec2-v2.pdf.
-/

namespace Secp256k1.Scalar.Basic

/-- The prime order of the secp256k1 scalar field. -/
@[reducible]
def CARD : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- The canonical secp256k1 scalar field. -/
abbrev Field := ZMod CARD

/-- The secp256k1 scalar-field order is prime. -/
theorem card_is_prime : Nat.Prime CARD := by
  unfold CARD
  refine PrattCertificate'.out (p := CARD) ⟨7, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 6, 3, 149, 631, 107361793816595537, 174723607534414371449,
    341948486974166000522343609283189] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr
  all_goals rw [hr]
  · exact .prime 2 6 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 149 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 631 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 107361793816595537 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 174723607534414371449 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 341948486974166000522343609283189 1 _ ?_ (by reduce_mod_char; decide)
      (by norm_num)
    · refine PrattCertificate'.out ⟨2, (by reduce_mod_char), ?_⟩
      refine .split [2 ^ 2, 3 ^ 3, 109, 29047611873442575647497758179] (fun r hr => ?_)
        (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 3 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 109 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 29047611873442575647497758179 1 _ (by pratt) (by reduce_mod_char; decide)
          (by norm_num)

/-- Registers the primality of the scalar-field modulus for typeclass inference. -/
instance card_prime_fact : Fact (Nat.Prime CARD) := ⟨card_is_prime⟩

/-- The canonical secp256k1 scalar field is a field. -/
instance field : _root_.Field Field := ZMod.instField CARD

end Secp256k1.Scalar.Basic

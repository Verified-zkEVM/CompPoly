/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.PrattCertificate

/-!
  # secp256k1 Base Field

  Canonical base field, its cardinality, and its primality certificate.

  Represented as `p` in https://www.secg.org/sec2-v2.pdf.
-/

namespace Secp256k1.Base.Basic

/-- The secp256k1 base-field prime `2^256 - 2^32 - 977`. -/
@[reducible]
def CARD : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

/-- The special form of the base-field prime used by pseudo-Mersenne reduction. -/
theorem card_eq_two_pow_256_sub : CARD = 2 ^ 256 - 2 ^ 32 - 977 := by
  unfold CARD
  norm_num

/-- The canonical secp256k1 base field. -/
abbrev Field := ZMod CARD

/-- The secp256k1 base-field prime is prime. -/
theorem card_is_prime : Nat.Prime CARD := by
  unfold CARD
  refine PrattCertificate'.out (p := CARD) ⟨3, (by reduce_mod_char), ?_⟩
  refine .split [2, 3, 7, 13441,
    205115282021455665897114700593932402728804164701536103180137503955397371]
    (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr
  all_goals rw [hr]
  · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13441 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 205115282021455665897114700593932402728804164701536103180137503955397371 1 _ ?_
      (by reduce_mod_char; decide) (by norm_num)
    · refine PrattCertificate'.out ⟨10, (by reduce_mod_char), ?_⟩
      refine .split [2, 3, 5, 29 ^ 2, 31, 7723, 132896956044521568488119,
        255515944373312847190720520512484175977] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 5 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 29 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 31 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 7723 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 132896956044521568488119 1 _ (by pratt)
          (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 255515944373312847190720520512484175977 1 _ (by pratt)
          (by reduce_mod_char; decide) (by norm_num)

/-- Registers the primality of the base-field modulus for typeclass inference. -/
instance card_prime_fact : Fact (Nat.Prime CARD) := ⟨card_is_prime⟩

/-- The canonical secp256k1 base field is a field. -/
instance field : _root_.Field Field := ZMod.instField CARD

end Secp256k1.Base.Basic

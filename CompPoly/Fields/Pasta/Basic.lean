/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daira-Emma Hopwood, Gregor Mitscha-Baude
-/

import CompPoly.Fields.PrattCertificate

/-!
# The Pasta (Pallas / Vesta) base prime fields

The Pallas and Vesta curves form a 2-cycle: the base field of one is the scalar field of the
other.  This module defines the two underlying 255-bit primes together with their Lucas/Pratt
primality certificates, following the pattern of `CompPoly.Fields.Secp256k1`.

* `Pallas.baseFieldSize` is the Pallas base field size, equal to the Vesta scalar field size;
* `Vesta.baseFieldSize` is the Vesta base field size, equal to the Pallas scalar field size.

Both primes are `1 mod 2 ^ 32` and have 2-adicity 32.  The certificates were generated from
the factorizations of `p - 1` and `q - 1`; see <https://github.com/zcash/pasta>.
-/

namespace Pallas

/-- The base field size of the Pallas curve, which is the scalar field size of Vesta. -/
@[reducible]
def baseFieldSize : Nat :=
  0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

/-- The Pallas base field as a `ZMod`. -/
abbrev BaseField := ZMod baseFieldSize

/-- The Pallas base field size is prime. -/
theorem baseFieldSize_is_prime : Nat.Prime baseFieldSize := by
  unfold baseFieldSize
  refine PrattCertificate'.out
    (p := 28948022309329048855892746252171976963363056481941560715954676764349967630337)
    ⟨5, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 32, 3, 463, 539204044132271846773,
    8999194758858563409123804352480028797519453] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr
  all_goals rw [hr]
  · exact .prime 2 32 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 463 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 539204044132271846773 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    refine PrattCertificate'.out (p := 539204044132271846773) ⟨5, (by reduce_mod_char), ?_⟩
    refine .split [2 ^ 2, 3 ^ 5, 89, 14923, 417677162933] (fun r hr => ?_) (by norm_num)
    simp at hr
    rcases hr with hr | hr | hr | hr | hr
    all_goals rw [hr]
    · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 3 5 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 89 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 14923 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 417677162933 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out (p := 417677162933) ⟨2, (by reduce_mod_char), ?_⟩
      refine .split [2 ^ 2, 59, 1973, 897019] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 59 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 1973 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 897019 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 8999194758858563409123804352480028797519453 1 _ ?_ (by reduce_mod_char; decide)
      (by norm_num)
    refine PrattCertificate'.out (p := 8999194758858563409123804352480028797519453)
      ⟨2, (by reduce_mod_char), ?_⟩
    refine .split [2 ^ 2, 3 ^ 4, 11, 2531, 115603, 1197907, 22160661629, 325086459374267]
      (fun r hr => ?_) (by norm_num)
    simp at hr
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr
    all_goals rw [hr]
    · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 3 4 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 11 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 2531 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 115603 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 1197907 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 22160661629 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out (p := 22160661629) ⟨3, (by reduce_mod_char), ?_⟩
      refine .split [2 ^ 2, 7, 19, 41655379] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 19 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 41655379 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 325086459374267 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out (p := 325086459374267) ⟨2, (by reduce_mod_char), ?_⟩
      refine .split [2, 509, 413527, 772231] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 509 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 413527 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 772231 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

instance : Fact (Nat.Prime baseFieldSize) := ⟨baseFieldSize_is_prime⟩

instance : Field BaseField := ZMod.instField baseFieldSize

end Pallas

namespace Vesta

/-- The base field size of the Vesta curve, which is the scalar field size of Pallas. -/
@[reducible]
def baseFieldSize : Nat :=
  0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

/-- The Vesta base field as a `ZMod`. -/
abbrev BaseField := ZMod baseFieldSize

/-- The Vesta base field size is prime. -/
theorem baseFieldSize_is_prime : Nat.Prime baseFieldSize := by
  unfold baseFieldSize
  refine PrattCertificate'.out
    (p := 28948022309329048855892746252171976963363056481941647379679742748393362948097)
    ⟨5, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 32, 3 ^ 2, 1709, 24859, 1690502597179744445941507,
    10427374428728808478656897599072717] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr
  all_goals rw [hr]
  · exact .prime 2 32 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 1709 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 24859 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 1690502597179744445941507 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    refine PrattCertificate'.out (p := 1690502597179744445941507) ⟨2, (by reduce_mod_char), ?_⟩
    refine .split [2, 3, 13, 4129989133, 5247740253619] (fun r hr => ?_) (by norm_num)
    simp at hr
    rcases hr with hr | hr | hr | hr | hr
    all_goals rw [hr]
    · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 13 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 4129989133 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out (p := 4129989133) ⟨5, (by reduce_mod_char), ?_⟩
      refine .split [2 ^ 2, 3, 359, 958679] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 359 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 958679 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 5247740253619 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out (p := 5247740253619) ⟨2, (by reduce_mod_char), ?_⟩
      refine .split [2, 3 ^ 3, 17, 71, 80513981] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 3 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 17 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 71 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 80513981 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 10427374428728808478656897599072717 1 _ ?_ (by reduce_mod_char; decide)
      (by norm_num)
    refine PrattCertificate'.out (p := 10427374428728808478656897599072717)
      ⟨2, (by reduce_mod_char), ?_⟩
    refine .split [2 ^ 2, 294793, 4229279, 399082391, 5239247429827] (fun r hr => ?_)
      (by norm_num)
    simp at hr
    rcases hr with hr | hr | hr | hr | hr
    all_goals rw [hr]
    · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 294793 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 4229279 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 399082391 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 5239247429827 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out (p := 5239247429827) ⟨2, (by reduce_mod_char), ?_⟩
      refine .split [2, 3 ^ 2, 757, 12149, 31649] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr | hr
      all_goals rw [hr]
      · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 757 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 12149 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 31649 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

instance : Fact (Nat.Prime baseFieldSize) := ⟨baseFieldSize_is_prime⟩

instance : Field BaseField := ZMod.instField baseFieldSize

end Vesta

namespace Pallas

/-- The scalar field size of Pallas is the base field size of Vesta. -/
abbrev scalarFieldSize : Nat := Vesta.baseFieldSize

/-- The Pallas scalar field is the Vesta base field. -/
abbrev ScalarField := Vesta.BaseField

end Pallas

namespace Vesta

/-- The scalar field size of Vesta is the base field size of Pallas. -/
abbrev scalarFieldSize : Nat := Pallas.baseFieldSize

/-- The Vesta scalar field is the Pallas base field. -/
abbrev ScalarField := Pallas.BaseField

end Vesta

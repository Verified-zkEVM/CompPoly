/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Parallel
public import CompPoly.Univariate.NTTFast.Packed.RecursiveFormula

/-! # Concatenating recursive DIF outputs preserves bit-reversed evaluation order -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Lower-half output indices correspond to the even evaluation points. -/
theorem bitRevNat_lower_half (bits i : Nat) (hi : i < 2 ^ bits) :
    NTT.Transform.bitRevNat (bits + 1) i = 2 * NTT.Transform.bitRevNat bits i := by
  have hb := NTT.Transform.bitRevNat_lt bits i
  have hs : 2 * NTT.Transform.bitRevNat bits i < 2 ^ (bits + 1) := by
    rw [Nat.pow_succ]
    omega
  have h := NTT.Transform.bitRevNat_even bits (NTT.Transform.bitRevNat bits i)
  rw [NTT.Transform.bitRevNat_involutive bits i hi] at h
  have he := congrArg (NTT.Transform.bitRevNat (bits + 1)) h
  rw [NTT.Transform.bitRevNat_involutive (bits + 1) _ hs] at he
  exact he.symm

/-- Upper-half output indices correspond to the odd evaluation points. -/
theorem bitRevNat_upper_half (bits i : Nat) (hi : i < 2 ^ bits) :
    NTT.Transform.bitRevNat (bits + 1) (2 ^ bits + i) =
      2 * NTT.Transform.bitRevNat bits i + 1 := by
  have hb := NTT.Transform.bitRevNat_lt bits i
  have hs : 2 * NTT.Transform.bitRevNat bits i + 1 < 2 ^ (bits + 1) := by
    rw [Nat.pow_succ]
    omega
  have h := NTT.Transform.bitRevNat_odd bits (NTT.Transform.bitRevNat bits i)
  rw [NTT.Transform.bitRevNat_involutive bits i hi] at h
  have he := congrArg (NTT.Transform.bitRevNat (bits + 1)) h
  rw [NTT.Transform.bitRevNat_involutive (bits + 1) _ hs] at he
  exact he.symm

/-- The ordinary bit-reversed mathematical forward output. -/
def difSpec [Field R] (D : NTT.Domain R) (a : Array R) : Array R :=
  NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D a)

/-- The mathematical DIF output has one value per domain point. -/
@[simp] theorem size_difSpec [Field R] (D : NTT.Domain R) (a : Array R) :
    (difSpec D a).size = D.n := by
  simp only [difSpec, NTT.Transform.bitRevPermute, Array.size_ofFn]

/-- Reading a bounded DIF output evaluates the DFT at the reversed index. -/
theorem getD_difSpec [Field R] (D : NTT.Domain R) (a : Array R) (i : Nat) (hi : i < D.n) :
    (difSpec D a).getD i 0 = dftValue D a (NTT.Transform.bitRevNat D.logN i) := by
  have hb : NTT.Transform.bitRevNat D.logN i < D.n := NTT.Transform.bitRevNat_lt _ _
  simp only [difSpec, NTT.Transform.bitRevPermute]
  rw [getD_ofFn_bounded _ i hi 0]
  simp only [NTT.Forward.forwardSpec]
  rw [getD_ofFn_bounded _ _ hb 0]
  exact (dftValue_eq_nttAt D a ⟨_, hb⟩).symm

/-- Two recursive transforms of the first-layer partitions give the original DIF transform. -/
theorem difSpec_split [Field R] (D : NTT.Domain R) (hlog : 0 < D.logN) (a : Array R) :
    difSpec (halfDomain D hlog) (splitFieldsLeft D a) ++
      difSpec (halfDomain D hlog) (splitFieldsRight D a) = difSpec D a := by
  have hn := halfDomain_size D hlog
  have hlogeq : D.logN = (D.logN - 1) + 1 := by omega
  apply Array.ext (by simp only [Array.size_append, size_difSpec]; omega)
  intro i hi hj
  have hik : i < D.n := by simpa only [size_difSpec] using hj
  have hquery :
      (difSpec (halfDomain D hlog) (splitFieldsLeft D a) ++
        difSpec (halfDomain D hlog) (splitFieldsRight D a)).getD i 0 =
        (difSpec D a).getD i 0 := by
    rw [getD_difSpec D a i hik]
    by_cases hlo : i < (halfDomain D hlog).n
    · rw [Plan.getD_append_left _ _ i (by rw [size_difSpec]; exact hlo),
        getD_difSpec _ _ i hlo]
      rw [dftValue_split_left, hlogeq, bitRevNat_lower_half (D.logN - 1) i hlo]
      rfl
    · have hoff : i - (halfDomain D hlog).n < (halfDomain D hlog).n := by omega
      have he : i = (halfDomain D hlog).n + (i - (halfDomain D hlog).n) := by omega
      conv_lhs => rw [he, ← size_difSpec (halfDomain D hlog) (splitFieldsLeft D a),
        Plan.getD_append_right]
      rw [size_difSpec, getD_difSpec _ _ _ hoff, dftValue_split_right]
      conv_rhs => rw [he]
      rw [hlogeq]
      change dftValue D a (2 * NTT.Transform.bitRevNat (D.logN - 1)
        (i - (halfDomain D hlog).n) + 1) = _
      simp only [NTT.Domain.n, halfDomain]
      rw [bitRevNat_upper_half (D.logN - 1) (i - 2 ^ (D.logN - 1))
        (by simpa only [NTT.Domain.n, halfDomain] using hoff)]
  simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hj, Option.getD_some] using hquery

end CompPoly.CPolynomial.NTTFast.Packed

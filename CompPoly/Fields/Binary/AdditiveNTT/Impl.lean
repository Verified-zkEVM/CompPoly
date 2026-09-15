/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Executable
public import CompPoly.Fields.Binary.Tower.Concrete.Basis
public import Mathlib.Data.BitVec

/-!
# Concrete additive NTT instances

Compatibility entry point for the generic executable additive NTT algorithms, together with
concrete binary tower bases, instances and the existing example. Generic algorithm clients can
import `CompPoly.Fields.Binary.AdditiveNTT.Executable`; generic correctness clients can import
`CompPoly.Fields.Binary.AdditiveNTT.Correctness`.
-/

@[expose] public section

namespace AdditiveNTT
open ConcreteBinaryTower

variable {r : ℕ} [NeZero r]

section ConcreteBTFieldInstances

instance (k : ℕ) : NeZero (2^k) := by
  refine ⟨?_⟩
  have h₂ : (2 : ℕ) ≠ 0 := by decide
  simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]

/-- Computable basis for ConcreteBTField k over ConcreteBTField 0.
This is the explicit product of Z's. -/
def computableBasisExplicit (k : ℕ) (i : Fin (2 ^ k)) : ConcreteBTField k :=
  (Finset.univ : Finset (Fin k)).prod fun j =>
    if Nat.getBit (n := i.val) (k := j.val) == 1 then
      concreteTowerAlgebraMap (j.val + 1) k (by omega) (Z (j.val + 1))
    else
      1

omit [NeZero r] in
/-- The executable bit-indexed basis equals the multilinear tower basis over level zero. -/
theorem computableBasisExplicit_eq_multilinearBasis (k : ℕ) :
    computableBasisExplicit k = fun i => multilinearBasis 0 k (by omega) i := by
  funext i
  unfold computableBasisExplicit
  rw [multilinearBasis_apply k 0 (by omega) i]
  simp only [beq_iff_eq, Nat.sub_zero, 𝕏, map_pow]
  congr 1
  funext x
  have h_lt := Nat.getBit_lt_2 (n := i) (k := x)
  by_cases h : Nat.getBit (k := x) (n := i) = 1
  · simp only [h, ↓reduceIte, pow_one]
    rw! (castMode := .all) [Nat.zero_add]
    rfl
  · have hBit_eq_0 : Nat.getBit (k := x) (n := i) = 0 := by omega
    simp only [hBit_eq_0, zero_ne_one, ↓reduceIte, pow_zero]

omit [NeZero r] in
theorem hβ_lin_indep_concrete (k : ℕ) :
    letI := ConcreteBTFieldAlgebra (l:=0) (r:=k) (h_le:=by omega)
    LinearIndependent (R := ConcreteBTField 0)
      (v := computableBasisExplicit k) := by
  let := ConcreteBTFieldAlgebra (l:=0) (r:=k) (h_le:=by omega)
  rw [computableBasisExplicit_eq_multilinearBasis]
  exact (multilinearBasis 0 k (by omega)).linearIndependent

abbrev BTF₃ := ConcreteBTField 3 -- 8 bits
instance : NeZero (2^3) := ⟨by norm_num⟩
instance : Field BTF₃ := instFieldConcrete
instance : DecidableEq BTF₃ := (inferInstance : DecidableEq (ConcreteBTField 3))
instance : Fintype BTF₃ :=
  Fintype.ofEquiv (Fin (2 ^ (2 ^ 3))) (BitVec.equivFin (m := 2 ^ 3)).symm.toEquiv

/-- Test of the computable additive NTT over BTF₃ (an 8-bit binary tower field `BTF₃`).
**Input polynomial:** p(x) = x (novel coefficients [7, 1, 0, 0]) of size `2^ℓ` in `BTF₃`
- `ℓ = 2`
- `R_rate = 2`: Repetition rate, evaluating at `S₀` of size `2^(ℓ + R_rate) = 16` points
- `r = 2^3 = 8`: Dimension of the basis for `BTF₃` over `GF(2)`
**Output:** A function `Fin 16 → BTF₃` giving the evaluations of `p(x) = x` at 16 points
in the evaluation domain `S₀` defined by the spanning basis elements `{β₀, ..., β_{ℓ + 𝓡 - 1}}`
of `BTF₃` over `GF(2)`. -/
def testNTTBTF₃ : Fin (2 ^ (2 + 2)) → BTF₃ := by
  let a : Fin 4 → BTF₃ := Array.toFinVec 4 #[7, 1, 0, 0] rfl
  letI : Algebra (ConcreteBTField 0) BTF₃ := ConcreteBTFieldAlgebra (l := 0) (r := 3)
    (h_le := by omega)
  haveI : Fact (LinearIndependent (ConcreteBTField 0) (computableBasisExplicit 3)) :=
    { out := hβ_lin_indep_concrete 3 }
  -- r is the size of the basis
  exact computableAdditiveNTT (𝔽q := ConcreteBTField 0) (L := BTF₃) (r := 2^3) (ℓ := 2)
    (R_rate := 2) (h_ℓ_add_R_rate := by omega) (β := computableBasisExplicit (k := 3)) (a := a)

-- #eval testNTTBTF₃
-- ![1#8, 0#8, 3#8, 2#8, 5#8, 4#8, 7#8, 6#8, 9#8, 8#8, 11#8, 10#8, 13#8, 12#8, 15#8, 14#8]

end ConcreteBTFieldInstances
end AdditiveNTT

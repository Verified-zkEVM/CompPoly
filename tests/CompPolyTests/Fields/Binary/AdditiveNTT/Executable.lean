/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

import CompPoly.Fields.Binary.AdditiveNTT.Correctness

/-!
# Generic executable additive NTT clients

The correctness entry point supports arbitrary fields and must not import a binary tower
construction. The import guard makes that boundary part of the regression suite.
-/

namespace CompPolyTests.AdditiveNTTExecutable

open AdditiveNTT

open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if name.toString.startsWith "CompPoly.Fields.Binary.Tower." then
      throwError "Generic additive NTT correctness imported a tower module: {name}"

example {r ℓ R_rate : ℕ} [NeZero r]
    {L 𝔽q : Type} [Field L] [Fintype L] [DecidableEq L]
    [Field 𝔽q] [Fintype 𝔽q] [Algebra 𝔽q L] [Fact (Fintype.card 𝔽q = 2)]
    (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)]
    (h : ℓ + R_rate < r) (a : Fin (2 ^ ℓ) → L) :
    computableAdditiveNTT (𝔽q := 𝔽q) (β := β) h a = additiveNTT 𝔽q β h a :=
  computableAdditiveNTT_eq_additiveNTT β h a

example {r ℓ R_rate : ℕ} [NeZero r]
    {L 𝔽q : Type} [Field L] [Fintype L] [DecidableEq L]
    [Field 𝔽q] [Fintype 𝔽q] [Algebra 𝔽q L] [Fact (Fintype.card 𝔽q = 2)]
    [Fact (Nat.Prime (ringChar 𝔽q))]
    (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)]
    (h : ℓ + R_rate < r) (a : Fin (2 ^ ℓ) → L) :
    arrayToFinFunction (2 ^ (ℓ + R_rate)) (computableAdditiveNTTFast β h a) =
      additiveNTT 𝔽q β h a :=
  computableAdditiveNTTFast_eq_additiveNTT β h a

end CompPolyTests.AdditiveNTTExecutable

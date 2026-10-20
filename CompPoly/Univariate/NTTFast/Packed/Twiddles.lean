/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Arithmetic
public import CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Correctness.Basic

/-! # Shape and identity invariants of twiddle tables -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Every stored twiddle table has its stage's butterfly width. -/
def TwiddleSizes (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field)) : Prop :=
  ∀ stage < logN, (tw.getD stage #[]).size = 2 ^ stage

/-- Every twiddle stage starts at the multiplicative identity. -/
def TwiddleOnes (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field)) : Prop :=
  ∀ stage < logN, (tw.getD stage #[]).getD 0 0 = 1

/-- A one-coordinate twiddle table beginning at one is the identity table. -/
theorem twiddle_zero_eq_one (tw : Array KoalaBear.Fast.Field)
    (hs : tw.size = 1) (hone : tw.getD 0 0 = 1) : tw = #[1] := by
  apply Array.ext (by simpa only [Array.size_singleton] using hs)
  intro i hi hj
  have he : i = 0 := by omega
  subst i
  simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
    Option.getD_some, Array.getElem_singleton] using hone

/-- Ordinary cached domain twiddles satisfy both packed-stage invariants. -/
theorem twiddleTable_invariants (D : NTT.Domain KoalaBear.Fast.Field) :
    TwiddleSizes D.logN (Plan.twiddleTable D) ∧
      TwiddleOnes D.logN (Plan.twiddleTable D) := by
  constructor
  · intro stage hs
    rw [Plan.twiddleTable_getD_eq_twiddlePowers D stage hs, Plan.twiddlePowers_size]
  · intro stage hs
    rw [Plan.twiddleTable_getD_eq_twiddlePowers D stage hs,
      Plan.twiddlePowers_getD_eq_pow D stage 0 (Nat.two_pow_pos stage), pow_zero]

end CompPoly.CPolynomial.NTTFast.Packed

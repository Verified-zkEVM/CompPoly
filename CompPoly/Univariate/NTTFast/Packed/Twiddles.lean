/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Basic
public import CompPoly.Univariate.NTTFast.Packed.Normalization

/-! # Reusing larger-domain twiddle tables in recursive transforms -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The stages consumed by a domain agree with its canonical twiddles. -/
def TwiddlesFor (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) : Prop :=
  ∀ stage < D.logN, tw.getD stage #[] = (Plan.twiddleTable D).getD stage #[]

/-- A matching twiddle prefix inherits the domain's shape and identity invariants. -/
theorem TwiddlesFor.invariants (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (ht : TwiddlesFor D tw) :
    TwiddleSizes D.logN tw ∧ TwiddleOnes D.logN tw := by
  obtain ⟨hs, ho⟩ := twiddleTable_invariants D
  exact ⟨fun stage hstage ↦ by rw [ht stage hstage]; exact hs stage hstage,
    fun stage hstage ↦ by rw [ht stage hstage]; exact ho stage hstage⟩

/-- The complete ordinary stage schedule depends only on its consumed twiddle prefix. -/
theorem allFieldStages_twiddles_congr (logN : Nat)
    (tw ta : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (ht : ∀ stage < logN, tw.getD stage #[] = ta.getD stage #[]) :
    allFieldStages logN tw a = allFieldStages logN ta a := by
  have hp : (List.range (logN / 2)).foldl (fun b pass ↦ fieldPass logN tw pass b) a =
      (List.range (logN / 2)).foldl (fun b pass ↦ fieldPass logN ta pass b) a := by
    apply Plan.foldl_range_congr
    intro pass hpass b
    obtain ⟨hhl, hh, hl⟩ := pass_indices logN pass hpass
    dsimp only [fieldPass]
    rw [ht _ hh, ht _ hl]
  unfold allFieldStages
  rw [hp]

/-- The packed pipeline may reuse a larger table when its required stage entries agree. -/
theorem Native.stages_correct_for (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (normalize : Bool)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size)
    (hn : ValidNormalization D.logN normalize) :
    Native.stages D.logN (tw.map packFields) (packFields a) factor.val normalize =
      packFields (if normalize then
        (Plan.runStagesDIFRadix4WithTwiddles D (Plan.twiddleTable D) a).map (fun x ↦ factor * x)
      else Plan.runStagesDIFRadix4WithTwiddles D (Plan.twiddleTable D) a) := by
  obtain ⟨htw, hone⟩ := ht.invariants D tw
  obtain ⟨hc, ho⟩ := twiddleTable_invariants D
  rw [Native.stages_packFields _ _ _ _ _ htw hone hs hu]
  cases normalize with
  | false =>
    rw [fieldStages_unscaled_eq_all _ _ _ _ htw hone hs,
      allFieldStages_twiddles_congr _ _ _ _ ht,
      allFieldStages_eq_plan D (Plan.twiddleTable D) a hc ho]
    rfl
  | true =>
    obtain ⟨hlog, hmod⟩ := hn rfl
    rw [fieldStages_normalized_eq_map _ _ _ _ hlog hmod hs,
      fieldStages_unscaled_eq_all _ _ _ _ htw hone hs,
      allFieldStages_twiddles_congr _ _ _ _ ht,
      allFieldStages_eq_plan D (Plan.twiddleTable D) a hc ho]
    rfl

end CompPoly.CPolynomial.NTTFast.Packed

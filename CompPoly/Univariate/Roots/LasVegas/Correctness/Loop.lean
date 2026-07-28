/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Correctness.EvenTrace
import CompPoly.Univariate.Roots.LasVegas.Correctness.Odd

/-!
# Loop Correctness Surface for Las Vegas Splitting

Completeness and packaging lemmas for the bounded Las Vegas splitter loop and
its enumeration fallback.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

private theorem representedEnumeratedLinearFactors_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) {p : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈ (representedLinearFactorsOnly (enumeratedLinearFactors enumeration p)).toList ∧
        IsLinearRootFactorCandidate factor a := by
  refine ⟨CPolynomial.linearFactor a, ?_, linearFactor_isRootFactorCandidate a⟩
  apply representedLinearFactorsOnly_mem_of_mem
  · rw [enumeratedLinearFactors]
    simpa using
      (List.mem_map.mpr
        ⟨a, rootsInFieldByEnumeration_complete enumeration hroot, rfl⟩)
  · exact linearFactor_isRepresentedLinearFactor a

private theorem linearFactor_mem_enumeratedLinearFactors {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) {p : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a p = 0) :
    CPolynomial.linearFactor a ∈ (enumeratedLinearFactors enumeration p).toList := by
  rw [enumeratedLinearFactors]
  simpa using
    (List.mem_map.mpr
      ⟨a, rootsInFieldByEnumeration_complete enumeration hroot, rfl⟩)

private theorem lasVegasSplitLoopWith_mem_of_mem_out {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {factor : CPolynomial F} :
    ∀ fuel stack out,
      factor ∈ out.toList →
        factor ∈
          (lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack out).toList := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack out hmem
      simp [lasVegasSplitLoopWith, hmem]
  | succ fuel ih =>
      intro stack out hmem
      cases stack with
      | nil =>
          simp [lasVegasSplitLoopWith, hmem]
      | cons g stack =>
          rw [lasVegasSplitLoopWith.eq_def]
          simp only
          by_cases hskip : (CPolynomial.monicNormalize g == 0 ||
              CPolynomial.monicNormalize g == 1) = true
          · rw [if_pos hskip]
            exact ih stack out hmem
          · rw [if_neg hskip]
            by_cases hlin : isRepresentedLinearFactor (CPolynomial.monicNormalize g) = true
            · rw [if_pos hlin]
              exact ih stack (out.push (CPolynomial.monicNormalize g)) (by simp [hmem])
            · rw [if_neg hlin]
              by_cases hodd : (cfg.tryOddRandomizedSplitting && q % 2 == 1) = true
              · rw [if_pos hodd]
                cases htry :
                    tryOddSplitAttemptsWith M D q probes (CPolynomial.monicNormalize g)
                      cfg.cutoff 0 with
                | none =>
                    simp only
                    exact ih stack
                      (out ++ enumeratedLinearFactors enumeration (CPolynomial.monicNormalize g))
                      (by simp [hmem])
                | some children =>
                    simp only
                    exact ih (children.toList ++ stack) out hmem
              · rw [if_neg hodd]
                by_cases heven : (cfg.tryEvenTraceSplitting && q % 2 == 0) = true
                · rw [if_pos heven]
                  cases traceCtx? with
                  | none =>
                      simp only
                      exact ih stack
                        (out ++ enumeratedLinearFactors enumeration (CPolynomial.monicNormalize g))
                        (by simp [hmem])
                  | some traceCtx =>
                      simp only
                      by_cases hmatch : traceContextMatchesQ traceCtx q = true
                      · rw [if_pos hmatch]
                        cases htry :
                            tryEvenTraceSplitAttemptsWith M D traceCtx q probes
                              (CPolynomial.monicNormalize g) cfg.cutoff 0 with
                        | none =>
                            simp only
                            exact ih stack
                              (out ++ enumeratedLinearFactors enumeration
                                (CPolynomial.monicNormalize g))
                              (by simp [hmem])
                        | some children =>
                            simp only
                            exact ih (children.toList ++ stack) out hmem
                      · rw [if_neg hmatch]
                        exact ih stack
                          (out ++ enumeratedLinearFactors enumeration
                            (CPolynomial.monicNormalize g))
                          (by simp [hmem])
                · rw [if_neg heven]
                  exact ih stack
                    (out ++ enumeratedLinearFactors enumeration (CPolynomial.monicNormalize g))
                    (by simp [hmem])

private theorem lasVegasSplitLoopWith_represented_mem_of_mem_out {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {factor : CPolynomial F} {fuel : Nat} {stack : List (CPolynomial F)}
    {out : Array (CPolynomial F)}
    (hmem : factor ∈ out.toList) (hlin : isRepresentedLinearFactor factor = true) :
    factor ∈
      (representedLinearFactorsOnly
        (lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack out)).toList := by
  apply representedLinearFactorsOnly_mem_of_mem
  · exact lasVegasSplitLoopWith_mem_of_mem_out
      M D enumeration traceCtx? cfg probes q fuel stack out hmem
  · exact hlin

private theorem lasVegasSplitLoopWith_fallback_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {fuel : Nat} {stack : List (CPolynomial F)} {out : Array (CPolynomial F)}
    {g : CPolynomial F} {a : F} (hroot : CPolynomial.eval a g = 0) :
    ∃ factor,
      factor ∈
          (representedLinearFactorsOnly
            (lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack
              (out ++ enumeratedLinearFactors enumeration g))).toList ∧
        IsLinearRootFactorCandidate factor a := by
  refine ⟨CPolynomial.linearFactor a, ?_, linearFactor_isRootFactorCandidate a⟩
  apply lasVegasSplitLoopWith_represented_mem_of_mem_out
    M D enumeration traceCtx? cfg probes q
  · simp [linearFactor_mem_enumeratedLinearFactors enumeration hroot]
  · exact linearFactor_isRepresentedLinearFactor a

set_option maxHeartbeats 800000 in
private theorem lasVegasSplitLoopWith_complete_of_state {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat) {a : F} :
    ∀ fuel stack out,
      normStackWork stack ≤ fuel →
        normStackReady stack →
          ((∃ factor, factor ∈ out.toList ∧
              isRepresentedLinearFactor factor = true ∧
              IsLinearRootFactorCandidate factor a) ∨
            (∃ g, g ∈ stack ∧ g ≠ 0 ∧ CPolynomial.eval a g = 0)) →
            ∃ factor,
              factor ∈
                  (representedLinearFactorsOnly
                    (lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q
                      fuel stack out)).toList ∧
                IsLinearRootFactorCandidate factor a := by
  intro fuel
  induction fuel with
  | zero =>
      intro stack out hwork hready hstate
      rcases hstate with hout | hstack
      · rcases hout with ⟨factor, hmem, hlin, hcand⟩
        exact ⟨factor,
          lasVegasSplitLoopWith_represented_mem_of_mem_out
            M D enumeration traceCtx? cfg probes q hmem hlin,
          hcand⟩
      · rcases hstack with ⟨g, hmem, _hg, _hroot⟩
        have hpos := normStackWork_pos_of_mem hready hmem
        omega
  | succ fuel ih =>
      intro stack out hwork hready hstate
      rcases hstate with hout | hstack
      · rcases hout with ⟨factor, hmem, hlin, hcand⟩
        exact ⟨factor,
          lasVegasSplitLoopWith_represented_mem_of_mem_out
            M D enumeration traceCtx? cfg probes q hmem hlin,
          hcand⟩
      · cases stack with
        | nil =>
            rcases hstack with ⟨g, hmem, _hg, _hroot⟩
            simp at hmem
        | cons g stack =>
            rcases hstack with ⟨rootPoly, hmemRoot, hrootNe, hrootEval⟩
            have hmemRoot' : rootPoly = g ∨ rootPoly ∈ stack := by
              simpa using hmemRoot
            have hheadReady := hready g (by simp)
            have hheadPos : 1 ≤ normSplitWork g :=
              normSplitWork_pos_of_monicNormalize_ne_zero_ne_one
                hheadReady.1 hheadReady.2
            have htailWork : normStackWork stack ≤ fuel :=
              normStackWork_tail_le_of_cons_le hwork hheadPos
            have htailReady : normStackReady stack :=
              normStackReady_tail hready
            rw [lasVegasSplitLoopWith.eq_def]
            simp only
            by_cases hskip :
                (CPolynomial.monicNormalize g == 0 ||
                    CPolynomial.monicNormalize g == 1) = true
            · rw [if_pos hskip]
              rcases hmemRoot' with hrootHead | hrootTail
              · subst rootPoly
                simp [hheadReady.1, hheadReady.2] at hskip
              · exact ih stack out htailWork htailReady
                  (Or.inr ⟨rootPoly, hrootTail, hrootNe, hrootEval⟩)
            · rw [if_neg hskip]
              have hgNorm : CPolynomial.monicNormalize g ≠ 0 := hheadReady.1
              by_cases hlin : isRepresentedLinearFactor (CPolynomial.monicNormalize g) = true
              · rw [if_pos hlin]
                rcases hmemRoot' with hrootHead | hrootTail
                · subst rootPoly
                  have hrootNorm :
                      CPolynomial.eval a (CPolynomial.monicNormalize g) = 0 :=
                    (monicNormalize_root_iff hrootNe).2 hrootEval
                  exact ih stack (out.push (CPolynomial.monicNormalize g))
                    htailWork htailReady
                    (Or.inl
                      ⟨CPolynomial.monicNormalize g, by simp, hlin,
                        representedLinearFactor_candidate_of_root hlin hrootNorm⟩)
                · exact ih stack (out.push (CPolynomial.monicNormalize g))
                    htailWork htailReady
                    (Or.inr ⟨rootPoly, hrootTail, hrootNe, hrootEval⟩)
              · rw [if_neg hlin]
                have hfallback :
                    ∃ factor,
                      factor ∈
                          (representedLinearFactorsOnly
                            (lasVegasSplitLoopWith M D enumeration traceCtx? cfg probes q fuel stack
                              (out ++ enumeratedLinearFactors enumeration
                                (CPolynomial.monicNormalize g)))).toList ∧
                        IsLinearRootFactorCandidate factor a := by
                  rcases hmemRoot' with hrootHead | hrootTail
                  · subst rootPoly
                    have hrootNorm :
                        CPolynomial.eval a (CPolynomial.monicNormalize g) = 0 :=
                      (monicNormalize_root_iff hrootNe).2 hrootEval
                    exact lasVegasSplitLoopWith_fallback_complete
                      M D enumeration traceCtx? cfg probes q hrootNorm
                  · exact ih stack
                      (out ++ enumeratedLinearFactors enumeration (CPolynomial.monicNormalize g))
                      htailWork htailReady
                      (Or.inr ⟨rootPoly, hrootTail, hrootNe, hrootEval⟩)
                by_cases hodd : (cfg.tryOddRandomizedSplitting && q % 2 == 1) = true
                · rw [if_pos hodd]
                  cases htry :
                      tryOddSplitAttemptsWith M D q probes (CPolynomial.monicNormalize g)
                        cfg.cutoff 0 with
                  | none =>
                      simp only
                      exact hfallback
                  | some children =>
                      simp only
                      have hchildrenWork :
                          stackWork children.toList ≤ normSplitWork g - 1 := by
                        have hworkChildren :=
                          tryOddSplitAttemptsWith_stackWork_le M D q probes
                            hgNorm cfg.cutoff 0 htry
                        simpa [normSplitWork, splitWork_monicNormalize_eq] using hworkChildren
                      have hnextWork :
                          normStackWork (children.toList ++ stack) ≤ fuel :=
                        normStackWork_split_stack_le hwork hheadPos hchildrenWork
                      have hchildrenReady : normStackReady children.toList := by
                        intro child hchild
                        exact normSplitWork_pos_ready
                          (tryOddSplitAttemptsWith_child_normSplitWork_pos
                            M D q probes hgNorm cfg.cutoff 0 htry hchild)
                      have hnextReady : normStackReady (children.toList ++ stack) :=
                        normStackReady_append hchildrenReady htailReady
                      rcases hmemRoot' with hrootHead | hrootTail
                      · subst rootPoly
                        have hrootNorm :
                            CPolynomial.eval a (CPolynomial.monicNormalize g) = 0 :=
                          (monicNormalize_root_iff hrootNe).2 hrootEval
                        rcases tryOddSplitAttemptsWith_root M D q probes
                            hgNorm hrootNorm cfg.cutoff 0 htry with
                          ⟨child, hchildMem, hchildRoot⟩
                        have hchildNe : child ≠ 0 := by
                          intro hzero
                          have hchildReady := hchildrenReady child hchildMem
                          exact hchildReady.1
                            (by simpa [hzero] using (monicNormalize_zero (F := F)))
                        exact ih (children.toList ++ stack) out hnextWork hnextReady
                          (Or.inr
                            ⟨child, by simp [hchildMem], hchildNe, hchildRoot⟩)
                      · exact ih (children.toList ++ stack) out hnextWork hnextReady
                          (Or.inr
                            ⟨rootPoly, by simp [hrootTail], hrootNe, hrootEval⟩)
                · rw [if_neg hodd]
                  by_cases heven : (cfg.tryEvenTraceSplitting && q % 2 == 0) = true
                  · rw [if_pos heven]
                    cases traceCtx? with
                    | none =>
                        simp only
                        exact hfallback
                    | some traceCtx =>
                        simp only
                        by_cases hmatch : traceContextMatchesQ traceCtx q = true
                        · rw [if_pos hmatch]
                          cases htry :
                              tryEvenTraceSplitAttemptsWith M D traceCtx q probes
                                (CPolynomial.monicNormalize g) cfg.cutoff 0 with
                          | none =>
                              simp only
                              exact hfallback
                          | some children =>
                              simp only
                              have hchildrenWork :
                                  stackWork children.toList ≤ normSplitWork g - 1 := by
                                have hworkChildren :=
                                  tryEvenTraceSplitAttemptsWith_stackWork_le
                                    M D traceCtx q probes hgNorm cfg.cutoff 0 htry
                                simpa [normSplitWork, splitWork_monicNormalize_eq] using
                                  hworkChildren
                              have hnextWork :
                                  normStackWork (children.toList ++ stack) ≤ fuel :=
                                normStackWork_split_stack_le hwork hheadPos hchildrenWork
                              have hchildrenReady : normStackReady children.toList := by
                                intro child hchild
                                exact normSplitWork_pos_ready
                                  (tryEvenTraceSplitAttemptsWith_child_normSplitWork_pos
                                    M D traceCtx q probes hgNorm cfg.cutoff 0 htry hchild)
                              have hnextReady : normStackReady (children.toList ++ stack) :=
                                normStackReady_append hchildrenReady htailReady
                              rcases hmemRoot' with hrootHead | hrootTail
                              · subst rootPoly
                                have hrootNorm :
                                    CPolynomial.eval a (CPolynomial.monicNormalize g) = 0 :=
                                  (monicNormalize_root_iff hrootNe).2 hrootEval
                                rcases tryEvenTraceSplitAttemptsWith_root
                                    M D traceCtx q probes hgNorm hrootNorm cfg.cutoff 0 htry with
                                  ⟨child, hchildMem, hchildRoot⟩
                                have hchildNe : child ≠ 0 := by
                                  intro hzero
                                  have hchildReady := hchildrenReady child hchildMem
                                  exact hchildReady.1
                                    (by simpa [hzero] using (monicNormalize_zero (F := F)))
                                exact ih (children.toList ++ stack) out hnextWork hnextReady
                                  (Or.inr
                                    ⟨child, by simp [hchildMem], hchildNe, hchildRoot⟩)
                              · exact ih (children.toList ++ stack) out hnextWork hnextReady
                                  (Or.inr
                                    ⟨rootPoly, by simp [hrootTail], hrootNe, hrootEval⟩)
                        · rw [if_neg hmatch]
                          exact hfallback
                  · rw [if_neg heven]
                    exact hfallback

private theorem lasVegasSplitLinearFactorsWithTrace?_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx? : Option (SmallPrimeTraceContext F))
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {p : CPolynomial F} {a : F}
    (_hvalid : lasVegasSplitterInput q p) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          (lasVegasSplitLinearFactorsWithTrace? M D enumeration traceCtx? cfg probes q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  let p' := CPolynomial.monicNormalize p
  have hp' : p' ≠ 0 := by
    dsimp [p']
    exact monicNormalize_ne_zero_of_ne_zero hp
  have hroot' : CPolynomial.eval a p' = 0 := by
    dsimp [p']
    exact (monicNormalize_root_iff hp).2 hroot
  have hwork : normStackWork [p'] ≤ 2 * p'.val.size + 1 := by
    rw [show normStackWork [p'] = splitWork p' by
      simp [normStackWork, normSplitWork, splitWork_monicNormalize_eq]]
    unfold splitWork
    rw [val_size_eq_natDegree_add_one_of_ne_zero hp', CPolynomial.natDegree_toPoly]
    omega
  have hready : normStackReady [p'] := by
    intro g hmem
    simp at hmem
    subst g
    constructor
    · exact monicNormalize_ne_zero_of_ne_zero hp'
    · intro hone
      have hrootNorm : CPolynomial.eval a (CPolynomial.monicNormalize p') = 0 :=
        monicNormalize_root_of_root hroot'
      rw [hone, CPolynomial.eval_one] at hrootNorm
      exact one_ne_zero hrootNorm
  have hloop :=
    lasVegasSplitLoopWith_complete_of_state M D enumeration traceCtx? cfg probes q
      (a := a) (2 * p'.val.size + 1) [p'] #[]
      hwork hready (Or.inr ⟨p', by simp, hp', hroot'⟩)
  simpa [lasVegasSplitLinearFactorsWithTrace?, lasVegasSplitCandidatesWithTrace?, p'] using hloop

/-- Completeness surface for bounded Las Vegas splitting plus enumeration fallback. -/
theorem lasVegasSplitLinearFactorsWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat)
    {p : CPolynomial F} {a : F}
    (hvalid : lasVegasSplitterInput q p) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          (lasVegasSplitLinearFactorsWith M D enumeration cfg probes q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  simpa [lasVegasSplitLinearFactorsWith] using
    lasVegasSplitLinearFactorsWithTrace?_complete
      M D enumeration none cfg probes q hvalid hp hroot

/-- Completeness surface for bounded Las Vegas splitting with characteristic-two trace metadata. -/
theorem lasVegasSplitLinearFactorsWithTrace_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (traceCtx : SmallPrimeTraceContext F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) (q : Nat)
    {p : CPolynomial F} {a : F}
    (hvalid : lasVegasSplitterInput q p) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          (lasVegasSplitLinearFactorsWithTrace M D enumeration traceCtx cfg probes q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  simpa [lasVegasSplitLinearFactorsWithTrace] using
    lasVegasSplitLinearFactorsWithTrace?_complete
      M D enumeration (some traceCtx) cfg probes q hvalid hp hroot

/-- Package bounded Las Vegas splitting as a finite-field linear-factor splitter. -/
def lasVegasLinearFactorProductSplitterWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (_ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := fun q p ↦
    lasVegasSplitLinearFactorsWith M D enumeration cfg probes q p
  validInput := fun q p ↦ lasVegasSplitterInput q p
  sound := by
    intro q p factor h
    exact lasVegasSplitLinearFactorsWith_sound M D enumeration cfg probes q h
  complete := by
    intro q p a hvalid hp hroot
    exact lasVegasSplitLinearFactorsWith_complete
      M D enumeration cfg probes q hvalid hp hroot

/-- Package bounded Las Vegas trace splitting as a finite-field linear-factor splitter. -/
def lasVegasLinearFactorProductSplitterWithTrace {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (_ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (traceCtx : SmallPrimeTraceContext F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := fun q p ↦
    lasVegasSplitLinearFactorsWithTrace M D enumeration traceCtx cfg probes q p
  validInput := fun q p ↦ lasVegasSplitterInput q p
  sound := by
    intro q p factor h
    exact lasVegasSplitLinearFactorsWithTrace_sound M D enumeration traceCtx cfg probes q h
  complete := by
    intro q p a hvalid hp hroot
    exact lasVegasSplitLinearFactorsWithTrace_complete
      M D enumeration traceCtx cfg probes q hvalid hp hroot

/-- Alias emphasizing the root-product precondition used by Las Vegas completeness. -/
theorem rootProduct_satisfies_lasVegasSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F)
    {p : CPolynomial F} (hp : p ≠ 0) :
    (lasVegasLinearFactorProductSplitterWith M D ctx enumeration cfg probes).validInput ctx.q
      (finiteFieldRootProductWith M D ctx p) := by
  exact finiteFieldRootProductWith_lasVegasSplitterInput M D ctx hp

end FiniteField

end Roots

end CPolynomial

end CompPoly

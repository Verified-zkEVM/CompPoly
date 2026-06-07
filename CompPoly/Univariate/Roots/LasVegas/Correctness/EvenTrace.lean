/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Correctness.Common

/-!
# Even-Trace Split Correctness for Las Vegas Splitting

Correctness lemmas for the characteristic-two trace split attempt and retry loop.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

private theorem cantorZassenhausEvenTraceAttemptWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let tracePoly := tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h
    let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)
    let complement := quotientAfterChild g' tracePart
    have hroot' : CPolynomial.eval a g' = 0 := (monicNormalize_root_iff hg).2 hroot
    have hdivTrace : tracePart.toPoly ∣ g'.toPoly := by
      dsimp [tracePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' tracePoly)
    by_cases htraceRoot : CPolynomial.eval a tracePart = 0
    · refine ⟨tracePart, ?_, htraceRoot⟩
      change tracePart ∈ (nontrivialProperChildren g' #[tracePart, complement]).toList
      have hsize' : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size := by
        simpa [g', h, tracePoly, tracePart, complement] using hsize
      have hproperTrace : isNontrivialProperChild g' tracePart = true :=
        left_proper_of_pair_filter_size_ge_two hsize'
      exact nontrivialProperChildren_mem_of_mem (by simp) hproperTrace
    · have hcomplementRoot : CPolynomial.eval a complement = 0 := by
        dsimp [complement]
        exact quotientAfterChild_root_of_not_child_root hdivTrace hroot' htraceRoot
      refine ⟨complement, ?_, hcomplementRoot⟩
      change complement ∈ (nontrivialProperChildren g' #[tracePart, complement]).toList
      have hsize' : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size := by
        simpa [g', h, tracePoly, tracePart, complement] using hsize
      have hproperComplement : isNontrivialProperChild g' complement = true :=
        right_proper_of_pair_filter_size_ge_two hsize'
      exact nontrivialProperChildren_mem_of_mem (by simp) hproperComplement
  next hsize =>
    simp at htry

private theorem cantorZassenhausEvenTraceAttemptWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hmem : child ∈ children.toList) :
    isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    exact proper_of_mem_nontrivialProperChildren hmem
  next hsize =>
    simp at htry

private theorem cantorZassenhausEvenTraceAttemptWith_stackWork_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hg : g ≠ 0) :
    stackWork children.toList ≤ splitWork (CPolynomial.monicNormalize g) - 1 := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let tracePoly := tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h
    let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)
    let complement := quotientAfterChild g' tracePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hsize' : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size := by
      simpa [g', h, tracePoly, tracePart, complement] using hsize
    have hproperTrace : isNontrivialProperChild g' tracePart = true :=
      left_proper_of_pair_filter_size_ge_two hsize'
    have hproperComplement : isNontrivialProperChild g' complement = true :=
      right_proper_of_pair_filter_size_ge_two hsize'
    have hchildrenList :
        (nontrivialProperChildren g' #[tracePart, complement]).toList =
          [tracePart, complement] := by
      unfold nontrivialProperChildren
      simp [hproperTrace, hproperComplement]
    have hdivTrace : tracePart.toPoly ∣ g'.toPoly := by
      dsimp [tracePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' tracePoly)
    have hsum :
        tracePart.toPoly.natDegree + complement.toPoly.natDegree ≤
          g'.toPoly.natDegree := by
      dsimp [complement]
      exact child_quotient_natDegree_le_parent hproperTrace hdivTrace hg'
    have htracePos : 0 < tracePart.toPoly.natDegree := by
      have hproperTrace' :
          isNontrivialProperChild g'
            (CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)) = true := by
        simpa [tracePart] using hproperTrace
      simpa [tracePart] using
        (monicNormalize_toPoly_natDegree_pos_of_proper hproperTrace')
    have hcomplementPos : 0 < complement.toPoly.natDegree := by
      have hproperComplement' :
          isNontrivialProperChild g'
            (CPolynomial.monicNormalize (CPolynomial.div g' tracePart)) = true := by
        simpa [complement, quotientAfterChild, hproperTrace] using hproperComplement
      simpa [complement, quotientAfterChild, hproperTrace] using
        (monicNormalize_toPoly_natDegree_pos_of_proper hproperComplement')
    rw [hchildrenList]
    simp [stackWork]
    have hsum' :
        tracePart.toPoly.natDegree + complement.toPoly.natDegree ≤
          (CPolynomial.monicNormalize g).toPoly.natDegree := by
      simpa [g'] using hsum
    exact splitWork_pair_le_of_natDegree_sum_le htracePos hcomplementPos hsum'
  next _hsize =>
    simp at htry

private theorem cantorZassenhausEvenTraceAttemptWith_child_normSplitWork_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hg : g ≠ 0) (hmem : child ∈ children.toList) :
    1 ≤ normSplitWork child := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let tracePoly := tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h
    let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)
    let complement := quotientAfterChild g' tracePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hsize' : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size := by
      simpa [g', h, tracePoly, tracePart, complement] using hsize
    have hproperTrace : isNontrivialProperChild g' tracePart = true :=
      left_proper_of_pair_filter_size_ge_two hsize'
    have hproperComplement : isNontrivialProperChild g' complement = true :=
      right_proper_of_pair_filter_size_ge_two hsize'
    have hchildrenList :
        (nontrivialProperChildren g' #[tracePart, complement]).toList =
          [tracePart, complement] := by
      unfold nontrivialProperChildren
      simp [hproperTrace, hproperComplement]
    rw [hchildrenList] at hmem
    simp at hmem
    rcases hmem with hmem | hmem
    · subst child
      have htraceNe : tracePart ≠ 0 := by
        unfold isNontrivialProperChild at hproperTrace
        simp at hproperTrace
        exact hproperTrace.1.1
      have htraceNotOne : tracePart ≠ 1 := by
        unfold isNontrivialProperChild at hproperTrace
        simp at hproperTrace
        exact hproperTrace.1.2
      have htraceMonic : tracePart.toPoly.Monic := by
        dsimp [tracePart]
        exact monicNormalize_toPoly_monic_of_ne_zero
          (gcdMonic_ne_zero_of_left hg')
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        htraceMonic htraceNe htraceNotOne
    · subst child
      have hcomplementNe : complement ≠ 0 := by
        unfold isNontrivialProperChild at hproperComplement
        simp at hproperComplement
        exact hproperComplement.1.1
      have hcomplementNotOne : complement ≠ 1 := by
        unfold isNontrivialProperChild at hproperComplement
        simp at hproperComplement
        exact hproperComplement.1.2
      have hdivTrace : tracePart.toPoly ∣ g'.toPoly := by
        dsimp [tracePart]
        exact (toPoly_monicNormalize_dvd_self _).trans
          (toPoly_gcdMonic_dvd_left g' tracePoly)
      have hg'Monic : g'.toPoly.Monic := by
        dsimp [g']
        exact monicNormalize_toPoly_monic_of_ne_zero hg
      have hcomplementMonic : complement.toPoly.Monic := by
        dsimp [complement]
        exact quotientAfterChild_toPoly_monic_of_dvd hg'Monic hdivTrace hg'
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        hcomplementMonic hcomplementNe hcomplementNotOne
  next _hsize =>
    simp at htry

theorem tryEvenTraceSplitAttemptsWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset = some children →
        ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry
      simp [tryEvenTraceSplitAttemptsWith] at htry
  | succ attempts ih =>
      intro offset children htry
      rw [tryEvenTraceSplitAttemptsWith] at htry
      cases hsplit :
          cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausEvenTraceAttemptWith_root
            M D traceCtx q probes hsplit hg hroot

private theorem tryEvenTraceSplitAttemptsWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F} :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset = some children →
        child ∈ children.toList →
          isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry hmem
      simp [tryEvenTraceSplitAttemptsWith] at htry
  | succ attempts ih =>
      intro offset children htry hmem
      rw [tryEvenTraceSplitAttemptsWith] at htry
      cases hsplit :
          cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry hmem
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausEvenTraceAttemptWith_child_proper
            M D traceCtx q probes hsplit hmem

theorem tryEvenTraceSplitAttemptsWith_stackWork_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    (hg : g ≠ 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset = some children →
        stackWork children.toList ≤ splitWork (CPolynomial.monicNormalize g) - 1 := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry
      simp [tryEvenTraceSplitAttemptsWith] at htry
  | succ attempts ih =>
      intro offset children htry
      rw [tryEvenTraceSplitAttemptsWith] at htry
      cases hsplit :
          cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausEvenTraceAttemptWith_stackWork_le
            M D traceCtx q probes hsplit hg

theorem tryEvenTraceSplitAttemptsWith_child_normSplitWork_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    (hg : g ≠ 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset = some children →
        child ∈ children.toList →
          1 ≤ normSplitWork child := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry hmem
      simp [tryEvenTraceSplitAttemptsWith] at htry
  | succ attempts ih =>
      intro offset children htry hmem
      rw [tryEvenTraceSplitAttemptsWith] at htry
      cases hsplit :
          cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry hmem
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausEvenTraceAttemptWith_child_normSplitWork_pos
            M D traceCtx q probes hsplit hg hmem

end FiniteField

end Roots

end CPolynomial

end CompPoly

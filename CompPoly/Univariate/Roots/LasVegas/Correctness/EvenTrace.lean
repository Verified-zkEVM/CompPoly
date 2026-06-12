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

theorem cantorZassenhausEvenTraceAttemptWith_child_proper {F : Type*}
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

theorem cantorZassenhausEvenTraceAttemptWith_stackWork_le {F : Type*}
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

theorem cantorZassenhausEvenTraceAttemptWith_child_normSplitWork_pos {F : Type*}
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

set_option maxHeartbeats 1600000 in
/-- The trace split attempt depends on the probe family only through the probe
it actually draws. -/
theorem cantorZassenhausEvenTraceAttemptWith_probe_congr {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) {p1 p2 : ProbeFamily F} {g : CPolynomial F} {a1 a2 : Nat}
    (hprobe : p1.probe q (CPolynomial.monicNormalize g) a1 =
      p2.probe q (CPolynomial.monicNormalize g) a2) :
    cantorZassenhausEvenTraceAttemptWith M D traceCtx q p1 g a1 =
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q p2 g a2 := by
  simp only [cantorZassenhausEvenTraceAttemptWith]
  rw [hprobe]

set_option maxHeartbeats 1600000 in
/-- The trace retry loop depends on the probe family only through the probes it
actually draws. -/
theorem tryEvenTraceSplitAttemptsWith_probe_congr {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) {p1 p2 : ProbeFamily F} {g : CPolynomial F} :
    ∀ (attempts offset1 offset2 : Nat),
      (∀ i, i < attempts →
        p1.probe q (CPolynomial.monicNormalize g) (offset1 + i) =
          p2.probe q (CPolynomial.monicNormalize g) (offset2 + i)) →
      tryEvenTraceSplitAttemptsWith M D traceCtx q p1 g attempts offset1 =
        tryEvenTraceSplitAttemptsWith M D traceCtx q p2 g attempts offset2 := by
  intro attempts
  induction attempts with
  | zero =>
      intro o1 o2 _hagree
      unfold tryEvenTraceSplitAttemptsWith
      rfl
  | succ attempts ih =>
      intro o1 o2 hagree
      unfold tryEvenTraceSplitAttemptsWith
      rw [cantorZassenhausEvenTraceAttemptWith_probe_congr M D traceCtx q (g := g)
        (by simpa using hagree 0 (by omega))]
      cases htry : cantorZassenhausEvenTraceAttemptWith M D traceCtx q p2 g o2 with
      | some c => simp
      | none =>
          simp only
          exact ih (o1 + 1) (o2 + 1) (by
            intro i hi
            have h := hagree (i + 1) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)

/-- A successful trace retry loop result is produced by some single attempt. -/
theorem tryEvenTraceSplitAttemptsWith_eq_some_exists_attempt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} :
    ∀ (attempts offset : Nat) {children : Array (CPolynomial F)},
      tryEvenTraceSplitAttemptsWith M D traceCtx q probes g attempts offset =
        some children →
      ∃ attempt,
        cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt =
          some children := by
  intro attempts
  induction attempts with
  | zero =>
      intro offset children htry
      cases htry
  | succ attempts ih =>
      intro offset children htry
      unfold tryEvenTraceSplitAttemptsWith at htry
      cases hsplit : cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g
          offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact ⟨offset, hsplit⟩

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

private theorem eval_add_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (z : F) (p q : CPolynomial F) :
    CPolynomial.eval z (p + q) = CPolynomial.eval z p + CPolynomial.eval z q := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

private theorem eval_tracePowerSumPolynomialLoopWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus : CPolynomial F} {z : F}
    (hroot : CPolynomial.eval z modulus = 0) (p : Nat) :
    ∀ (steps : Nat) (power acc : CPolynomial F),
      CPolynomial.eval z (tracePowerSumPolynomialLoopWith M D modulus p steps power acc) =
        CPolynomial.eval z acc +
          ∑ i ∈ Finset.range steps, CPolynomial.eval z power ^ p ^ i := by
  intro steps
  induction steps with
  | zero =>
      intro power acc
      rw [tracePowerSumPolynomialLoopWith]
      simp
  | succ steps ih =>
      intro power acc
      rw [tracePowerSumPolynomialLoopWith]
      rw [ih, eval_reduceModWith_eq_self_of_root D hroot, eval_add_eq,
        eval_powModWith_eq_pow M D hroot p]
      have hpow : ∀ i : Nat,
          (CPolynomial.eval z power ^ p) ^ p ^ i = CPolynomial.eval z power ^ p ^ (i + 1) := by
        intro i
        rw [← pow_mul, pow_succ, Nat.mul_comm (p ^ i) p]
      rw [Finset.sum_congr rfl fun i _ ↦ hpow i, Finset.sum_range_succ']
      rw [pow_zero, pow_one]
      ring

/-- Evaluating the modular trace power sum at a root of the modulus computes
the field-level trace power sum of the probe value. -/
theorem eval_tracePowerSumPolynomialWith_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {modulus : CPolynomial F} {z : F}
    (hroot : CPolynomial.eval z modulus = 0) (p k : Nat) (h : CPolynomial F) :
    CPolynomial.eval z (tracePowerSumPolynomialWith M D modulus p k h) =
      tracePowerSum p k (CPolynomial.eval z h) := by
  unfold tracePowerSumPolynomialWith
  rw [eval_tracePowerSumPolynomialLoopWith M D hroot p k _ _,
    eval_reduceModWith_eq_self_of_root D hroot, tracePowerSum_eq_sum_range]
  have hzero : CPolynomial.eval z (0 : CPolynomial F) = 0 := by
    rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_zero, Polynomial.eval_zero]
  rw [hzero, _root_.zero_add]

private theorem two_le_size_filter_pair {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {parent u v : CPolynomial F}
    (hu : isNontrivialProperChild parent u = true)
    (hv : isNontrivialProperChild parent v = true) :
    2 ≤ (nontrivialProperChildren parent #[u, v]).size := by
  unfold nontrivialProperChildren
  rw [← Array.length_toList, Array.toList_filter]
  simp [hu, hv]

theorem cantorZassenhausEvenTraceAttemptWith_size_ge_two {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children) :
    2 ≤ children.size := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    simpa using hsize
  next _hsize =>
    simp at htry

theorem cantorZassenhausEvenTraceAttemptWith_child_dvd_input {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry :
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q probes g attempt = some children)
    (hmem : child ∈ children.toList) :
    child.toPoly ∣ g.toPoly := by
  unfold cantorZassenhausEvenTraceAttemptWith at htry
  simp only at htry
  split at htry
  next _hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let tracePoly := tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h
    let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)
    let complement := quotientAfterChild g' tracePart
    have hdivTrace : tracePart.toPoly ∣ g'.toPoly := by
      dsimp [tracePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' tracePoly)
    have hmem' : child ∈ (nontrivialProperChildren g' #[tracePart, complement]).toList :=
      hmem
    have hpair : child = tracePart ∨ child = complement := by
      unfold nontrivialProperChildren at hmem'
      rw [Array.toList_filter, List.mem_filter] at hmem'
      simpa using hmem'.1
    have hnorm : g'.toPoly ∣ g.toPoly := toPoly_monicNormalize_dvd_self g
    rcases hpair with hchild | hchild
    · subst hchild
      exact hdivTrace.trans hnorm
    · subst hchild
      exact (quotientAfterChild_toPoly_dvd_parent hdivTrace).trans hnorm
  next _hsize =>
    simp at htry

/--
A fixed probe whose trace power sums separate two roots of `g` forces the
characteristic-two trace split attempt to succeed: the root with trace zero
lands in `gcd(g, Tr(h))` and the root with nonzero trace survives into the
complement, so both candidates are nontrivial proper children.
-/
theorem cantorZassenhausEvenTraceAttemptWith_success_of_trace_separated {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (traceCtx : SmallPrimeTraceContext F)
    (q : Nat) {g h : CPolynomial F} {a b : F} (attempt : Nat)
    (hg : g ≠ 0)
    (hrootA : CPolynomial.eval a g = 0)
    (hrootB : CPolynomial.eval b g = 0)
    (hsepA : tracePowerSum traceCtx.p traceCtx.k (CPolynomial.eval a h) = 0)
    (hsepB : tracePowerSum traceCtx.p traceCtx.k (CPolynomial.eval b h) ≠ 0) :
    ∃ children,
      cantorZassenhausEvenTraceAttemptWith M D traceCtx q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F)
        g attempt = some children := by
  cases htry : cantorZassenhausEvenTraceAttemptWith M D traceCtx q
      ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g attempt with
  | some children => exact ⟨children, rfl⟩
  | none =>
      exfalso
      unfold cantorZassenhausEvenTraceAttemptWith at htry
      simp only at htry
      split at htry
      next hsize => simp at htry
      next hsize =>
        apply hsize
        let g' := CPolynomial.monicNormalize g
        let h' := reduceModWith D g' h
        let tracePoly := tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h'
        let tracePart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' tracePoly)
        let complement := quotientAfterChild g' tracePart
        have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
        have hgMonic : g'.toPoly.Monic := monicNormalize_toPoly_monic_of_ne_zero hg
        have hA' : CPolynomial.eval a g' = 0 := (monicNormalize_root_iff hg).2 hrootA
        have hB' : CPolynomial.eval b g' = 0 := (monicNormalize_root_iff hg).2 hrootB
        have hhA : CPolynomial.eval a h' = CPolynomial.eval a h :=
          eval_reduceModWith_eq_self_of_root D hA'
        have hhB : CPolynomial.eval b h' = CPolynomial.eval b h :=
          eval_reduceModWith_eq_self_of_root D hB'
        have htraceA : CPolynomial.eval a tracePoly = 0 := by
          show CPolynomial.eval a
            (tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h') = 0
          rw [eval_tracePowerSumPolynomialWith_eq M D hA', hhA]
          exact hsepA
        have htraceB : CPolynomial.eval b tracePoly ≠ 0 := by
          show CPolynomial.eval b
            (tracePowerSumPolynomialWith M D g' traceCtx.p traceCtx.k h') ≠ 0
          rw [eval_tracePowerSumPolynomialWith_eq M D hB', hhB]
          exact hsepB
        have htraceIff : ∀ z : F, CPolynomial.eval z tracePart = 0 ↔
            CPolynomial.eval z g' = 0 ∧ CPolynomial.eval z tracePoly = 0 :=
          fun z ↦ eval_monicNormalize_gcdMonic_eq_zero_iff g' tracePoly z
        have hdivTrace : tracePart.toPoly ∣ g'.toPoly :=
          (toPoly_monicNormalize_dvd_self _).trans (toPoly_gcdMonic_dvd_left g' tracePoly)
        have htracePartNe : tracePart ≠ 0 :=
          monicNormalize_ne_zero_of_ne_zero (gcdMonic_ne_zero_left tracePoly hg')
        have htracePartMonic : tracePart.toPoly.Monic :=
          monicNormalize_toPoly_monic_of_ne_zero (gcdMonic_ne_zero_left tracePoly hg')
        have htracePartA : CPolynomial.eval a tracePart = 0 :=
          (htraceIff a).2 ⟨hA', htraceA⟩
        have htracePartBne : CPolynomial.eval b tracePart ≠ 0 := by
          intro hb
          exact htraceB ((htraceIff b).1 hb).2
        have htraceSizeLt : tracePart.val.size < g'.val.size := by
          by_contra hnot
          apply htracePartBne
          have heq : g' = tracePart :=
            eq_of_monic_dvd_of_val_size_le htracePartMonic hgMonic hdivTrace
              htracePartNe hg' (Nat.le_of_not_lt hnot)
          rw [← heq]
          exact hB'
        have hproperTrace : isNontrivialProperChild g' tracePart = true :=
          proper_child_of_ne_zero_root_size_lt htracePartNe htracePartA htraceSizeLt
        have hcompB : CPolynomial.eval b complement = 0 :=
          quotientAfterChild_root_of_not_child_root hdivTrace hB' htracePartBne
        have hcompNe : complement ≠ 0 := quotientAfterChild_ne_zero_of_dvd hdivTrace hg'
        have hcompSizeLt : complement.val.size < g'.val.size :=
          quotientAfterChild_size_lt_parent_of_monicNormalize_proper hg' hproperTrace
        have hproperComp : isNontrivialProperChild g' complement = true :=
          proper_child_of_ne_zero_root_size_lt hcompNe hcompB hcompSizeLt
        have hfinal : 2 ≤ (nontrivialProperChildren g' #[tracePart, complement]).size :=
          two_le_size_filter_pair hproperTrace hproperComp
        simpa [g', h', tracePoly, tracePart, complement] using hfinal

end FiniteField

end Roots

end CPolynomial

end CompPoly

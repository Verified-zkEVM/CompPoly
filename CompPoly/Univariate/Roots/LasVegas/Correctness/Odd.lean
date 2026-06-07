/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Correctness.Common

/-!
# Odd Split Correctness for Las Vegas Splitting

Correctness lemmas for the odd-characteristic Cantor-Zassenhaus split attempt
and retry loop.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

private theorem cantorZassenhausOddAttemptWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let s := powModWith M D g' h ((q - 1) / 2)
    let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)
    let afterZero := quotientAfterChild g' zeroPart
    let squarePart := CPolynomial.monicNormalize
      (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
    let afterSquare := quotientAfterChild afterZero squarePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hroot' : CPolynomial.eval a g' = 0 := (monicNormalize_root_iff hg).2 hroot
    have hsize' :
        2 ≤ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups.size := by
      simpa [g', h, s, zeroPart, afterZero, squarePart, afterSquare] using hsize
    have hdivZero : zeroPart.toPoly ∣ g'.toPoly := by
      dsimp [zeroPart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' h)
    have hdivSquare : squarePart.toPoly ∣ afterZero.toPoly := by
      dsimp [squarePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left afterZero (s - (1 : CPolynomial F)))
    have hzeroMem (hproperZero : isNontrivialProperChild g' zeroPart = true) :
        zeroPart ∈
          ((nontrivialProperChildren g'
            #[zeroPart, squarePart, afterSquare]).eraseDups).toList := by
      have hraw :
          zeroPart ∈ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).toList :=
        nontrivialProperChildren_mem_of_mem (by simp) hproperZero
      simpa using (mem_eraseDups_of_mem (by simpa using hraw))
    have hsquareMem (hproperSquare : isNontrivialProperChild g' squarePart = true) :
        squarePart ∈
          ((nontrivialProperChildren g'
            #[zeroPart, squarePart, afterSquare]).eraseDups).toList := by
      have hraw :
          squarePart ∈ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).toList :=
        nontrivialProperChildren_mem_of_mem (by simp) hproperSquare
      simpa using (mem_eraseDups_of_mem (by simpa using hraw))
    have hafterMem (hproperAfter : isNontrivialProperChild g' afterSquare = true) :
        afterSquare ∈
          ((nontrivialProperChildren g'
            #[zeroPart, squarePart, afterSquare]).eraseDups).toList := by
      have hraw :
          afterSquare ∈ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).toList :=
        nontrivialProperChildren_mem_of_mem (by simp) hproperAfter
      simpa using (mem_eraseDups_of_mem (by simpa using hraw))
    have hafterZeroRoot_of_not_zero
        (hzeroRoot : CPolynomial.eval a zeroPart ≠ 0) :
        CPolynomial.eval a afterZero = 0 := by
      dsimp [afterZero]
      exact quotientAfterChild_root_of_not_child_root hdivZero hroot' hzeroRoot
    have hafterSquareRoot_of_afterZero
        (hafterZeroRoot : CPolynomial.eval a afterZero = 0)
        (hsquareRoot : CPolynomial.eval a squarePart ≠ 0) :
        CPolynomial.eval a afterSquare = 0 := by
      dsimp [afterSquare]
      exact quotientAfterChild_root_of_not_child_root hdivSquare hafterZeroRoot hsquareRoot
    by_cases hzeroRoot : CPolynomial.eval a zeroPart = 0
    · by_cases hproperZero : isNontrivialProperChild g' zeroPart = true
      · refine ⟨zeroPart, hzeroMem hproperZero, hzeroRoot⟩
      · have hafterZeroRoot : CPolynomial.eval a afterZero = 0 := by
          dsimp [afterZero, quotientAfterChild]
          rw [if_neg hproperZero]
          exact hroot'
        by_cases hsquareRoot : CPolynomial.eval a squarePart = 0
        · have hproperSquare :
              isNontrivialProperChild g' squarePart = true :=
            middle_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
              hproperZero hsize'
          refine ⟨squarePart, hsquareMem hproperSquare, hsquareRoot⟩
        · have hafterRoot : CPolynomial.eval a afterSquare = 0 :=
            hafterSquareRoot_of_afterZero hafterZeroRoot hsquareRoot
          have hproperAfter :
              isNontrivialProperChild g' afterSquare = true :=
            right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
              hproperZero hsize'
          refine ⟨afterSquare, hafterMem hproperAfter, hafterRoot⟩
    · have hafterZeroRoot : CPolynomial.eval a afterZero = 0 :=
        hafterZeroRoot_of_not_zero hzeroRoot
      by_cases hsquareRoot : CPolynomial.eval a squarePart = 0
      · by_cases hproperSquare : isNontrivialProperChild g' squarePart = true
        · refine ⟨squarePart, hsquareMem hproperSquare, hsquareRoot⟩
        · have hafterRoot : CPolynomial.eval a afterSquare = 0 := by
            have hafterZeroSizeLe : afterZero.val.size ≤ g'.val.size := by
              dsimp [afterZero]
              exact quotientAfterChild_size_le_parent hg'
            have hnotProperAfterZero :
                ¬ isNontrivialProperChild afterZero squarePart = true := by
              intro hproperAfterZero
              exact hproperSquare
                (proper_child_of_proper_intermediate hproperAfterZero hafterZeroSizeLe)
            dsimp [afterSquare, quotientAfterChild]
            rw [if_neg hnotProperAfterZero]
            exact hafterZeroRoot
          have hproperAfter :
              isNontrivialProperChild g' afterSquare = true :=
            right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_middle
              hproperSquare hsize'
          refine ⟨afterSquare, hafterMem hproperAfter, hafterRoot⟩
      · have hafterRoot : CPolynomial.eval a afterSquare = 0 :=
          hafterSquareRoot_of_afterZero hafterZeroRoot hsquareRoot
        by_cases hproperSquare : isNontrivialProperChild g' squarePart = true
        · by_cases hproperAfter : isNontrivialProperChild g' afterSquare = true
          · refine ⟨afterSquare, hafterMem hproperAfter, hafterRoot⟩
          · by_cases hproperZero : isNontrivialProperChild g' zeroPart = true
            · have hafterZeroNe : afterZero ≠ 0 :=
                quotientAfterChild_ne_zero_of_dvd hdivZero hg'
              have hafterSquareNe : afterSquare ≠ 0 :=
                quotientAfterChild_ne_zero_of_dvd hdivSquare hafterZeroNe
              have hafterZeroSize : afterZero.val.size < g'.val.size := by
                have hproperZero' :
                    isNontrivialProperChild g'
                      (CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)) = true := by
                  simpa [zeroPart] using hproperZero
                simpa [afterZero, zeroPart] using
                  (quotientAfterChild_size_lt_parent_of_monicNormalize_proper
                    (parent := g') (childSource := CPolynomial.gcdMonic g' h)
                    hg' hproperZero')
              have hafterSquareSizeLe : afterSquare.val.size ≤ afterZero.val.size := by
                dsimp [afterSquare]
                exact quotientAfterChild_size_le_parent hafterZeroNe
              have hafterSquareSize : afterSquare.val.size < g'.val.size :=
                lt_of_le_of_lt hafterSquareSizeLe hafterZeroSize
              have hproperAfter' :
                  isNontrivialProperChild g' afterSquare = true :=
                proper_child_of_ne_zero_root_size_lt hafterSquareNe hafterRoot hafterSquareSize
              exact False.elim (hproperAfter hproperAfter')
            · have hproperAfter' :
                isNontrivialProperChild g' afterSquare = true :=
                right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
                  hproperZero hsize'
              exact False.elim (hproperAfter hproperAfter')
        · have hproperAfter :
              isNontrivialProperChild g' afterSquare = true :=
            right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_middle
              hproperSquare hsize'
          refine ⟨afterSquare, hafterMem hproperAfter, hafterRoot⟩
  next _hsize =>
    simp at htry

theorem cantorZassenhausOddAttemptWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hmem : child ∈ children.toList) :
    isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next _hsize =>
    injection htry with hchildren
    subst children
    have hraw := mem_of_mem_eraseDups (by simpa using hmem)
    exact proper_of_mem_nontrivialProperChildren (by simpa using hraw)
  next _hsize =>
    simp at htry

theorem cantorZassenhausOddAttemptWith_size_ge_two {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children) :
    2 ≤ children.size := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    simpa using hsize
  next _hsize =>
    simp at htry

theorem cantorZassenhausOddAttemptWith_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children) :
    g ≠ 0 := by
  intro hg
  have hsize := cantorZassenhausOddAttemptWith_size_ge_two M D q probes htry
  have hpos : 0 < children.size := by omega
  let child : CPolynomial F := children[0]
  have hmem : child ∈ children.toList := by
    exact Array.getElem_mem_toList hpos
  have hproper :=
    cantorZassenhausOddAttemptWith_child_proper M D q probes htry hmem
  unfold isNontrivialProperChild at hproper
  simp [hg, monicNormalize_zero] at hproper
  exact Nat.not_lt_zero _ hproper.2

theorem cantorZassenhausOddAttemptWith_root_preserved {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hroot : CPolynomial.eval a g = 0) :
    ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  exact cantorZassenhausOddAttemptWith_root M D q probes htry
    (cantorZassenhausOddAttemptWith_ne_zero M D q probes htry) hroot

theorem cantorZassenhausOddAttemptWith_child_dvd_input {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hmem : child ∈ children.toList) :
    child.toPoly ∣ g.toPoly := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next _hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let s := powModWith M D g' h ((q - 1) / 2)
    let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)
    let afterZero := quotientAfterChild g' zeroPart
    let squarePart := CPolynomial.monicNormalize
      (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
    let afterSquare := quotientAfterChild afterZero squarePart
    have hdivZero : zeroPart.toPoly ∣ g'.toPoly := by
      dsimp [zeroPart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' h)
    have hafterZeroDvd : afterZero.toPoly ∣ g'.toPoly := by
      dsimp [afterZero]
      exact quotientAfterChild_toPoly_dvd_parent hdivZero
    have hdivSquare : squarePart.toPoly ∣ afterZero.toPoly := by
      dsimp [squarePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left afterZero (s - (1 : CPolynomial F)))
    have hafterSquareDvd : afterSquare.toPoly ∣ g'.toPoly := by
      dsimp [afterSquare]
      exact (quotientAfterChild_toPoly_dvd_parent hdivSquare).trans hafterZeroDvd
    have hraw := mem_of_mem_eraseDups (by simpa using hmem)
    unfold nontrivialProperChildren at hraw
    simp at hraw
    rcases hraw with ⟨hrawMem, _hproper⟩
    have hchildDvdNorm : child.toPoly ∣ g'.toPoly := by
      rcases hrawMem with hchild | hchild | hchild
      · subst child
        exact hdivZero
      · subst child
        exact hdivSquare.trans hafterZeroDvd
      · subst child
        exact hafterSquareDvd
    exact hchildDvdNorm.trans (by simpa [g'] using toPoly_monicNormalize_dvd_self g)
  next _hsize =>
    simp at htry

private theorem cantorZassenhausOddAttemptWith_child_normSplitWork_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hg : g ≠ 0) (hmem : child ∈ children.toList) :
    1 ≤ normSplitWork child := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next _hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let s := powModWith M D g' h ((q - 1) / 2)
    let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)
    let afterZero := quotientAfterChild g' zeroPart
    let squarePart := CPolynomial.monicNormalize
      (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
    let afterSquare := quotientAfterChild afterZero squarePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hdivZero : zeroPart.toPoly ∣ g'.toPoly := by
      dsimp [zeroPart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' h)
    have hafterZeroNe : afterZero ≠ 0 := by
      dsimp [afterZero]
      exact quotientAfterChild_ne_zero_of_dvd hdivZero hg'
    have hg'Monic : g'.toPoly.Monic := by
      dsimp [g']
      exact monicNormalize_toPoly_monic_of_ne_zero hg
    have hafterZeroMonic : afterZero.toPoly.Monic := by
      dsimp [afterZero]
      exact quotientAfterChild_toPoly_monic_of_dvd hg'Monic hdivZero hg'
    have hdivSquare : squarePart.toPoly ∣ afterZero.toPoly := by
      dsimp [squarePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left afterZero (s - (1 : CPolynomial F)))
    have hraw := mem_of_mem_eraseDups (by simpa using hmem)
    unfold nontrivialProperChildren at hraw
    simp at hraw
    rcases hraw with ⟨hrawMem, hproper⟩
    rcases hrawMem with hchild | hchild | hchild
    · subst child
      have hzeroNe : zeroPart ≠ 0 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.1
      have hzeroNotOne : zeroPart ≠ 1 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.2
      have hzeroMonic : zeroPart.toPoly.Monic := by
        dsimp [zeroPart]
        exact monicNormalize_toPoly_monic_of_ne_zero
          (gcdMonic_ne_zero_of_left hg')
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        hzeroMonic hzeroNe hzeroNotOne
    · subst child
      have hsquareNe : squarePart ≠ 0 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.1
      have hsquareNotOne : squarePart ≠ 1 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.2
      have hsquareMonic : squarePart.toPoly.Monic := by
        dsimp [squarePart]
        exact monicNormalize_toPoly_monic_of_ne_zero
          (gcdMonic_ne_zero_of_left hafterZeroNe)
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        hsquareMonic hsquareNe hsquareNotOne
    · subst child
      have hafterNe : afterSquare ≠ 0 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.1
      have hafterNotOne : afterSquare ≠ 1 := by
        unfold isNontrivialProperChild at hproper
        simp at hproper
        exact hproper.1.2
      have hafterMonic : afterSquare.toPoly.Monic := by
        dsimp [afterSquare]
        exact quotientAfterChild_toPoly_monic_of_dvd
          hafterZeroMonic hdivSquare hafterZeroNe
      exact normSplitWork_pos_of_monic_ne_zero_ne_one
        hafterMonic hafterNe hafterNotOne
  next _hsize =>
    simp at htry

set_option maxHeartbeats 800000 in
private theorem cantorZassenhausOddAttemptWith_stackWork_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    {attempt : Nat} {children : Array (CPolynomial F)}
    (htry : cantorZassenhausOddAttemptWith M D q probes g attempt = some children)
    (hg : g ≠ 0) :
    stackWork children.toList ≤ splitWork (CPolynomial.monicNormalize g) - 1 := by
  unfold cantorZassenhausOddAttemptWith at htry
  simp only at htry
  split at htry
  next hsize =>
    injection htry with hchildren
    subst children
    let g' := CPolynomial.monicNormalize g
    let h := reduceModWith D g' (probes.probe q g' attempt)
    let s := powModWith M D g' h ((q - 1) / 2)
    let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)
    let afterZero := quotientAfterChild g' zeroPart
    let squarePart := CPolynomial.monicNormalize
      (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
    let afterSquare := quotientAfterChild afterZero squarePart
    have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
    have hsize' :
        2 ≤ (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare]).eraseDups.size := by
      simpa [g', h, s, zeroPart, afterZero, squarePart, afterSquare] using hsize
    have hdivZero : zeroPart.toPoly ∣ g'.toPoly := by
      dsimp [zeroPart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left g' h)
    have hg'Monic : g'.toPoly.Monic := by
      dsimp [g']
      exact monicNormalize_toPoly_monic_of_ne_zero hg
    have hafterZeroNe : afterZero ≠ 0 := by
      dsimp [afterZero]
      exact quotientAfterChild_ne_zero_of_dvd hdivZero hg'
    have hafterZeroMonic : afterZero.toPoly.Monic := by
      dsimp [afterZero]
      exact quotientAfterChild_toPoly_monic_of_dvd hg'Monic hdivZero hg'
    have hdivSquare : squarePart.toPoly ∣ afterZero.toPoly := by
      dsimp [squarePart]
      exact (toPoly_monicNormalize_dvd_self _).trans
        (toPoly_gcdMonic_dvd_left afterZero (s - (1 : CPolynomial F)))
    by_cases hproperZero : isNontrivialProperChild g' zeroPart = true
    · have hzeroPos : 0 < zeroPart.toPoly.natDegree := by
        have hproperZero' :
            isNontrivialProperChild g'
              (CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h)) = true := by
          simpa [zeroPart] using hproperZero
        simpa [zeroPart] using
          (monicNormalize_toPoly_natDegree_pos_of_proper hproperZero')
      have hzeroAfterSum :
          zeroPart.toPoly.natDegree + afterZero.toPoly.natDegree ≤
            g'.toPoly.natDegree := by
        dsimp [afterZero]
        exact child_quotient_natDegree_le_parent hproperZero hdivZero hg'
      by_cases hproperSquareAfter : isNontrivialProperChild afterZero squarePart = true
      · have hafterZeroSizeLe : afterZero.val.size ≤ g'.val.size := by
          dsimp [afterZero]
          exact quotientAfterChild_size_le_parent hg'
        have hproperSquareG : isNontrivialProperChild g' squarePart = true :=
          proper_child_of_proper_intermediate hproperSquareAfter hafterZeroSizeLe
        have hsquarePos : 0 < squarePart.toPoly.natDegree := by
          have hproperSquare' :
              isNontrivialProperChild afterZero
                (CPolynomial.monicNormalize
                  (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))) = true := by
            simpa [squarePart] using hproperSquareAfter
          simpa [squarePart] using
            (monicNormalize_toPoly_natDegree_pos_of_proper hproperSquare')
        have hsquareAfterSum :
            squarePart.toPoly.natDegree + afterSquare.toPoly.natDegree ≤
              afterZero.toPoly.natDegree := by
          dsimp [afterSquare]
          exact child_quotient_natDegree_le_parent hproperSquareAfter hdivSquare hafterZeroNe
        have hsum :
            zeroPart.toPoly.natDegree + squarePart.toPoly.natDegree +
              afterSquare.toPoly.natDegree ≤ g'.toPoly.natDegree := by
          omega
        have hraw :
            stackWork
                ((nontrivialProperChildren g'
                  #[zeroPart, squarePart, afterSquare]).eraseDups).toList ≤
              splitWork zeroPart + (splitWork squarePart + (splitWork afterSquare + 0)) := by
          have herase :=
            stackWork_eraseDups_le
              (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare])
          by_cases hproperAfterG : isNontrivialProperChild g' afterSquare = true
          · unfold nontrivialProperChildren at herase ⊢
            simp [hproperZero, hproperSquareG, hproperAfterG, stackWork] at herase ⊢
            omega
          · unfold nontrivialProperChildren at herase ⊢
            simp [hproperZero, hproperSquareG, hproperAfterG, stackWork] at herase ⊢
            omega
        have hwork :
            splitWork zeroPart + (splitWork squarePart + (splitWork afterSquare + 0)) ≤
              splitWork g' - 1 :=
          splitWork_triple_le_of_first_two_pos_natDegree_sum_le hzeroPos hsquarePos hsum
        exact le_trans hraw (by simpa [g'] using hwork)
      · have hafterEq : afterSquare = afterZero := by
          dsimp [afterSquare, quotientAfterChild]
          rw [if_neg hproperSquareAfter]
        by_cases hproperSquareG : isNontrivialProperChild g' squarePart = true
        · have hsquareNe : squarePart ≠ 0 := by
            unfold isNontrivialProperChild at hproperSquareG
            simp at hproperSquareG
            exact hproperSquareG.1.1
          have hsquareNotOne : squarePart ≠ 1 := by
            unfold isNontrivialProperChild at hproperSquareG
            simp at hproperSquareG
            exact hproperSquareG.1.2
          have hsquareMonic : squarePart.toPoly.Monic := by
            dsimp [squarePart]
            exact monicNormalize_toPoly_monic_of_ne_zero
              (gcdMonic_ne_zero_of_left hafterZeroNe)
          have hsqEq : afterZero = squarePart :=
            eq_of_not_proper_of_monic_dvd hsquareMonic hafterZeroMonic hdivSquare
              hsquareNe hafterZeroNe hsquareNotOne hproperSquareAfter
          have hafterZeroPos : 0 < afterZero.toPoly.natDegree := by
            rw [hsqEq]
            exact toPoly_natDegree_pos_of_monic_ne_zero_ne_one
              hsquareMonic hsquareNe hsquareNotOne
          have hpair :
              splitWork zeroPart + splitWork afterZero ≤ splitWork g' - 1 :=
            splitWork_pair_le_of_natDegree_sum_le hzeroPos hafterZeroPos hzeroAfterSum
          have hraw :
              stackWork
                  ((nontrivialProperChildren g'
                    #[zeroPart, squarePart, afterSquare]).eraseDups).toList ≤
                splitWork zeroPart + splitWork afterZero := by
            rw [hafterEq, hsqEq]
            unfold nontrivialProperChildren
            simp [hproperZero, hproperSquareG]
            exact stackWork_eraseDups_triple_dup_right_le zeroPart squarePart
          exact le_trans hraw (by simpa [g'] using hpair)
        · have hproperAfterG :
              isNontrivialProperChild g' afterSquare = true :=
            right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_middle
              hproperSquareG hsize'
          have hafterZeroProper : isNontrivialProperChild g' afterZero = true := by
            simpa [hafterEq] using hproperAfterG
          have hafterZeroPos : 0 < afterZero.toPoly.natDegree := by
            have hafterZeroNe' : afterZero ≠ 0 := by
              unfold isNontrivialProperChild at hafterZeroProper
              simp at hafterZeroProper
              exact hafterZeroProper.1.1
            have hafterZeroNotOne : afterZero ≠ 1 := by
              unfold isNontrivialProperChild at hafterZeroProper
              simp at hafterZeroProper
              exact hafterZeroProper.1.2
            exact toPoly_natDegree_pos_of_monic_ne_zero_ne_one
              hafterZeroMonic hafterZeroNe' hafterZeroNotOne
          have hpair :
              splitWork zeroPart + splitWork afterZero ≤ splitWork g' - 1 :=
            splitWork_pair_le_of_natDegree_sum_le hzeroPos hafterZeroPos hzeroAfterSum
          have hraw :
              stackWork
                  ((nontrivialProperChildren g'
                    #[zeroPart, squarePart, afterSquare]).eraseDups).toList ≤
                splitWork zeroPart + splitWork afterZero := by
            rw [hafterEq]
            unfold nontrivialProperChildren
            simpa [hproperZero, hproperSquareG, hafterZeroProper, stackWork] using
              (stackWork_eraseDups_le (#[zeroPart, afterZero] : Array (CPolynomial F)))
          exact le_trans hraw (by simpa [g'] using hpair)
    · have hafterZeroEq : afterZero = g' := by
        dsimp [afterZero, quotientAfterChild]
        rw [if_neg hproperZero]
      have hproperSquareG :
          isNontrivialProperChild g' squarePart = true :=
        middle_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
          hproperZero hsize'
      have hproperAfterG :
          isNontrivialProperChild g' afterSquare = true :=
        right_proper_of_triple_eraseDups_filter_size_ge_two_of_not_left
          hproperZero hsize'
      have hproperSquareAfter : isNontrivialProperChild afterZero squarePart = true := by
        simpa [hafterZeroEq] using hproperSquareG
      have hsquarePos : 0 < squarePart.toPoly.natDegree := by
        have hproperSquare' :
            isNontrivialProperChild g'
              (CPolynomial.monicNormalize
                (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))) = true := by
          simpa [squarePart] using hproperSquareG
        simpa [squarePart] using
          (monicNormalize_toPoly_natDegree_pos_of_proper hproperSquare')
      have hafterMonic : afterSquare.toPoly.Monic := by
        dsimp [afterSquare]
        exact quotientAfterChild_toPoly_monic_of_dvd
          (by simpa [hafterZeroEq] using hg'Monic) hdivSquare
          (by simpa [hafterZeroEq] using hg')
      have hafterPos : 0 < afterSquare.toPoly.natDegree := by
        have hafterNe : afterSquare ≠ 0 := by
          unfold isNontrivialProperChild at hproperAfterG
          simp at hproperAfterG
          exact hproperAfterG.1.1
        have hafterNotOne : afterSquare ≠ 1 := by
          unfold isNontrivialProperChild at hproperAfterG
          simp at hproperAfterG
          exact hproperAfterG.1.2
        exact toPoly_natDegree_pos_of_monic_ne_zero_ne_one
          hafterMonic hafterNe hafterNotOne
      have hsquareAfterSum :
          squarePart.toPoly.natDegree + afterSquare.toPoly.natDegree ≤
            g'.toPoly.natDegree := by
        have hsum := child_quotient_natDegree_le_parent hproperSquareAfter hdivSquare
          (by simpa [hafterZeroEq] using hg')
        simpa [hafterZeroEq, afterSquare] using hsum
      have hpair :
          splitWork squarePart + splitWork afterSquare ≤ splitWork g' - 1 :=
        splitWork_pair_le_of_natDegree_sum_le hsquarePos hafterPos hsquareAfterSum
      have hraw :
          stackWork
              ((nontrivialProperChildren g'
                #[zeroPart, squarePart, afterSquare]).eraseDups).toList ≤
            splitWork squarePart + splitWork afterSquare := by
        have herase :=
          stackWork_eraseDups_le
            (nontrivialProperChildren g' #[zeroPart, squarePart, afterSquare])
        unfold nontrivialProperChildren at herase ⊢
        simp [hproperZero, hproperSquareG, hproperAfterG, stackWork] at herase ⊢
        omega
      exact le_trans hraw (by simpa [g'] using hpair)
  next _hsize =>
    simp at htry

theorem tryOddSplitAttemptsWith_root {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} {a : F}
    (hg : g ≠ 0) (hroot : CPolynomial.eval a g = 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        ∃ child, child ∈ children.toList ∧ CPolynomial.eval a child = 0 := by
  intro attempts
  induction attempts using Nat.rec with
  | zero =>
      intro offset children htry
      cases htry
  | succ attempts ih =>
      intro offset children htry
      unfold tryOddSplitAttemptsWith at htry
      cases hsplit : cantorZassenhausOddAttemptWith M D q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausOddAttemptWith_root M D q probes hsplit hg hroot

private theorem tryOddSplitAttemptsWith_child_proper {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F} :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        child ∈ children.toList →
          isNontrivialProperChild (CPolynomial.monicNormalize g) child = true := by
  intro attempts
  induction attempts using Nat.rec with
  | zero =>
      intro offset children htry hmem
      cases htry
  | succ attempts ih =>
      intro offset children htry hmem
      unfold tryOddSplitAttemptsWith at htry
      cases hsplit : cantorZassenhausOddAttemptWith M D q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry hmem
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausOddAttemptWith_child_proper M D q probes hsplit hmem

theorem tryOddSplitAttemptsWith_child_normSplitWork_pos {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g child : CPolynomial F}
    (hg : g ≠ 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        child ∈ children.toList →
          1 ≤ normSplitWork child := by
  intro attempts
  induction attempts using Nat.rec with
  | zero =>
      intro offset children htry hmem
      cases htry
  | succ attempts ih =>
      intro offset children htry hmem
      unfold tryOddSplitAttemptsWith at htry
      cases hsplit : cantorZassenhausOddAttemptWith M D q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry hmem
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausOddAttemptWith_child_normSplitWork_pos
            M D q probes hsplit hg hmem

theorem tryOddSplitAttemptsWith_stackWork_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F}
    (hg : g ≠ 0) :
    ∀ attempts offset {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
        stackWork children.toList ≤ splitWork (CPolynomial.monicNormalize g) - 1 := by
  intro attempts
  induction attempts using Nat.rec with
  | zero =>
      intro offset children htry
      cases htry
  | succ attempts ih =>
      intro offset children htry
      unfold tryOddSplitAttemptsWith at htry
      cases hsplit : cantorZassenhausOddAttemptWith M D q probes g offset with
      | none =>
          simp [hsplit] at htry
          exact ih (offset + 1) htry
      | some splitChildren =>
          simp [hsplit] at htry
          subst children
          exact cantorZassenhausOddAttemptWith_stackWork_le M D q probes hsplit hg

end FiniteField

end Roots

end CPolynomial

end CompPoly

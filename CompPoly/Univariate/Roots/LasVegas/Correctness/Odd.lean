/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Correctness.Common
import CompPoly.Univariate.Roots.LasVegas.OddBucket

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

theorem cantorZassenhausOddAttemptWith_child_normSplitWork_pos {F : Type*}
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
theorem cantorZassenhausOddAttemptWith_stackWork_le {F : Type*}
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

set_option maxHeartbeats 1600000 in
/-- The odd split attempt depends on the probe family only through the probe
it actually draws. -/
theorem cantorZassenhausOddAttemptWith_probe_congr {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) {p1 p2 : ProbeFamily F} {g : CPolynomial F} {a1 a2 : Nat}
    (hprobe : p1.probe q (CPolynomial.monicNormalize g) a1 =
      p2.probe q (CPolynomial.monicNormalize g) a2) :
    cantorZassenhausOddAttemptWith M D q p1 g a1 =
      cantorZassenhausOddAttemptWith M D q p2 g a2 := by
  simp only [cantorZassenhausOddAttemptWith]
  rw [hprobe]

set_option maxHeartbeats 1600000 in
/-- The odd retry loop depends on the probe family only through the probes it
actually draws. -/
theorem tryOddSplitAttemptsWith_probe_congr {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) {p1 p2 : ProbeFamily F} {g : CPolynomial F} :
    ∀ (attempts offset1 offset2 : Nat),
      (∀ i, i < attempts →
        p1.probe q (CPolynomial.monicNormalize g) (offset1 + i) =
          p2.probe q (CPolynomial.monicNormalize g) (offset2 + i)) →
      tryOddSplitAttemptsWith M D q p1 g attempts offset1 =
        tryOddSplitAttemptsWith M D q p2 g attempts offset2 := by
  intro attempts
  induction attempts with
  | zero =>
      intro o1 o2 _hagree
      unfold tryOddSplitAttemptsWith
      rfl
  | succ attempts ih =>
      intro o1 o2 hagree
      unfold tryOddSplitAttemptsWith
      rw [cantorZassenhausOddAttemptWith_probe_congr M D q (g := g)
        (by simpa using hagree 0 (by omega))]
      cases htry : cantorZassenhausOddAttemptWith M D q p2 g o2 with
      | some c => simp
      | none =>
          simp only
          exact ih (o1 + 1) (o2 + 1) (by
            intro i hi
            have h := hagree (i + 1) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)

/-- A successful retry loop result is produced by some single attempt. -/
theorem tryOddSplitAttemptsWith_eq_some_exists_attempt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (probes : ProbeFamily F) {g : CPolynomial F} :
    ∀ (attempts offset : Nat) {children : Array (CPolynomial F)},
      tryOddSplitAttemptsWith M D q probes g attempts offset = some children →
      ∃ attempt, cantorZassenhausOddAttemptWith M D q probes g attempt = some children := by
  intro attempts
  induction attempts with
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
          exact ⟨offset, hsplit⟩

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

private theorem two_le_length_of_mem_of_mem_of_ne {α : Type*} {l : List α} {u v : α}
    (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) :
    2 ≤ l.length := by
  rcases l with _ | ⟨w, _ | ⟨w', t⟩⟩
  · cases hu
  · rw [List.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv
  · simp only [List.length_cons]
    omega

private theorem two_le_size_eraseDups_of_mem_of_mem_of_ne {α : Type*} [BEq α] [LawfulBEq α]
    {xs : Array α} {u v : α}
    (hu : u ∈ xs) (hv : v ∈ xs) (huv : u ≠ v) :
    2 ≤ xs.eraseDups.size := by
  have hu' : u ∈ xs.eraseDups.toList := by simpa using mem_eraseDups_of_mem hu
  have hv' : v ∈ xs.eraseDups.toList := by simpa using mem_eraseDups_of_mem hv
  simpa using two_le_length_of_mem_of_mem_of_ne hu' hv' huv

/--
Core success argument: if the probe value vanishes at the root `x` but not at
the root `y`, or the probe values at `x` and `y` are nonzero with Euler powers
one and not-one respectively, the split candidates separate `x` from `y` and
the attempt succeeds.
-/
private theorem cantorZassenhausOddAttemptWith_success_aux {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) {g h : CPolynomial F} {x y : F} (attempt : Nat)
    (hg : g ≠ 0)
    (hrootX : CPolynomial.eval x g = 0)
    (hrootY : CPolynomial.eval y g = 0)
    (hY0 : CPolynomial.eval y h ≠ 0)
    (hcase :
      CPolynomial.eval x h = 0 ∨
        (CPolynomial.eval x h ≠ 0 ∧ CPolynomial.eval x h ^ ((q - 1) / 2) = 1 ∧
          CPolynomial.eval y h ^ ((q - 1) / 2) ≠ 1)) :
    ∃ children,
      cantorZassenhausOddAttemptWith M D q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F)
        g attempt = some children := by
  cases htry : cantorZassenhausOddAttemptWith M D q
      ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F) g attempt with
  | some children => exact ⟨children, rfl⟩
  | none =>
      exfalso
      unfold cantorZassenhausOddAttemptWith at htry
      simp only at htry
      split at htry
      next hsize => simp at htry
      next hsize =>
        apply hsize
        let g' := CPolynomial.monicNormalize g
        let h' := reduceModWith D g' h
        let s := powModWith M D g' h' ((q - 1) / 2)
        let zeroPart := CPolynomial.monicNormalize (CPolynomial.gcdMonic g' h')
        let afterZero := quotientAfterChild g' zeroPart
        let squarePart := CPolynomial.monicNormalize
          (CPolynomial.gcdMonic afterZero (s - (1 : CPolynomial F)))
        let afterSquare := quotientAfterChild afterZero squarePart
        have hg' : g' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hg
        have hgMonic : g'.toPoly.Monic := monicNormalize_toPoly_monic_of_ne_zero hg
        have hX' : CPolynomial.eval x g' = 0 := (monicNormalize_root_iff hg).2 hrootX
        have hY' : CPolynomial.eval y g' = 0 := (monicNormalize_root_iff hg).2 hrootY
        have hhX : CPolynomial.eval x h' = CPolynomial.eval x h :=
          eval_reduceModWith_eq_self_of_root D hX'
        have hhY : CPolynomial.eval y h' = CPolynomial.eval y h :=
          eval_reduceModWith_eq_self_of_root D hY'
        have hsY : CPolynomial.eval y (s - 1) =
            CPolynomial.eval y h ^ ((q - 1) / 2) - 1 := by
          rw [CPolynomial.eval_sub, CPolynomial.eval_one,
            eval_powModWith_eq_pow M D hY' ((q - 1) / 2), hhY]
        have hzeroIff : ∀ z : F, CPolynomial.eval z zeroPart = 0 ↔
            CPolynomial.eval z g' = 0 ∧ CPolynomial.eval z h' = 0 :=
          fun z ↦ eval_monicNormalize_gcdMonic_eq_zero_iff g' h' z
        have hdivZero : zeroPart.toPoly ∣ g'.toPoly :=
          (toPoly_monicNormalize_dvd_self _).trans (toPoly_gcdMonic_dvd_left g' h')
        have hzeroNe : zeroPart ≠ 0 :=
          monicNormalize_ne_zero_of_ne_zero (gcdMonic_ne_zero_left h' hg')
        have hzeroMonic : zeroPart.toPoly.Monic :=
          monicNormalize_toPoly_monic_of_ne_zero (gcdMonic_ne_zero_left h' hg')
        have hzeroYne : CPolynomial.eval y zeroPart ≠ 0 := by
          intro hzy
          apply hY0
          rw [← hhY]
          exact ((hzeroIff y).1 hzy).2
        have hafterZeroY : CPolynomial.eval y afterZero = 0 :=
          quotientAfterChild_root_of_not_child_root hdivZero hY' hzeroYne
        have hafterZeroNe : afterZero ≠ 0 :=
          quotientAfterChild_ne_zero_of_dvd hdivZero hg'
        have hafterZeroDvd : afterZero.toPoly ∣ g'.toPoly :=
          quotientAfterChild_toPoly_dvd_parent hdivZero
        have hafterZeroMonic : afterZero.toPoly.Monic :=
          quotientAfterChild_toPoly_monic_of_dvd hgMonic hdivZero hg'
        have hafterZeroSizeLe : afterZero.val.size ≤ g'.val.size :=
          quotientAfterChild_size_le_parent hg'
        have hsquareIff : ∀ z : F, CPolynomial.eval z squarePart = 0 ↔
            CPolynomial.eval z afterZero = 0 ∧
              CPolynomial.eval z (s - (1 : CPolynomial F)) = 0 :=
          fun z ↦ eval_monicNormalize_gcdMonic_eq_zero_iff afterZero
            (s - (1 : CPolynomial F)) z
        have hdivSquare : squarePart.toPoly ∣ afterZero.toPoly :=
          (toPoly_monicNormalize_dvd_self _).trans
            (toPoly_gcdMonic_dvd_left afterZero (s - (1 : CPolynomial F)))
        have hsquareNe : squarePart ≠ 0 :=
          monicNormalize_ne_zero_of_ne_zero
            (gcdMonic_ne_zero_left (s - (1 : CPolynomial F)) hafterZeroNe)
        have hsquareMonic : squarePart.toPoly.Monic :=
          monicNormalize_toPoly_monic_of_ne_zero
            (gcdMonic_ne_zero_left (s - (1 : CPolynomial F)) hafterZeroNe)
        have hafterSquareNe : afterSquare ≠ 0 :=
          quotientAfterChild_ne_zero_of_dvd hdivSquare hafterZeroNe
        have hfinal : 2 ≤
            ((nontrivialProperChildren g'
              #[zeroPart, squarePart, afterSquare]).eraseDups).size := by
          rcases hcase with hX0 | ⟨hX0, hXm, hYm⟩
          · -- `x` is a root of the zero part, `y` survives into the later parts.
            have hzeroX : CPolynomial.eval x zeroPart = 0 :=
              (hzeroIff x).2 ⟨hX', by rw [hhX]; exact hX0⟩
            have hzeroSizeLt : zeroPart.val.size < g'.val.size := by
              by_contra hnot
              apply hzeroYne
              have heq : g' = zeroPart :=
                eq_of_monic_dvd_of_val_size_le hzeroMonic hgMonic hdivZero hzeroNe hg'
                  (Nat.le_of_not_lt hnot)
              rw [← heq]
              exact hY'
            have hproperZero : isNontrivialProperChild g' zeroPart = true :=
              proper_child_of_ne_zero_root_size_lt hzeroNe hzeroX hzeroSizeLt
            have hafterZeroSizeLt : afterZero.val.size < g'.val.size :=
              quotientAfterChild_size_lt_parent_of_monicNormalize_proper hg' hproperZero
            by_cases hsqY : CPolynomial.eval y squarePart = 0
            · have hsquareSizeLt : squarePart.val.size < g'.val.size := by
                have hle : squarePart.val.size ≤ afterZero.val.size :=
                  val_size_le_of_toPoly_natDegree_le hafterZeroNe
                    (Polynomial.natDegree_le_of_dvd hdivSquare
                      ((CPolynomial.toPoly_eq_zero_iff afterZero).not.mpr hafterZeroNe))
                omega
              have hproperSquare : isNontrivialProperChild g' squarePart = true :=
                proper_child_of_ne_zero_root_size_lt hsquareNe hsqY hsquareSizeLt
              have hne : zeroPart ≠ squarePart := by
                intro heq
                apply hzeroYne
                rw [heq]
                exact hsqY
              refine two_le_size_eraseDups_of_mem_of_mem_of_ne ?_ ?_ hne
              · have hmem := nontrivialProperChildren_mem_of_mem
                  (parent := g') (children := #[zeroPart, squarePart, afterSquare])
                  (by simp) hproperZero
                simpa using hmem
              · have hmem := nontrivialProperChildren_mem_of_mem
                  (parent := g') (children := #[zeroPart, squarePart, afterSquare])
                  (by simp) hproperSquare
                simpa using hmem
            · have hafterSquareY : CPolynomial.eval y afterSquare = 0 :=
                quotientAfterChild_root_of_not_child_root hdivSquare hafterZeroY hsqY
              have hafterSquareSizeLt : afterSquare.val.size < g'.val.size := by
                have hle : afterSquare.val.size ≤ afterZero.val.size :=
                  quotientAfterChild_size_le_parent hafterZeroNe
                omega
              have hproperAfter : isNontrivialProperChild g' afterSquare = true :=
                proper_child_of_ne_zero_root_size_lt hafterSquareNe hafterSquareY
                  hafterSquareSizeLt
              have hne : zeroPart ≠ afterSquare := by
                intro heq
                apply hzeroYne
                rw [heq]
                exact hafterSquareY
              refine two_le_size_eraseDups_of_mem_of_mem_of_ne ?_ ?_ hne
              · have hmem := nontrivialProperChildren_mem_of_mem
                  (parent := g') (children := #[zeroPart, squarePart, afterSquare])
                  (by simp) hproperZero
                simpa using hmem
              · have hmem := nontrivialProperChildren_mem_of_mem
                  (parent := g') (children := #[zeroPart, squarePart, afterSquare])
                  (by simp) hproperAfter
                simpa using hmem
          · -- `x` lands in the square part, `y` in the remaining quotient.
            have hzeroXne : CPolynomial.eval x zeroPart ≠ 0 := by
              intro hzx
              apply hX0
              rw [← hhX]
              exact ((hzeroIff x).1 hzx).2
            have hafterZeroX : CPolynomial.eval x afterZero = 0 :=
              quotientAfterChild_root_of_not_child_root hdivZero hX' hzeroXne
            have hsX : CPolynomial.eval x (s - 1) = 0 := by
              rw [CPolynomial.eval_sub, CPolynomial.eval_one,
                eval_powModWith_eq_pow M D hX' ((q - 1) / 2), hhX, hXm, sub_self]
            have hsquareX : CPolynomial.eval x squarePart = 0 :=
              (hsquareIff x).2 ⟨hafterZeroX, hsX⟩
            have hsquareYne : CPolynomial.eval y squarePart ≠ 0 := by
              intro hsy
              apply hYm
              have hy1 := ((hsquareIff y).1 hsy).2
              rw [hsY] at hy1
              exact sub_eq_zero.mp hy1
            have hsquareSizeLt : squarePart.val.size < g'.val.size := by
              by_contra hnot
              apply hsquareYne
              have heq : g' = squarePart :=
                eq_of_monic_dvd_of_val_size_le hsquareMonic hgMonic
                  (hdivSquare.trans hafterZeroDvd) hsquareNe hg' (Nat.le_of_not_lt hnot)
              rw [← heq]
              exact hY'
            have hproperSquare : isNontrivialProperChild g' squarePart = true :=
              proper_child_of_ne_zero_root_size_lt hsquareNe hsquareX hsquareSizeLt
            have hafterSquareY : CPolynomial.eval y afterSquare = 0 :=
              quotientAfterChild_root_of_not_child_root hdivSquare hafterZeroY hsquareYne
            have hproperSqAfterZero : isNontrivialProperChild afterZero squarePart = true := by
              by_contra hnot
              apply hsquareYne
              have heq : afterZero = squarePart :=
                eq_of_not_proper_of_monic_dvd hsquareMonic hafterZeroMonic hdivSquare
                  hsquareNe hafterZeroNe (child_ne_one_of_root hsquareX) hnot
              rw [← heq]
              exact hafterZeroY
            have hafterSquareSizeLt : afterSquare.val.size < g'.val.size := by
              have hlt : afterSquare.val.size < afterZero.val.size :=
                quotientAfterChild_size_lt_parent_of_monicNormalize_proper hafterZeroNe
                  hproperSqAfterZero
              omega
            have hproperAfter : isNontrivialProperChild g' afterSquare = true :=
              proper_child_of_ne_zero_root_size_lt hafterSquareNe hafterSquareY
                hafterSquareSizeLt
            have hne : squarePart ≠ afterSquare := by
              intro heq
              apply hsquareYne
              rw [heq]
              exact hafterSquareY
            refine two_le_size_eraseDups_of_mem_of_mem_of_ne ?_ ?_ hne
            · have hmem := nontrivialProperChildren_mem_of_mem
                (parent := g') (children := #[zeroPart, squarePart, afterSquare])
                (by simp) hproperSquare
              simpa using hmem
            · have hmem := nontrivialProperChildren_mem_of_mem
                (parent := g') (children := #[zeroPart, squarePart, afterSquare])
                (by simp) hproperAfter
              simpa using hmem
        simpa [g', h', s, zeroPart, afterZero, squarePart, afterSquare] using hfinal

/--
A fixed probe whose Euler buckets separate two distinct roots of `g` forces the
odd Cantor-Zassenhaus split attempt to succeed.

The split candidates of `cantorZassenhausOddAttemptWith` are the zero part
`gcd(g, h)`, the square part `gcd(g / zeroPart, h ^ ((q - 1) / 2) - 1)`, and
the remaining quotient. Roots in the `zero`, `square`, and `nonsquare` Euler
buckets of the probe land in these three candidates respectively, so two roots
in different buckets witness two distinct nontrivial proper children.

The hypothesis `hg : g ≠ 0` is essential: for `g = 0` both root hypotheses hold
vacuously while the attempt always fails, because no candidate child can have
representation size strictly below the parent size `0`. No distinctness
hypothesis on `a` and `b` is needed: bucket separation already forces `a ≠ b`.
-/
theorem cantorZassenhausOddAttemptWith_success_of_bucket_separated {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) {g h : CPolynomial F} {a b : F} (attempt : Nat)
    (hg : g ≠ 0)
    (hrootA : CPolynomial.eval a g = 0)
    (hrootB : CPolynomial.eval b g = 0)
    (hsep :
      oddCZBucket q (CPolynomial.eval a h) ≠
        oddCZBucket q (CPolynomial.eval b h)) :
    ∃ children,
      cantorZassenhausOddAttemptWith M D q
        ({ probe := fun _q _factor _attempt ↦ h } : ProbeFamily F)
        g attempt = some children := by
  cases hbA : oddCZBucket q (CPolynomial.eval a h) with
  | zero =>
      have hA := (oddCZBucket_eq_zero_iff q (CPolynomial.eval a h)).1 hbA
      cases hbB : oddCZBucket q (CPolynomial.eval b h) with
      | zero => exact absurd (hbA.trans hbB.symm) hsep
      | square =>
          have hB := (oddCZBucket_eq_square_iff q (CPolynomial.eval b h)).1 hbB
          exact cantorZassenhausOddAttemptWith_success_aux M D q attempt hg hrootA hrootB
            hB.1 (Or.inl hA)
      | nonsquare =>
          have hB := (oddCZBucket_eq_nonsquare_iff q (CPolynomial.eval b h)).1 hbB
          exact cantorZassenhausOddAttemptWith_success_aux M D q attempt hg hrootA hrootB
            hB.1 (Or.inl hA)
  | square =>
      have hA := (oddCZBucket_eq_square_iff q (CPolynomial.eval a h)).1 hbA
      cases hbB : oddCZBucket q (CPolynomial.eval b h) with
      | zero =>
          have hB := (oddCZBucket_eq_zero_iff q (CPolynomial.eval b h)).1 hbB
          exact cantorZassenhausOddAttemptWith_success_aux M D q attempt hg hrootB hrootA
            hA.1 (Or.inl hB)
      | square => exact absurd (hbA.trans hbB.symm) hsep
      | nonsquare =>
          have hB := (oddCZBucket_eq_nonsquare_iff q (CPolynomial.eval b h)).1 hbB
          exact cantorZassenhausOddAttemptWith_success_aux M D q attempt hg hrootA hrootB
            hB.1 (Or.inr ⟨hA.1, hA.2, hB.2⟩)
  | nonsquare =>
      have hA := (oddCZBucket_eq_nonsquare_iff q (CPolynomial.eval a h)).1 hbA
      cases hbB : oddCZBucket q (CPolynomial.eval b h) with
      | zero =>
          have hB := (oddCZBucket_eq_zero_iff q (CPolynomial.eval b h)).1 hbB
          exact cantorZassenhausOddAttemptWith_success_aux M D q attempt hg hrootB hrootA
            hA.1 (Or.inl hB)
      | square =>
          have hB := (oddCZBucket_eq_square_iff q (CPolynomial.eval b h)).1 hbB
          exact cantorZassenhausOddAttemptWith_success_aux M D q attempt hg hrootB hrootA
            hA.1 (Or.inr ⟨hB.1, hB.2, hA.2⟩)
      | nonsquare => exact absurd (hbA.trans hbB.symm) hsep

end FiniteField

end Roots

end CPolynomial

end CompPoly

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Completeness

/-!
# Diagonal Modular Equation Solver Context

Umbrella module for the diagonal modular-equation solver: definitions,
soundness, the completeness development, and the production
`ModularSolutionBasisContext` instance backed by the X-adic PM-basis.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Diagonal modular-equation solution-basis context obtained from the
exact-nullspace lift and an X-adic PM-basis context. -/
def modularSolutionBasisContextViaPMBasis
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) : ModularSolutionBasisContext F where
  mulContext := mulCtx
  modContext := modCtx
  solutionBasis := filteredSolutionBasisViaPMBasis mulCtx modCtx pmCtx
  sound := by
    intro equation shift row hrow
    exact filteredSolutionBasisViaPMBasis_sound hrow
  complete_minimal := by
    -- Certified verification window: solutions at or above the best adaptive
    -- degree are dominated by the adaptive rows of `combined`; solutions
    -- strictly below it (or with no adaptive row at all) are dominated by a
    -- verification row through `me_verification_dominates`, with the fallback
    -- solution `e_p * prod(moduli)` covering degrees beyond the saturated
    -- window.
    intro equation shift row hmonic hcols hshift hsat hnz hwidth
    classical
    obtain ⟨d, hd⟩ := me_rowShiftedDegree_isSome (shift := shift) hnz
    obtain ⟨j0, hj0, hj0ne⟩ := exists_nonzero_entry_of_rowIsZero_false hnz
    have hpos : 0 < equation.solutionWidth := by omega
    -- Main existence in the combined candidate set.
    have hmain : ∃ basisRow degree,
        basisRow ∈ MatrixRows
          ((adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift).filtered ++
            filterModularSolutionRows mulCtx modCtx equation
              (verificationSolutionBasisViaPMBasis modCtx pmCtx equation shift
                (leastSolutionRowDegree?
                  (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                    shift).filtered shift))) ∧
        rowShiftedDegree? basisRow shift = some degree ∧ degree ≤ d := by
      by_cases hcase : ∃ B, leastSolutionRowDegree?
          (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift).filtered
          shift = some B ∧ B ≤ d
      · -- An adaptive row already dominates.
        obtain ⟨B, hB, hBd⟩ := hcase
        rw [leastSolutionRowDegree?] at hB
        rcases Option.map_eq_some_iff.mp hB with ⟨choice, hchoice, hchoicedeg⟩
        obtain ⟨hidx, hrowEq, hcdeg⟩ := leastShiftedDegreeChoice?_some_valid hchoice
        refine ⟨choice.row, choice.degree, ?_, hcdeg, by omega⟩
        rw [MatrixRows, Array.toList_append]
        refine List.mem_append.mpr (Or.inl ?_)
        rw [hrowEq]
        exact me_getD_mem_toList #[] hidx
      · -- Route through the certified verification window.
        push Not at hcase
        have hwindow : ∃ (rowStar : PolynomialRow F) (e : Nat),
            rowSatisfiesModularBool mulCtx modCtx rowStar equation.matrix
              equation.moduli = true ∧
            rowIsZero rowStar = false ∧
            rowStar.size ≤ equation.solutionWidth ∧
            rowShiftedDegree? rowStar shift = some e ∧
            e ≤ verificationWindowBound equation shift
              (leastSolutionRowDegree?
                (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                  shift).filtered shift) ∧
            e ≤ d := by
          by_cases hdbound : d ≤ verificationWindowBound equation shift
              (leastSolutionRowDegree?
                (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                  shift).filtered shift)
          · exact ⟨row, d, hsat, hnz, hwidth, hd, hdbound, le_refl d⟩
          · -- The window is saturated at the full pivot window.
            have hfull : verificationWindowBound equation shift
                (leastSolutionRowDegree?
                  (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                    shift).filtered shift) =
                pivotWindowCap equation + maxShiftDegree shift := by
              cases hbest : leastSolutionRowDegree?
                  (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                    shift).filtered shift with
              | none =>
                  simp [verificationWindowBound, fullWindowDegreeBound]
              | some B =>
                  have hdB : d < B := hcase B hbest
                  rw [hbest] at hdbound
                  simp only [verificationWindowBound] at hdbound ⊢
                  omega
            obtain ⟨prow, e, hsatP, hnzP, hsizeP, hdegP, heP⟩ :=
              me_prodRow_facts mulCtx modCtx equation shift (p := j0) hmonic
                hcols (by omega)
            exact ⟨prow, e, hsatP, hnzP, le_of_eq hsizeP, hdegP, by omega,
              by omega⟩
        obtain ⟨rowStar, e, hsatS, hnzS, hwidthS, hdegS, heB, heD⟩ := hwindow
        obtain ⟨bRow, degB, hmem, hdegB, hle⟩ := me_verification_dominates
          mulCtx modCtx pmCtx equation shift
          (verificationWindowBound equation shift
            (leastSolutionRowDegree?
              (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                shift).filtered shift))
          hmonic hcols hshift hpos hsatS hnzS hwidthS hdegS heB
        refine ⟨bRow, degB, ?_, hdegB, by omega⟩
        rw [MatrixRows, Array.toList_append]
        refine List.mem_append.mpr (Or.inr ?_)
        exact hmem
    obtain ⟨bRow, degB, hmemC, hdegB, hled⟩ := hmain
    -- The combined candidate set is nonempty, so the repair branch is skipped.
    have hsizepos : 0 <
        ((adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift).filtered ++
          filterModularSolutionRows mulCtx modCtx equation
            (verificationSolutionBasisViaPMBasis modCtx pmCtx equation shift
              (leastSolutionRowDegree?
                (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                  shift).filtered shift))).size := by
      rcases List.getElem_of_mem hmemC with ⟨i, hi, _⟩
      rw [MatrixRows, Array.length_toList] at hi
      omega
    have hresult : filteredSolutionBasisViaPMBasis mulCtx modCtx pmCtx equation
        shift =
        (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift).filtered ++
          filterModularSolutionRows mulCtx modCtx equation
            (verificationSolutionBasisViaPMBasis modCtx pmCtx equation shift
              (leastSolutionRowDegree?
                (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                  shift).filtered shift)) := by
      simp only [filteredSolutionBasisViaPMBasis]
      rw [if_neg (by simp only [beq_iff_eq]; omega)]
    constructor
    · -- Width discipline of the returned rows.
      intro basisRow hbasisRow
      rw [hresult, MatrixRows, Array.toList_append, List.mem_append] at hbasisRow
      rcases hbasisRow with h | h
      · exact le_of_eq (me_adaptiveBasis_width basisRow h)
      · have hsub := me_filterModularSolutionRows_subset h
        have hsub' : basisRow ∈ MatrixRows (compactNonzeroRows
            (principalSolutionRows equation.solutionWidth
              (pmCtx.basis
                (fullWindowExactNullspaceProblem modCtx equation
                  (verificationWindowBound equation shift
                    (leastSolutionRowDegree?
                      (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                        shift).filtered shift)))
                (exactNullspaceShift shift equation.modularWidth
                  (verificationWindowBound equation shift
                    (leastSolutionRowDegree?
                      (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                        shift).filtered shift)))))) := hsub
        exact le_of_eq
          (me_principalSolutionRows_width (compactNonzeroRows_subset hsub'))
    · refine ⟨bRow, degB, ?_, hdegB, ?_⟩
      · rw [hresult]
        exact hmemC
      · intro rowDegree hrowDegree
        rw [hd] at hrowDegree
        have hEq := Option.some.inj hrowDegree
        omega

end Approximant

end PolynomialMatrix

end CompPoly

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
    intro equation shift degreeBound? row hrow
    exact filteredSolutionBasisViaPMBasis_sound hrow
  complete_minimal := by
    -- With the degree gate passed, the adaptive best itself meets the bound,
    -- so the adaptive candidate set suffices.  Otherwise the certified gated
    -- window takes over: solutions at or above the best adaptive degree are
    -- dominated by the adaptive rows of `combined`; solutions inside the
    -- window are dominated by a verification row through
    -- `me_verification_dominates`, with the fallback solution
    -- `e_p * prod(moduli)` covering degrees beyond the saturated window.
    intro equation shift degreeBound? row d hmonic hcols hshift hsat hnz hwidth
      hd hdbound
    classical
    obtain ⟨j0, hj0, hj0ne⟩ := exists_nonzero_entry_of_rowIsZero_false hnz
    have hpos : 0 < equation.solutionWidth := by omega
    cases hgate : degreeGatePassed degreeBound?
        (leastSolutionRowDegree?
          (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?).filtered
          shift) with
    | true =>
        -- Gate passed: the adaptive candidate set is returned, and its least
        -- row meets the caller's bound.
        obtain ⟨bound, best, hBound, hBest, hle⟩ :=
          degreeGatePassed_eq_true_iff.mp hgate
        have hresult : filteredSolutionBasisViaPMBasis mulCtx modCtx pmCtx
            equation shift degreeBound? =
            (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?).filtered := by
          simp only [filteredSolutionBasisViaPMBasis]
          rw [if_pos hgate]
        rw [leastSolutionRowDegree?] at hBest
        rcases Option.map_eq_some_iff.mp hBest with ⟨choice, hchoice, hchoicedeg⟩
        obtain ⟨hidx, hrowEq, hcdeg⟩ := leastShiftedDegreeChoice?_some_valid hchoice
        refine ⟨?_, choice.row, choice.degree, ?_, hcdeg, ?_⟩
        · intro basisRow hbasisRow
          rw [hresult] at hbasisRow
          exact le_of_eq (me_adaptiveBasis_width basisRow hbasisRow)
        · rw [hresult, MatrixRows, hrowEq]
          exact me_getD_mem_toList #[] hidx
        · rw [hBound, Option.getD_some]
          omega
    | false =>
        -- Gate failed or no bound supplied: the certified union is returned.
        have hmain : ∃ basisRow degree,
            basisRow ∈ MatrixRows
              ((adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?).filtered ++
                filterModularSolutionRows mulCtx modCtx equation
                  (windowedSolutionBasisViaPMBasis modCtx pmCtx equation shift
                    (gatedWindowBound equation shift degreeBound?
                      (leastSolutionRowDegree?
                        (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                          shift degreeBound?).filtered shift)))) ∧
            rowShiftedDegree? basisRow shift = some degree ∧
            degree ≤ degreeBound?.getD d := by
          cases hbnd : degreeBound? with
          | some bound =>
              -- Bounded window `min(bound, cap) + maxShift`.
              have hdb : d ≤ bound := hdbound bound hbnd
              simp only [gatedWindowBound, Option.getD_some]
              by_cases hdw : d ≤
                  min bound (pivotWindowCap equation) + maxShiftDegree shift
              · -- The solution row itself fits the gated window.
                obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := me_verification_dominates
                  mulCtx modCtx pmCtx equation shift
                  (min bound (pivotWindowCap equation) + maxShiftDegree shift)
                  hmonic hcols hshift hpos hsat hnz hwidth hd hdw
                refine ⟨bRow, degB, ?_, hdegB, by omega⟩
                rw [MatrixRows, Array.toList_append]
                exact List.mem_append.mpr (Or.inr hmem)
              · -- Beyond the window the bound forces saturation at the full
                -- pivot window, where the fallback row dominates.
                obtain ⟨prow, e, hsatP, hnzP, hsizeP, hdegP, heP⟩ :=
                  me_prodRow_facts mulCtx modCtx equation shift (p := j0) hmonic
                    hcols (by omega)
                obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := me_verification_dominates
                  mulCtx modCtx pmCtx equation shift
                  (min bound (pivotWindowCap equation) + maxShiftDegree shift)
                  hmonic hcols hshift hpos hsatP hnzP (le_of_eq hsizeP) hdegP
                  (by omega)
                refine ⟨bRow, degB, ?_, hdegB, by omega⟩
                rw [MatrixRows, Array.toList_append]
                exact List.mem_append.mpr (Or.inr hmem)
          | none =>
              simp only [gatedWindowBound, Option.getD_none]
              by_cases hcase : ∃ B, leastSolutionRowDegree?
                  (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift none).filtered
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
                          shift none).filtered shift) ∧
                    e ≤ d := by
                  by_cases hdwindow : d ≤ verificationWindowBound equation shift
                      (leastSolutionRowDegree?
                        (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                          shift none).filtered shift)
                  · exact ⟨row, d, hsat, hnz, hwidth, hd, hdwindow, le_refl d⟩
                  · -- The window is saturated at the full pivot window.
                    have hfull : verificationWindowBound equation shift
                        (leastSolutionRowDegree?
                          (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                            shift none).filtered shift) =
                        pivotWindowCap equation + maxShiftDegree shift := by
                      cases hbest : leastSolutionRowDegree?
                          (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                            shift none).filtered shift with
                      | none =>
                          simp [verificationWindowBound, fullWindowDegreeBound]
                      | some B =>
                          have hdB : d < B := hcase B hbest
                          rw [hbest] at hdwindow
                          simp only [verificationWindowBound] at hdwindow ⊢
                          omega
                    obtain ⟨prow, e, hsatP, hnzP, hsizeP, hdegP, heP⟩ :=
                      me_prodRow_facts mulCtx modCtx equation shift (p := j0) hmonic
                        hcols (by omega)
                    exact ⟨prow, e, hsatP, hnzP, le_of_eq hsizeP, hdegP, by omega,
                      by omega⟩
                obtain ⟨rowStar, e, hsatS, hnzS, hwidthS, hdegS, heB, heD⟩ := hwindow
                obtain ⟨bRow, degB, hmem, hdegB, hleB⟩ := me_verification_dominates
                  mulCtx modCtx pmCtx equation shift
                  (verificationWindowBound equation shift
                    (leastSolutionRowDegree?
                      (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                        shift none).filtered shift))
                  hmonic hcols hshift hpos hsatS hnzS hwidthS hdegS heB
                refine ⟨bRow, degB, ?_, hdegB, by omega⟩
                rw [MatrixRows, Array.toList_append]
                refine List.mem_append.mpr (Or.inr ?_)
                exact hmem
        obtain ⟨bRow, degB, hmemC, hdegB, hled⟩ := hmain
        -- The combined candidate set is nonempty, so the repair branch is
        -- skipped.
        have hsizepos : 0 <
            ((adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?).filtered ++
              filterModularSolutionRows mulCtx modCtx equation
                (windowedSolutionBasisViaPMBasis modCtx pmCtx equation shift
                  (gatedWindowBound equation shift degreeBound?
                    (leastSolutionRowDegree?
                      (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                        shift degreeBound?).filtered shift)))).size := by
          rcases List.getElem_of_mem hmemC with ⟨i, hi, _⟩
          rw [MatrixRows, Array.length_toList] at hi
          omega
        have hresult : filteredSolutionBasisViaPMBasis mulCtx modCtx pmCtx equation
            shift degreeBound? =
            (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift degreeBound?).filtered ++
              filterModularSolutionRows mulCtx modCtx equation
                (windowedSolutionBasisViaPMBasis modCtx pmCtx equation shift
                  (gatedWindowBound equation shift degreeBound?
                    (leastSolutionRowDegree?
                      (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                        shift degreeBound?).filtered shift))) := by
          simp only [filteredSolutionBasisViaPMBasis]
          rw [hgate]
          simp only [Bool.false_eq_true, if_false]
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
                      (gatedWindowBound equation shift degreeBound?
                        (leastSolutionRowDegree?
                          (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                            shift degreeBound?).filtered shift)))
                    (exactNullspaceShift shift equation.modularWidth
                      (gatedWindowBound equation shift degreeBound?
                        (leastSolutionRowDegree?
                          (adaptiveSolutionBasis mulCtx modCtx pmCtx equation
                            shift degreeBound?).filtered shift)))))) := hsub
            exact le_of_eq
              (me_principalSolutionRows_width (compactNonzeroRows_subset hsub'))
        · refine ⟨bRow, degB, ?_, hdegB, hled⟩
          rw [hresult]
          exact hmemC

end Approximant

end PolynomialMatrix

end CompPoly

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.BatchEval.Correctness
import CompPoly.Univariate.Raw.Modular
import CompPoly.Univariate.Roots.Context
import Mathlib.GroupTheory.OrderOfElement

/-!
# Smooth Multiplicative-Subgroup Linear-Factor Splitting

Executable splitter for field-root products over finite fields whose
multiplicative group admits a smooth cyclic refinement schedule.

The generic root pipeline still sees only a `LinearFactorProductSplitter`. This
module provides a contract-bearing smooth context plus an adapter from that
context to the shared splitter interface.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Contract wrapper for batch evaluation backends used at smooth-splitter leaves. -/
structure BatchEvalContext (F : Type*) [Semiring F] where
  evalBatchWith : CPolynomial F → Array F → Array F
  correct : ∀ p xs, evalBatchWith p xs = CPolynomial.evalBatch p xs

namespace BatchEvalContext

/-- Horner-backed batch evaluation context. -/
def horner (F : Type*) [Semiring F] : BatchEvalContext F where
  evalBatchWith := CPolynomial.evalBatchHorner
  correct := by
    intro p xs
    exact CPolynomial.evalBatchHorner_eq_evalBatch p xs

/-- Subproduct-tree-backed batch evaluation context. -/
def subproduct (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F) :
    BatchEvalContext F where
  evalBatchWith := CPolynomial.evalBatchSubproduct M D
  correct := by
    intro p xs
    exact CPolynomial.evalBatchSubproduct_eq_evalBatch M D p xs

end BatchEvalContext

/--
Splitter-input predicate for a smooth cyclic splitter.

This is intentionally a mathematical contract, not an executable guard. The
field-root pipeline is expected to prove it for `gcd(p, X^q - X)` values before
using the splitter completeness theorem.
-/
def smoothSplitterInput {F : Type*} [Field F]
    (q : Nat) (_generator : F) (_schedule : Array Nat) (p : CPolynomial F) : Prop :=
  p ≠ 0 ∧ ∀ a : F, CPolynomial.eval a p = 0 → a ^ q = a

/-- Package the executable smooth splitter with its field and schedule facts. -/
structure SmoothCyclicRootContext (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  q : Nat
  generator : F
  schedule : Array Nat
  leafEvaluator : BatchEvalContext F
  validInput : CPolynomial F → Prop
  card_eq : Nat.card F = q
  generator_order : orderOf generator = q - 1
  schedule_complete :
    schedule.toList.foldl (fun order ell => order / ell) (q - 1) = 1
  splitLinearFactorsWith :
    CPolynomial.Raw.MulContext F →
      CPolynomial.Raw.ModContext F →
        CPolynomial F → Array (CPolynomial F)
  sound :
    ∀ M D p factor,
      factor ∈ (splitLinearFactorsWith M D p).toList →
        IsLinearFactor factor
  complete :
    ∀ M D p a,
      validInput p →
        p ≠ 0 →
          CPolynomial.eval a p = 0 →
            ∃ factor,
              factor ∈ (splitLinearFactorsWith M D p).toList ∧
                IsLinearRootFactorCandidate factor a

/-- Boolean recognizer for represented nonconstant linear factors. -/
def isRepresentedLinearFactor {F : Type*} [Field F] [BEq F]
    (p : CPolynomial F) : Bool :=
  decide (p.val.size ≤ 2) && !(p.coeff 1 == 0)

/-- Return `p` as a singleton array if it is represented as a nonconstant linear factor. -/
def representedLinearFactorArray {F : Type*} [Field F] [BEq F]
    (p : CPolynomial F) : Array (CPolynomial F) :=
  if isRepresentedLinearFactor p then #[p] else #[]

/-- `X^exponent mod modulus`, lifted back to canonical polynomials. -/
def xPowModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus : CPolynomial F) (exponent : Nat) : CPolynomial F :=
  CPolynomial.ofArray
    (CPolynomial.Raw.powModWith M D modulus.val
      (CPolynomial.Raw.X : CPolynomial.Raw F) exponent)

/-- Ordered elements of the coset `alpha * <gamma>` with the supplied order. -/
def smoothCosetPoints {F : Type*} [Field F]
    (alpha gamma : F) (order : Nat) : Array F :=
  Array.ofFn fun j : Fin order => alpha * gamma ^ j.val

/-- Emit linear factors for the points whose evaluated value is zero. -/
def linearFactorsFromLeafValues {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (points values : Array F) : Array (CPolynomial F) :=
  points.zipIdx.foldl
    (fun factors ⟨point, idx⟩ =>
      if values.getD idx 1 == 0 then
        factors.push (CPolynomial.linearFactor point)
      else
        factors)
    #[]

/-- Leaf extraction by evaluating all elements of the current coset. -/
def smoothLeafLinearFactors {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (E : BatchEvalContext F) (alpha gamma : F) (order : Nat)
    (p : CPolynomial F) : Array (CPolynomial F) :=
  let points := smoothCosetPoints alpha gamma order
  linearFactorsFromLeafValues points (E.evalBatchWith p points)

/-- Schedule-driven nonzero-root refinement inside one multiplicative coset. -/
def smoothCosetLinearFactorsWithSchedule {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (E : BatchEvalContext F) :
    List Nat → Nat → F → F → CPolynomial F → Array (CPolynomial F)
  | [], order, alpha, gamma, p =>
      let p := CPolynomial.monicNormalize p
      if p == 0 || p == 1 then
        #[]
      else if isRepresentedLinearFactor p then
        #[p]
      else
        smoothLeafLinearFactors E alpha gamma order p
  | ell :: rest, order, alpha, gamma, p =>
      let p := CPolynomial.monicNormalize p
      if p == 0 || p == 1 then
        #[]
      else if isRepresentedLinearFactor p then
        #[p]
      else if ell ≤ 1 then
        smoothCosetLinearFactorsWithSchedule M D E rest order alpha gamma p
      else if ell = order then
        smoothLeafLinearFactors E alpha gamma order p
      else
        let childOrder := order / ell
        let tau := gamma ^ childOrder
        let xPow := xPowModWith M D p childOrder
        (List.range ell).foldl
          (fun factors j =>
            let beta := alpha ^ childOrder * tau ^ j
            let witness := xPow - CPolynomial.C beta
            let child := CPolynomial.monicNormalize (CPolynomial.gcdMonic p witness)
            if child == 0 || child == 1 then
              factors
            else
              factors ++
                smoothCosetLinearFactorsWithSchedule M D E rest childOrder
                  (alpha * gamma ^ j) (gamma ^ ell) child)
          #[]

/-- Nonzero root extraction by smooth multiplicative-subgroup refinement. -/
def smoothNonzeroLinearFactorsWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (E : BatchEvalContext F) (q : Nat) (generator : F) (schedule : Array Nat)
    (p : CPolynomial F) : Array (CPolynomial F) :=
  smoothCosetLinearFactorsWithSchedule M D E schedule.toList (q - 1)
    (1 : F) generator p

/-- Smooth linear-factor splitting algorithm, including separate handling of root `0`. -/
def smoothLinearFactorsAlgorithmWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (E : BatchEvalContext F) (q : Nat) (generator : F) (schedule : Array Nat)
    (p : CPolynomial F) : Array (CPolynomial F) :=
  let p := CPolynomial.monicNormalize p
  if p == 0 || p == 1 then
    #[]
  else
    let zeroSplit : Array (CPolynomial F) × CPolynomial F :=
      if p.coeff 0 == 0 then
        (#[CPolynomial.linearFactor (0 : F)], CPolynomial.monicNormalize (CPolynomial.divX p))
      else
        (#[], p)
    zeroSplit.1 ++
      smoothNonzeroLinearFactorsWith M D E q generator schedule zeroSplit.2

/-- Build a smooth cyclic root context from executable constants and proof fields. -/
def smoothCyclicRootContextOf {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (q : Nat) (generator : F) (schedule : Array Nat)
    (leafEvaluator : BatchEvalContext F)
    (validInput : CPolynomial F → Prop)
    (card_eq : Nat.card F = q)
    (generator_order : orderOf generator = q - 1)
    (schedule_complete :
      schedule.toList.foldl (fun order ell => order / ell) (q - 1) = 1)
    (sound :
      ∀ M D p factor,
        factor ∈
            (smoothLinearFactorsAlgorithmWith M D leafEvaluator q generator schedule p).toList →
          IsLinearFactor factor)
    (complete :
      ∀ M D p a,
        validInput p →
          p ≠ 0 →
            CPolynomial.eval a p = 0 →
              ∃ factor,
                factor ∈
                    (smoothLinearFactorsAlgorithmWith M D leafEvaluator q generator schedule p).toList ∧
                  IsLinearRootFactorCandidate factor a) :
    SmoothCyclicRootContext F where
  q := q
  generator := generator
  schedule := schedule
  leafEvaluator := leafEvaluator
  validInput := validInput
  card_eq := card_eq
  generator_order := generator_order
  schedule_complete := schedule_complete
  splitLinearFactorsWith := fun M D =>
    smoothLinearFactorsAlgorithmWith M D leafEvaluator q generator schedule
  sound := sound
  complete := complete

/-- Adapt a smooth cyclic context to the generic splitter interface. -/
def smoothLinearFactorProductSplitterWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmoothCyclicRootContext F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := fun _qArg p => ctx.splitLinearFactorsWith M D p
  validInput := fun _qArg p => ctx.validInput p
  sound := by
    intro _qArg p factor h
    exact ctx.sound M D p factor h
  complete := by
    intro _qArg p a hvalid hp hroot
    exact ctx.complete M D p a hvalid hp hroot

end FiniteField

end Roots

end CPolynomial

end CompPoly

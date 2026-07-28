/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_64.Primitive
import CompPoly.Fields.Binary.Extension.Enumeration
import CompPoly.Univariate.Roots.Context
import CompPoly.Univariate.Roots.LasVegas.Basic
import CompPoly.Univariate.Roots.Shoup.Basic
import CompPoly.Univariate.Roots.SmoothSubgroup
import Mathlib.FieldTheory.Finite.Trace

/-!
# GF(2^64) Root-Search Contexts

Certified finite-field context for the executable `GF(2^64)` carrier.
-/

namespace GF2_64

open CompPoly
open CompPoly.CPolynomial.Roots.FiniteField

private theorem exists_basis_trace_ne {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (b : Module.Basis ι K L) {x : L} (hx : x ≠ 0) :
    ∃ i, Algebra.trace K L (b i * x) ≠ 0 := by
  have hnd := (traceForm_nondegenerate K L).1 x
  by_contra hnone
  push Not at hnone
  have hzero : (Algebra.traceForm K L) x = 0 := by
    apply b.ext
    intro i
    rw [Algebra.traceForm_apply]
    simpa [mul_comm] using hnone i
  exact hx (hnd (by
    intro y
    rw [hzero]
    rfl))

/-- Finite-field context for the executable `GF(2^64)` carrier. -/
def finiteFieldContext :
    CompPoly.CPolynomial.Roots.FiniteField.FiniteFieldContext ConcreteField where
  q := fieldSize
  finite := by infer_instance
  card_eq := by
    rw [Nat.card_eq_fintype_card]
    exact ConcreteField.card
  frobenius_fixed := by
    intro a
    have hcard : Fintype.card ConcreteField = fieldSize := by
      exact ConcreteField.card
    simpa [hcard] using FiniteField.pow_card a

/-- Lazy complete enumeration for `GF(2^64)`. -/
def fieldEnumeration :
    CompPoly.CPolynomial.Roots.FiniteField.FieldEnumeration ConcreteField :=
  BinaryField.Extension.Concrete.fieldEnumeration Concrete.params

namespace ConcreteField

local instance fieldInst : Field ConcreteField :=
  instFieldConcreteField

local instance commRingInst : CommRing ConcreteField :=
  fieldInst.toCommRing

noncomputable local instance algebraInst : Algebra (ZMod 2) ConcreteField :=
  instAlgebraConcreteField

/-- Algebraic trace value embedded back into executable `GF(2^64)`. -/
noncomputable def algebraicTraceValue (z : ConcreteField) : ConcreteField :=
  algebraMap (ZMod 2) ConcreteField (Algebra.trace (ZMod 2) ConcreteField z)

/-- The executable GF64 carrier has dimension `64` over `GF(2)`. -/
theorem finrank_eq_extensionDegree :
    Module.finrank (ZMod 2) ConcreteField = extensionDegree := by
  have h := FiniteField.pow_finrank_eq_card (p := 2) (k := ConcreteField)
  rw [card] at h
  exact Nat.pow_right_injective (by norm_num : 1 < 2) h

/-- The algebraic trace equals the Shoup Frobenius power sum. -/
theorem algebraicTraceValue_eq_powerSum (z : ConcreteField) :
    algebraicTraceValue z = tracePowerSum 2 extensionDegree z := by
  unfold algebraicTraceValue
  have htrace := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) ConcreteField z
  rw [finrank_eq_extensionDegree] at htrace
  rw [htrace]
  rw [tracePowerSum_eq_sum_range]
  simp

/-- The GF64 trace lands in the embedded `GF(2)` constants. -/
theorem algebraicTraceValue_mem_base (z : ConcreteField) :
    algebraicTraceValue z ∈ baseConstants.toList := by
  unfold algebraicTraceValue baseConstants BinaryField.Extension.Concrete.baseConstants
  let t : ZMod 2 := Algebra.trace (ZMod 2) ConcreteField z
  change algebraMap (ZMod 2) ConcreteField t ∈
    [BinaryField.Extension.Concrete.zero Concrete.params,
      BinaryField.Extension.Concrete.one Concrete.params]
  have ht : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by
    intro u
    fin_cases u
    · left
      rfl
    · right
      rfl
  rcases ht t with ht0 | ht1
  · rw [ht0, map_zero]
    left
  · rw [ht1, map_one]
    right
    left

/-- The transported quotient power basis for executable `GF(2^64)`. -/
noncomputable def polynomialPowerBasis : PowerBasis (ZMod 2) ConcreteField :=
  (AdjoinRoot.powerBasis (BinaryField.Extension.polynomial_ne_zero definingPolynomialData)).map
    toSpecAlgEquiv.symm

@[simp]
theorem polynomialPowerBasis_dim_eq :
    polynomialPowerBasis.dim = extensionDegree := by
  simp [polynomialPowerBasis, BinaryField.Extension.polynomial_natDegree,
    definingPolynomialData, extensionDegree]

/-- The executable polynomial basis as a Lean basis. -/
noncomputable def polynomialBasisBasis :
    Module.Basis (Fin extensionDegree) (ZMod 2) ConcreteField :=
  polynomialPowerBasis.basis.reindex (finCongr polynomialPowerBasis_dim_eq)

theorem polynomialBasisBasis_apply (i : Fin extensionDegree) :
    polynomialBasisBasis i = root ^ i.val := by
  unfold polynomialBasisBasis polynomialPowerBasis
  rw [Module.Basis.reindex_apply]
  change toSpecAlgEquiv.symm
      (AdjoinRoot.powerBasisAux (BinaryField.Extension.polynomial_ne_zero definingPolynomialData)
        ((finCongr polynomialPowerBasis_dim_eq).symm i)) = root ^ i.val
  rw [show
      AdjoinRoot.powerBasisAux (BinaryField.Extension.polynomial_ne_zero definingPolynomialData)
          ((finCongr polynomialPowerBasis_dim_eq).symm i) =
        (BinaryField.Extension.root definingPolynomialData) ^
          ((finCongr polynomialPowerBasis_dim_eq).symm i).val by
    simp [AdjoinRoot.powerBasisAux, BinaryField.Extension.root]]
  rw [map_pow]
  change toSpecAlgEquiv.symm GF2_64.root ^
      ((finCongr polynomialPowerBasis_dim_eq).symm i).val = root ^ i.val
  have hrootSymm : toSpecAlgEquiv.symm GF2_64.root = root := by
    rw [AlgEquiv.symm_apply_eq]
    exact toSpec_root.symm
  rw [hrootSymm]
  congr 1

/-- Each Lean polynomial-basis vector is present in the executable basis array. -/
theorem polynomialBasisBasis_mem (i : Fin extensionDegree) :
    polynomialBasisBasis i ∈ polynomialBasis.toList := by
  rw [polynomialBasisBasis_apply]
  rw [← Array.mem_def]
  rw [polynomialBasis, BinaryField.Extension.Concrete.polynomialBasis, Array.mem_ofFn]
  exact ⟨i, rfl⟩

/-- The executable polynomial basis separates distinct elements by GF64 trace coordinates. -/
theorem algebraicTraceValue_separates {a b : ConcreteField} (hne : a ≠ b) :
    ∃ beta, beta ∈ polynomialBasis.toList ∧ algebraicTraceValue (beta * (a - b)) ≠ 0 := by
  have hx : a - b ≠ 0 := sub_ne_zero.mpr hne
  rcases exists_basis_trace_ne polynomialBasisBasis hx with ⟨i, htrace⟩
  refine ⟨polynomialBasisBasis i, polynomialBasisBasis_mem i, ?_⟩
  unfold algebraicTraceValue
  intro hzero
  apply htrace
  have hz' :
      algebraMap (ZMod 2) ConcreteField
          (Algebra.trace (ZMod 2) ConcreteField (polynomialBasisBasis i * (a - b))) =
        algebraMap (ZMod 2) ConcreteField 0 := by
    rw [map_zero]
    exact hzero
  exact (FaithfulSMul.algebraMap_injective (ZMod 2) ConcreteField) hz'

end ConcreteField

/-- Shoup trace splitter context for `GF(2^64)`. -/
def shoupTraceContext :
    CPolynomial.Roots.FiniteField.SmallPrimeTraceContext ConcreteField where
  toFiniteFieldContext := finiteFieldContext
  p := 2
  k := extensionDegree
  p_prime := Nat.prime_two
  q_eq := by
    simp [finiteFieldContext, fieldSize, BinaryField.Extension.fieldSize]
  baseConstants := ConcreteField.baseConstants
  baseConstants_size := ConcreteField.baseConstants_size
  basis := ConcreteField.polynomialBasis
  basis_size := ConcreteField.polynomialBasis_size
  traceValue := tracePowerSum 2 extensionDegree
  traceValue_eq_powerSum := fun _ ↦ rfl
  traceValue_mem_base := by
    intro z
    rw [← ConcreteField.algebraicTraceValue_eq_powerSum]
    exact ConcreteField.algebraicTraceValue_mem_base z
  trace_separates := by
    intro a b hne
    rcases ConcreteField.algebraicTraceValue_separates hne with ⟨beta, hbeta, htrace⟩
    refine ⟨beta, hbeta, ?_⟩
    rwa [← ConcreteField.algebraicTraceValue_eq_powerSum]

/-- Default Las Vegas trace configuration for `GF(2^64)`. -/
def lasVegasConfig : CPolynomial.Roots.FiniteField.LasVegasConfig where
  cutoff := extensionDegree
  tryOddRandomizedSplitting := true
  tryEvenTraceSplitting := true

/-- Deterministic basis-cycle Las Vegas probes for `GF(2^64)`. -/
def lasVegasProbeFamily :
    CPolynomial.Roots.FiniteField.ProbeFamily ConcreteField :=
  CPolynomial.Roots.FiniteField.traceBasisProbeFamily shoupTraceContext

/-- Smooth cyclic splitter context for `GF(2^64)` with the supplied leaf evaluator. -/
def smoothCyclicRootContextWith
    (leafEvaluator : CPolynomial.BatchEvalContext ConcreteField) :
    CPolynomial.Roots.FiniteField.SmoothCyclicRootContext ConcreteField :=
  CPolynomial.Roots.FiniteField.smoothCyclicRootContextOf
    fieldSize
    primitiveRoot
    smoothRootSchedule
    leafEvaluator
    (CPolynomial.Roots.FiniteField.smoothSplitterInput
      fieldSize primitiveRoot smoothRootSchedule)
    (by
      rw [Nat.card_eq_fintype_card]
      exact ConcreteField.card)
    primitiveRoot_order
    smoothRootSchedule_fold_eq_one
    (by
      intro M D p factor h
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_sound
        M D leafEvaluator fieldSize primitiveRoot smoothRootSchedule h)
    (by
      intro M D p a _hvalid hp hroot
      exact CPolynomial.Roots.FiniteField.smoothLinearFactorsAlgorithmWith_complete
        M D leafEvaluator fieldSize primitiveRoot smoothRootSchedule
        (by
          rw [Nat.card_eq_fintype_card]
          exact ConcreteField.card)
        primitiveRoot_order
        (by decide)
        hp hroot)

/-- Smooth cyclic splitter context for `GF(2^64)` using Horner leaf evaluation. -/
def smoothHornerRootContext :
    CPolynomial.Roots.FiniteField.SmoothCyclicRootContext ConcreteField :=
  smoothCyclicRootContextWith (CPolynomial.BatchEvalContext.horner ConcreteField)

/-- Smooth cyclic splitter context for `GF(2^64)` using subproduct-tree leaf evaluation. -/
def smoothSubproductRootContext :
    CPolynomial.Roots.FiniteField.SmoothCyclicRootContext ConcreteField :=
  smoothCyclicRootContextWith
    (CPolynomial.BatchEvalContext.subproduct ConcreteField
      CPolynomial.MulContext.naive CPolynomial.ModContext.naive)

end GF2_64

/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Fields.Binary.Tower.Concrete.Arithmetic
public import CompPoly.Fields.Binary.Tower.Support.DefiningPoly

/-!
# Concrete binary tower field construction interface

Compatibility entry point for the executable arithmetic, together with the law records,
finite-field utilities, and field-instance assembly used by the recursive construction.
Arithmetic-only clients can import `CompPoly.Fields.Binary.Tower.Concrete.Arithmetic`;
canonical field clients use `CompPoly.Fields.Binary.Tower.Concrete.Field`.
-/

@[expose] public section

namespace ConcreteBinaryTower

open Polynomial

-- Isomorphism between ConcreteBTField 0 and GF(2)
-- Ensure GF(2) has decidable equality
noncomputable instance : DecidableEq (GF(2)) :=
  fun x y =>
    -- Use the isomorphism between GF(2) and ZMod 2
    let φ : GF(2) ≃ₐ[ZMod 2] ZMod 2 := GaloisField.equivZmodP 2
    -- ZMod 2 has decidable equality
    if h : φ x = φ y then
      isTrue (by
        -- φ is injective, so φ x = φ y implies x = y
        exact φ.injective h)
    else
      isFalse (by
        intro h_eq
        -- If x = y, then φ x = φ y
        apply h
        exact congrArg φ h_eq)

noncomputable def toConcreteBTF0 : GF(2) → ConcreteBTField 0 :=
  fun x => if decide (x = 0) then zero else one -- it depends on 'instFieldGaloisField'

noncomputable def fromConcreteBTF0 : ConcreteBTField 0 → (GF(2)) :=
  fun x => if decide (x = zero) then 0 else 1

-- Helper : Convert coefficients back to BitVec
def coeffsToBitVec {n : ℕ} (coeffs : List (ZMod 2)) : BitVec n :=
  let val := List.foldr (fun c acc => acc * 2 + c.val) 0 (coeffs.take n)
  BitVec.ofNat n val

-------------------------------------------------------------------------------------------
structure ConcreteBTFAddCommGroupProps (k : ℕ) where
  add_assoc : ∀ a b c : ConcreteBTField k, (a + b) + c = a + (b + c) := add_assoc
  add_comm : ∀ a b : ConcreteBTField k, a + b = b + a := add_comm
  add_zero : ∀ a : ConcreteBTField k, a + zero = a := add_zero
  zero_add : ∀ a : ConcreteBTField k, zero + a = a := zero_add
  add_neg : ∀ a : ConcreteBTField k, a + (neg a) = zero := neg_add_cancel

-- Ring properties structure
structure ConcreteBTFRingProps (k : ℕ) extends (ConcreteBTFAddCommGroupProps k) where
  -- Multiplication equations and basic properties
  mul_eq : ∀ (a b : ConcreteBTField k) (h_k : k > 0)
    {a₁ a₀ b₁ b₀ : ConcreteBTField (k - 1)}
    (_h_a : (a₁, a₀) = split h_k a) (_h_b : (b₁, b₀) = split h_k b),
    concrete_mul a b =
      《 concrete_mul a₀ b₁ + concrete_mul b₀ a₁ + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)),
      concrete_mul a₀ b₀ + concrete_mul a₁ b₁ 》

  -- Zero and one laws
  zero_mul : ∀ a : ConcreteBTField k, concrete_mul zero a = zero
  zero_mul' : ∀ a : ConcreteBTField k, concrete_mul 0 a = 0
  mul_zero : ∀ a : ConcreteBTField k, concrete_mul a zero = zero
  mul_zero' : ∀ a : ConcreteBTField k, concrete_mul a 0 = 0
  one_mul : ∀ a : ConcreteBTField k, concrete_mul one a = a
  mul_one : ∀ a : ConcreteBTField k, concrete_mul a one = a

  -- Associativity and distributivity (Ring axioms)
  mul_assoc : ∀ a b c : ConcreteBTField k, concrete_mul (concrete_mul a b) c
    = concrete_mul a (concrete_mul b c)
  mul_left_distrib : ∀ a b c : ConcreteBTField k, concrete_mul a (b + c)
    = concrete_mul a b + concrete_mul a c
  mul_right_distrib : ∀ a b c : ConcreteBTField k, concrete_mul (a + b) c
    = concrete_mul a c + concrete_mul b c

-- DivisionRing properties structure (extends Ring properties)
structure ConcreteBTFDivisionRingProps (k : ℕ) extends (ConcreteBTFRingProps k) where
  -- Multiplicative inverse property
  mul_inv_cancel : ∀ a : ConcreteBTField k, a ≠ zero → concrete_mul a (concrete_inv a) = one

-- Field properties structure (extends DivisionRing properties)
structure ConcreteBTFieldProps (k : ℕ) extends (ConcreteBTFDivisionRingProps k) where
  -- Commutativity (what makes it a Field vs just a DivisionRing)
  mul_comm : ∀ a b : ConcreteBTField k, concrete_mul a b = concrete_mul b a

@[reducible] def mkRingInstance {k : ℕ} (props : ConcreteBTFieldProps k) :
    Ring (ConcreteBTField k) where
  toAddCommGroup := mkAddCommGroupInstance
  toOne := inferInstance
  mul := concrete_mul
  mul_assoc := props.mul_assoc
  one_mul := props.one_mul
  mul_one := props.mul_one
  left_distrib := props.mul_left_distrib
  right_distrib := props.mul_right_distrib
  zero_mul := props.zero_mul
  mul_zero := props.mul_zero
  npow := npowBinRec
  npow_zero := npowBinRec_zero
  npow_succ := by
    let : Semigroup (ConcreteBTField k) := { mul_assoc := props.mul_assoc }
    exact npowBinRec_succ

  natCast n := natCast n
  natCast_zero := natCast_zero
  natCast_succ n := natCast_succ n
  intCast n := intCast n
  intCast_ofNat n := intCast_ofNat n
  intCast_negSucc n := intCast_negSucc n

@[reducible] def mkDivisionRingInstance {k : ℕ} (props : ConcreteBTFieldProps k) :
    DivisionRing (ConcreteBTField k) where
  toRing := mkRingInstance (k:=k) props
  inv := concrete_inv
  exists_pair_ne := concrete_exists_pair_ne (k := k)
  mul_inv_cancel := props.mul_inv_cancel
  inv_zero := concrete_inv_zero
  zpow := zpowRec npowBinRec
  zpow_zero' _ := rfl
  zpow_succ' := by
    let := mkRingInstance props
    exact npowBinRec_succ
  zpow_neg' _ _ := rfl
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

@[reducible] def mkFieldInstance {k : ℕ} (props : ConcreteBTFieldProps k) :
    Field (ConcreteBTField k) where
  toDivisionRing := mkDivisionRingInstance (k:=k) props
  mul_comm := props.mul_comm

structure ConcreteBTFStepResult (k : ℕ) extends (ConcreteBTFieldProps k) where
  instFintype : Fintype (ConcreteBTField k)
  fieldFintypeCard : Fintype.card (ConcreteBTField k) = 2^(2^k)
  -- Additional field theory properties for irreducibility proof
  sumZeroIffEq : ∀ (x y : ConcreteBTField k), x + y = 0 ↔ x = y
  traceMapEvalAtRootsIs1 :
    letI := mkFieldInstance (k:=k) (props:=toConcreteBTFieldProps)
    TraceMapProperty (ConcreteBTField k) (u:=Z k) k
  instIrreduciblePoly :
    letI := mkFieldInstance (k:=k) (props:=toConcreteBTFieldProps)
    (Irreducible (p := (definingPoly (s:=(Z k)))))

end ConcreteBinaryTower

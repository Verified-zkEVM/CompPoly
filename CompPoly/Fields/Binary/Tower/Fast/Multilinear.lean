/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.Tower.Fast
public import CompPoly.Multilinear.Basic

/-!
# Packed binary-tower product accumulation

The eager `FastBT128` backend uses its ordinary field multiplication and addition, with
identity reduction. Its existing ring equivalence transports arbitrary product accumulations
and coefficient-form multilinear evaluations to the concrete tower. No unreduced product
representation or delayed-reduction algorithm is introduced.
-/

@[expose] public section

open CompPoly

namespace ConcreteBinaryTower.Fast.FastBT128

/-- Converting an eager product accumulation to the concrete tower preserves its initial
accumulator and the dot product of its two vectors. -/
theorem toConcrete_accumulateProducts {n : ℕ} (init : FastBT128)
    (a b : Vector FastBT128 n) :
    toConcrete (Vector.accumulateProducts (· * ·) init a b) =
      toConcrete init + Vector.dotProduct (a.map toConcrete) (b.map toConcrete) := by
  rw [Vector.accumulateProducts_mul, toConcrete_add]
  exact congrArg (toConcrete init + ·) (Vector.map_dotProduct ringEquiv.toRingHom a b)

/-- Eager packed coefficient evaluation, followed by conversion to the concrete tower,
agrees with evaluating the converted coefficients at the converted point. -/
theorem toConcrete_evalWithProducts {n : ℕ} (p : CMlPolynomial FastBT128 n)
    (x : Vector FastBT128 n) :
    toConcrete (CMlPolynomial.evalWithProducts (· * ·) (AddMonoidHom.id FastBT128) p x) =
      CMlPolynomial.eval (CMlPolynomial.map ringEquiv.toRingHom p) (x.map toConcrete) := by
  rw [CMlPolynomial.evalWithProducts_eq_eval (· * ·) (AddMonoidHom.id FastBT128)
    (fun _ _ => rfl)]
  exact CMlPolynomial.map_eval ringEquiv.toRingHom p x

end ConcreteBinaryTower.Fast.FastBT128

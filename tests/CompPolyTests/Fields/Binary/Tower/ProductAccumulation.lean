/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.Tower.Fast.Multilinear
public import CompPoly.Fields.Binary.Tower.Fast.Multilinear

/-!
# Packed tower accumulation regressions

The universal refinements preserve the entire field value, including arbitrary initial
accumulators. Executable checks cover empty and cancelling sums, coefficient order, both limbs,
and the failure of integer-word multiplication to implement tower multiplication.
-/

public meta section

namespace CompPolyTests.TowerProductAccumulation

open CompPoly ConcreteBinaryTower ConcreteBinaryTower.Fast

example {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) {n : ℕ} (a b : Vector R n) :
    f (Vector.dotProduct a b) = Vector.dotProduct (a.map f) (b.map f) :=
  Vector.map_dotProduct f a b

example {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {n : ℕ} (p : CMlPolynomial R n) (x : Vector R n) :
    f (CMlPolynomial.eval p x) = CMlPolynomial.eval (CMlPolynomial.map f p) (x.map f) :=
  CMlPolynomial.map_eval f p x

example {n : ℕ} (init : FastBT128) (a b : Vector FastBT128 n) :
    FastBT128.toConcrete (Vector.accumulateProducts (· * ·) init a b) =
      FastBT128.toConcrete init +
        Vector.dotProduct (a.map FastBT128.toConcrete) (b.map FastBT128.toConcrete) :=
  FastBT128.toConcrete_accumulateProducts init a b

example {n : ℕ} (p : CMlPolynomial FastBT128 n) (x : Vector FastBT128 n) :
    FastBT128.toConcrete
      (CMlPolynomial.evalWithProducts (· * ·) (AddMonoidHom.id FastBT128) p x) =
    CMlPolynomial.eval (CMlPolynomial.map FastBT128.ringEquiv.toRingHom p)
      (x.map FastBT128.toConcrete) :=
  FastBT128.toConcrete_evalWithProducts p x

example (a : FastBT128) : (FastBT128.toConcrete a).toNat = a.toNat :=
  FastBT128.toNat_toConcrete a

private def accumulate {n : ℕ} (init : ℕ) (a b : Vector ℕ n) : ℕ :=
  (Vector.accumulateProducts (· * ·) (FastBT128.ofNat init)
    (a.map FastBT128.ofNat) (b.map FastBT128.ofNat)).toNat

#guard accumulate (2 ^ 127 + 2 ^ 64 + 1) #v[] #v[] == 2 ^ 127 + 2 ^ 64 + 1
#guard accumulate 7 #v[2 ^ 127, 2 ^ 127] #v[2 ^ 64, 2 ^ 64] == 7
#guard accumulate 0 #v[2 ^ 63, 2 ^ 64, 2 ^ 127] #v[1, 1, 1] ==
  2 ^ 63 + 2 ^ 64 + 2 ^ 127
#guard accumulate 0 #v[2] #v[3] == 1
#guard accumulate 0 #v[2] #v[3] != 2 * 3

private def evaluate {n : ℕ} (p : Vector ℕ (2 ^ n)) (x : Vector ℕ n) : ℕ :=
  (CMlPolynomial.evalWithProducts (· * ·) (AddMonoidHom.id FastBT128)
    (p.map FastBT128.ofNat) (x.map FastBT128.ofNat)).toNat

#guard evaluate #v[2 ^ 127 + 1] #v[] == 2 ^ 127 + 1
#guard evaluate #v[0, 1, 0, 0] #v[2, 3] == 2
#guard evaluate #v[0, 1, 0, 0] #v[3, 2] == 3
#guard evaluate #v[0, 0, 0, 1] #v[2, 3] == 1
#guard evaluate #v[2 ^ 127, 2 ^ 127] #v[1] == 0

end CompPolyTests.TowerProductAccumulation

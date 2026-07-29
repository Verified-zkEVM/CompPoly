/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.Extension.Binomial
import Mathlib.Algebra.BigOperators.Fin

/-!
# Computable binomial extension fields

A degree-`d` binomial extension of `F` is `F[X] / (X^d - W)`. Elements are represented as
dense coefficient vectors of length exactly `d`, so arithmetic is straight-line: no trimming,
no size branching, and multiplication reduces by folding the high half of the schoolbook
product back with a factor of `W`.

The parameters are bundled into `BinomialParams` and carried as a *type index* (`Ext P`), so
two different extensions of the same base field are different types and cannot have their
instances confused.

This file supplies only the operations and the elementary `coeff` lemmas — no algebraic
structure. `CompPoly/Fields/Extension/Bridge.lean` relates them to `AdjoinRoot P.poly` and
establishes `CommRing`; `CompPoly/Fields/Extension/Field.lean` adds inversion and `Field`.

## Main definitions

* `BinomialParams`: the degree `d`, the constant `W`, and the base-field cardinality `q`.
* `Ext P`: the carrier, `Vector F P.d`.
* `Ext.mul`: multiplication, with the `X^d = W` fold applied inline.

## Implementation notes

Degree bounds are *not* re-derived here. `Ext P` is a fixed-length vector, and the bridge to
degree-bounded polynomials goes through the existing `CPolynomial.degreeLT` theory
(`CompPoly/Univariate/Linear.lean`, `CompPoly/Univariate/ToPoly/Degree.lean`), whose
`degreeLTEquiv` already identifies `↥(degreeLT d)` with `Fin d → F`.
-/

namespace CompPoly.Extension

open Polynomial

variable {F : Type*} [Field F]

/--
The data defining a binomial extension `F[X] / (X^d - W)`.

Irreducibility is deliberately *not* a field here: the commutative-ring structure on `Ext P`
does not need it, and requiring it would force every consumer of the ring operations to carry
the proof. `Ext.instField` takes `[Fact (Irreducible P.poly)]` separately, mirroring
`AdjoinRoot`. Use `Polynomial.irreducible_X_pow_four_sub_C_of_card` to discharge it.
-/
structure BinomialParams (F : Type*) [Field F] [Fintype F] where
  /-- The degree of the extension. -/
  d : ℕ
  /-- The extension adjoins a `d`-th root of `W`. -/
  W : F
  /-- Degree at least two; a degree-one "extension" is just `F`. -/
  two_le : 2 ≤ d
  /-- The cardinality of the base field, as a numeral.

  This is carried as *data* rather than read off `Fintype.card F` because inversion is
  Fermat-based and must evaluate the exponent at runtime: for `F = ZMod p` with `p` around
  `2^31`, `Fintype.card F` would enumerate all of `Fin p`. Supply `card_eq` as `ZMod.card _`. -/
  q : ℕ
  /-- `q` really is the cardinality of the base field. -/
  card_eq : Fintype.card F = q

namespace BinomialParams

variable [Fintype F] (P : BinomialParams F)

/-- The defining polynomial `X^d - W`. Part of the specification only; the computable
arithmetic on `Ext P` never evaluates it. -/
noncomputable def poly : F[X] := X ^ P.d - C P.W

@[simp] theorem natDegree_poly : P.poly.natDegree = P.d := natDegree_X_pow_sub_C

theorem monic_poly : P.poly.Monic := monic_X_pow_sub_C _ (by have := P.two_le; omega)

theorem d_pos : 0 < P.d := by have := P.two_le; omega

/-- An irreducible binomial has `W ≠ 0`: otherwise `X^d - W = X^d`, which factors as `X * X^(d-1)`
with both factors non-units when `2 ≤ d`. -/
theorem W_ne_zero (h : Irreducible P.poly) : P.W ≠ 0 := by
  intro hW
  have hpoly : P.poly = X * X ^ (P.d - 1) := by
    rw [poly, hW, map_zero, sub_zero, ← pow_succ']
    congr 1
    have := P.two_le; omega
  rw [hpoly] at h
  rcases h.isUnit_or_isUnit rfl with hu | hu
  · exact not_isUnit_of_natDegree_pos (X : F[X]) (by simp) hu
  · exact not_isUnit_of_natDegree_pos ((X : F[X]) ^ (P.d - 1))
      (by simpa using by have := P.two_le; omega) hu

end BinomialParams

/--
The carrier of the extension `F[X] / (X^d - W)`: a dense coefficient vector of length `P.d`,
little-endian (index `i` is the coefficient of `X^i`).
-/
def Ext {F : Type*} [Field F] [Fintype F] (P : BinomialParams F) : Type _ := Vector F P.d

namespace Ext

variable [Fintype F] {P : BinomialParams F}

/-- View an element as its coefficient vector. This is the identity. -/
@[inline] def coeffs (x : Ext P) : Vector F P.d := x

/-- Build an element from a coefficient vector. This is the identity. -/
@[inline] def ofVector (v : Vector F P.d) : Ext P := v

/-- Build an element from a coefficient function. -/
@[inline] def ofFn (g : Fin P.d → F) : Ext P := ofVector (Vector.ofFn g)

/-- The coefficient of `X^i`. -/
@[inline] def coeff (x : Ext P) (i : Fin P.d) : F := (coeffs x)[i.val]

@[simp] theorem coeff_ofFn (g : Fin P.d → F) (i : Fin P.d) : coeff (ofFn g) i = g i := by
  simp [coeff, ofFn, ofVector, coeffs]

/-- Two elements with the same coefficients are equal. -/
@[ext] theorem ext {x y : Ext P} (h : ∀ i, coeff x i = coeff y i) : x = y :=
  Vector.ext fun i hi => h ⟨i, hi⟩

theorem ofFn_coeff (x : Ext P) : ofFn (coeff x) = x := by ext i; simp

/-! ### Operations -/

instance : Zero (Ext P) := ⟨ofFn fun _ => 0⟩
instance : One (Ext P) := ⟨ofFn fun i => if (i : ℕ) = 0 then 1 else 0⟩
instance : Add (Ext P) := ⟨fun x y => ofFn fun i => coeff x i + coeff y i⟩
instance : Neg (Ext P) := ⟨fun x => ofFn fun i => -coeff x i⟩
instance : Sub (Ext P) := ⟨fun x y => ofFn fun i => coeff x i - coeff y i⟩
instance : SMul F (Ext P) := ⟨fun c x => ofFn fun i => c * coeff x i⟩

/--
Multiplication in `F[X] / (X^d - W)`.

Coefficient `k` collects the schoolbook terms `x_i * y_j` with `i + j = k`, plus the terms that
wrap around, `i + j = k + d`, scaled by `W` because `X^d = W`. Since `i, j < d` we have
`i + j ≤ 2d - 2 < 2d`, so each pair `(i, j)` contributes to exactly one `k`.
-/
@[inline, specialize]
def mul (x y : Ext P) : Ext P :=
  ofFn fun k => ∑ i : Fin P.d, ∑ j : Fin P.d,
    if (i : ℕ) + (j : ℕ) = (k : ℕ) then coeff x i * coeff y j
    else if (i : ℕ) + (j : ℕ) = (k : ℕ) + P.d then P.W * (coeff x i * coeff y j)
    else 0

instance : Mul (Ext P) := ⟨mul⟩

/-- `Nat`-power by binary exponentiation, so `x ^ n` costs `O(log n)` multiplications. -/
instance : Pow (Ext P) ℕ := ⟨fun x n => npowBinRec n x⟩

instance : NatCast (Ext P) := ⟨fun n => ofFn fun i => if (i : ℕ) = 0 then (n : F) else 0⟩
instance : IntCast (Ext P) := ⟨fun n => ofFn fun i => if (i : ℕ) = 0 then (n : F) else 0⟩

instance [DecidableEq F] : DecidableEq (Ext P) :=
  inferInstanceAs (DecidableEq (Vector F P.d))
instance [BEq F] : BEq (Ext P) := inferInstanceAs (BEq (Vector F P.d))
instance [Repr F] : Repr (Ext P) := inferInstanceAs (Repr (Vector F P.d))
instance : Inhabited (Ext P) := ⟨0⟩

/-! ### Coefficients of the operations -/

@[simp] theorem coeff_zero (i : Fin P.d) : coeff (0 : Ext P) i = 0 := coeff_ofFn _ _
@[simp] theorem coeff_one (i : Fin P.d) :
    coeff (1 : Ext P) i = if (i : ℕ) = 0 then 1 else 0 := coeff_ofFn _ _
@[simp] theorem coeff_add (x y : Ext P) (i : Fin P.d) :
    coeff (x + y) i = coeff x i + coeff y i := coeff_ofFn _ _
@[simp] theorem coeff_neg (x : Ext P) (i : Fin P.d) : coeff (-x) i = -coeff x i := coeff_ofFn _ _
@[simp] theorem coeff_sub (x y : Ext P) (i : Fin P.d) :
    coeff (x - y) i = coeff x i - coeff y i := coeff_ofFn _ _
@[simp] theorem coeff_smul (c : F) (x : Ext P) (i : Fin P.d) :
    coeff (c • x) i = c * coeff x i := coeff_ofFn _ _

@[simp] theorem coeff_mul (x y : Ext P) (k : Fin P.d) :
    coeff (x * y) k = ∑ i : Fin P.d, ∑ j : Fin P.d,
      if (i : ℕ) + (j : ℕ) = (k : ℕ) then coeff x i * coeff y j
      else if (i : ℕ) + (j : ℕ) = (k : ℕ) + P.d then P.W * (coeff x i * coeff y j)
      else 0 := coeff_ofFn _ _

@[simp] theorem coeff_natCast (n : ℕ) (i : Fin P.d) :
    coeff (n : Ext P) i = if (i : ℕ) = 0 then (n : F) else 0 := coeff_ofFn _ _

@[simp] theorem coeff_intCast (n : ℤ) (i : Fin P.d) :
    coeff (n : Ext P) i = if (i : ℕ) = 0 then (n : F) else 0 := coeff_ofFn _ _

theorem pow_def (x : Ext P) (n : ℕ) : x ^ n = npowBinRec n x := rfl

end Ext

end CompPoly.Extension

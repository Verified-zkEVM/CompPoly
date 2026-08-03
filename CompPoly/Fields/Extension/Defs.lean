/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Binomial
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Computable extension fields by an arbitrary monic modulus

A degree-`d` extension of `F` is `F[X] / f` for a monic `f` of degree `d`. Elements are
represented as dense coefficient vectors of length exactly `d`, so arithmetic is straight-line:
no trimming and no size branching. Multiplication expands each product monomial `Xⁱ⁺ʲ` through
`monomialMod (i + j)`, the reduced form of `Xⁱ⁺ʲ` modulo `f`, obtained by iterating a single
"multiply by `X`, reduce mod `f`" linear map, `shiftReduce`.

The parameters are bundled into `GeneralParams` and carried as a *type index* (`Ext P`), so two
different extensions of the same base field are different types and cannot have their instances
confused.

The special case `f = X^d - W` (a binomial extension) is recovered by
`BinomialParams.toGeneral`, whose `lower` vector is `(-W, 0, …, 0)`; see `Extension/Binomial.lean`
for the irreducibility criterion that discharges `Fact (Irreducible P.poly)` in that case.

This file supplies only the operations and the elementary `coeff` lemmas — no algebraic
structure. `CompPoly/Fields/Extension/Bridge.lean` relates them to `AdjoinRoot P.poly` and
establishes `CommRing`; `CompPoly/Fields/Extension/Field.lean` adds inversion and `Field`.

## Main definitions

* `GeneralParams`: the degree `d`, the lower coefficients of the monic modulus, and the
  base-field cardinality `q`.
* `Ext P`: the carrier, `Vector F P.d`.
* `Ext.shiftReduce`: multiply by `X` and reduce mod `f`; iterated to build `Ext.monomialMod`.
* `Ext.monomialMod k`: the reduced form of `X^k` modulo `f`.
* `Ext.mul`: multiplication, expanding product monomials through `monomialMod`.
* `BinomialParams.toGeneral`: the binomial special case `f = X^d - W`.

## Implementation notes

There is no degree-bound invariant to maintain: `Ext P` has length exactly `P.d`, so the bound
is *structural* rather than a proposition carried alongside the data. This subtree is therefore
independent of the `CPolynomial` stack — it imports none of `CompPoly/Univariate/`. Where a
degree bound is needed on the *polynomial* side (to show the representative chosen by
`Ext.toQuot` is the canonical one), it is proved directly in
`CompPoly/Fields/Extension/Bridge.lean` as `degree_repr_lt`.
-/

@[expose] public section

namespace CompPoly.Extension

open Polynomial

variable {F : Type*} [Field F]

/--
The data defining an extension `F[X] / f` by a monic modulus `f` of degree `d`.

The modulus is stored by its `d` lower coefficients: `f = X^d + ∑_{i < d} lower[i] · X^i`. The
leading coefficient is an implicit `1`, so `f` is monic by construction.

Irreducibility is deliberately *not* a field here: the commutative-ring structure on `Ext P`
does not need it, and requiring it would force every consumer of the ring operations to carry
the proof. `Ext.instField` takes `[Fact (Irreducible P.poly)]` separately, mirroring
`AdjoinRoot`.
-/
structure GeneralParams (F : Type*) [Field F] [Fintype F] where
  /-- The degree of the extension. -/
  d : ℕ
  /-- Degree at least two; a degree-one "extension" is just `F`. -/
  two_le : 2 ≤ d
  /-- The lower coefficients of the monic modulus, little-endian: `lower[i]` is the coefficient
  of `X^i` in `poly`, for `i < d`. The coefficient of `X^d` is an implicit `1`. -/
  lower : Vector F d
  /-- The cardinality of the base field, as a numeral.

  This is carried as *data* rather than read off `Fintype.card F` because inversion is
  Fermat-based and must evaluate the exponent at runtime: for `F = ZMod p` with `p` around
  `2^31`, `Fintype.card F` would enumerate all of `Fin p`. Supply `card_eq` as `ZMod.card _`. -/
  q : ℕ
  /-- `q` really is the cardinality of the base field. -/
  card_eq : Fintype.card F = q

namespace GeneralParams

variable [Fintype F] (P : GeneralParams F)

/-- The coefficient of `X^i` in the lower part of the modulus. -/
@[inline] def lowerCoeff (i : Fin P.d) : F := P.lower[i.val]

/-- `lowerCoeff` extended by zero outside the valid range, for reindexing sums in
`CompPoly/Fields/Extension/Bridge.lean`. -/
def lowerCoeffNat (k : ℕ) : F := if h : k < P.d then P.lower[k] else 0

@[simp] theorem lowerCoeffNat_coe (i : Fin P.d) : P.lowerCoeffNat (i : ℕ) = P.lowerCoeff i := by
  rw [lowerCoeffNat, dif_pos i.isLt]; rfl

theorem lowerCoeffNat_of_ge {k : ℕ} (h : P.d ≤ k) : P.lowerCoeffNat k = 0 := dif_neg (by omega)

theorem d_pos : 0 < P.d := by have := P.two_le; omega

/-- The monic defining polynomial `X^d + ∑_{i < d} lower[i] · X^i`. Part of the specification
only; the computable arithmetic on `Ext P` never evaluates it. -/
noncomputable def poly : F[X] := X ^ P.d + ∑ i : Fin P.d, C (P.lowerCoeff i) * X ^ (i : ℕ)

/-- The lower part of the modulus has degree strictly less than `d`. -/
theorem degree_lower_lt :
    (∑ i : Fin P.d, C (P.lowerCoeff i) * X ^ (i : ℕ)).degree < (P.d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe P.d)]
  intro i _
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)

theorem degree_poly : P.poly.degree = (P.d : WithBot ℕ) := by
  rw [poly, degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact P.degree_lower_lt),
    degree_X_pow]

theorem monic_poly : P.poly.Monic := by
  rw [poly]
  exact (monic_X_pow P.d).add_of_left (by rw [degree_X_pow]; exact P.degree_lower_lt)

@[simp] theorem natDegree_poly : P.poly.natDegree = P.d :=
  natDegree_eq_of_degree_eq_some P.degree_poly

end GeneralParams

/--
The carrier of the extension `F[X] / f`: a dense coefficient vector of length `P.d`,
little-endian (index `i` is the coefficient of `X^i`).
-/
def Ext {F : Type*} [Field F] [Fintype F] (P : GeneralParams F) : Type _ := Vector F P.d

namespace Ext

variable [Fintype F] {P : GeneralParams F}

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

/-- `coeff` extended by zero outside the valid range. Handy for reindexing sums in
`CompPoly/Fields/Extension/Bridge.lean` without carrying `Fin` bound proofs. -/
def coeffNat (x : Ext P) (i : ℕ) : F := if h : i < P.d then coeff x ⟨i, h⟩ else 0

@[simp] theorem coeffNat_coe (x : Ext P) (i : Fin P.d) : coeffNat x (i : ℕ) = coeff x i := by
  rw [coeffNat, dif_pos i.isLt]

theorem coeffNat_of_lt (x : Ext P) {i : ℕ} (h : i < P.d) : coeffNat x i = coeff x ⟨i, h⟩ :=
  dif_pos h

theorem coeffNat_of_ge (x : Ext P) {i : ℕ} (h : P.d ≤ i) : coeffNat x i = 0 :=
  dif_neg (by omega)

/-! ### Distinguished elements

`ofBase` embeds the base field as constant coefficients and `gen` is the class of `X`, i.e. the
adjoined root of `f`. They are the two elements a consumer of the extension needs by name;
`CompPoly/Fields/Extension/Bridge.lean` promotes `ofBase` to an `Algebra` structure and proves
`gen ^ d = xPowD` (the reduced form of `X^d`).
-/

/-- The base field embedded into the extension, as the constant coefficient. -/
@[inline] def ofBase (c : F) : Ext P := ofFn fun i => if (i : ℕ) = 0 then c else 0

/-- The adjoined root: the class of `X`. -/
def gen : Ext P := ofFn fun i => if (i : ℕ) = 1 then 1 else 0

/-! ### Operations

Multiplication is defined in terms of `shiftReduce` — the "multiply by `X`, reduce mod `f`"
map — whose iterates `monomialMod k = shiftReduce^[k] 1` are the reduced monomials `X^k mod f`.
Everything downstream is proved from the single homomorphism law
`toQuot (shiftReduce e) = rt * toQuot e` in `CompPoly/Fields/Extension/Bridge.lean`.
-/

instance : Zero (Ext P) := ⟨ofFn fun _ => 0⟩
instance : One (Ext P) := ⟨ofFn fun i => if (i : ℕ) = 0 then 1 else 0⟩
instance : Add (Ext P) := ⟨fun x y => ofFn fun i => coeff x i + coeff y i⟩
instance : Neg (Ext P) := ⟨fun x => ofFn fun i => -coeff x i⟩
instance : Sub (Ext P) := ⟨fun x y => ofFn fun i => coeff x i - coeff y i⟩
instance : SMul F (Ext P) := ⟨fun c x => ofFn fun i => c * coeff x i⟩

/--
Multiply by `X` and reduce modulo `f`.

`X · (∑ eᵢ Xⁱ) = ∑ eᵢ X^(i+1)`, whose top term `e_{d-1} X^d` wraps via `X^d = -∑ lowerₘ Xᵐ`.
So coefficient `m` of the reduced result is `e_{m-1} - e_{d-1} · lowerₘ`, with `e_{-1} = 0`.
This is the single linear map whose iterates build the reduction table `red`.
-/
def shiftReduce (e : Ext P) : Ext P :=
  ofFn fun m =>
    (if (m : ℕ) = 0 then 0 else coeffNat e ((m : ℕ) - 1))
      - coeffNat e (P.d - 1) * P.lowerCoeff m

/-- The reduced form of `X^k` modulo `f`, obtained by iterating `shiftReduce` (multiply by `X`,
reduce) `k` times from `1 = X^0`. Its image under `toQuot` is `rt ^ k`. -/
def monomialMod (k : ℕ) : Ext P := (shiftReduce)^[k] 1

/--
Multiplication in `F[X] / f`.

Each product monomial `Xⁱ⁺ʲ` is reduced modulo `f` by `monomialMod (i + j)`, so coefficient `m`
of the product collects `xᵢ · yⱼ · [X^(i+j) mod f]ₘ` over all pairs `(i, j)`.
-/
@[inline, specialize]
def mul (x y : Ext P) : Ext P :=
  ofFn fun m =>
    ∑ i : Fin P.d, ∑ j : Fin P.d,
      coeff x i * coeff y j * coeff (monomialMod ((i : ℕ) + (j : ℕ))) m

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

@[simp] theorem coeff_shiftReduce (e : Ext P) (m : Fin P.d) :
    coeff (shiftReduce e) m =
      (if (m : ℕ) = 0 then 0 else coeffNat e ((m : ℕ) - 1))
        - coeffNat e (P.d - 1) * P.lowerCoeff m := coeff_ofFn _ _

@[simp] theorem coeff_mul (x y : Ext P) (m : Fin P.d) :
    coeff (x * y) m =
      ∑ i : Fin P.d, ∑ j : Fin P.d,
        coeff x i * coeff y j * coeff (monomialMod ((i : ℕ) + (j : ℕ))) m :=
  coeff_ofFn _ _

@[simp] theorem coeff_ofBase (c : F) (i : Fin P.d) :
    coeff (ofBase (P := P) c) i = if (i : ℕ) = 0 then c else 0 := coeff_ofFn _ _

@[simp] theorem coeff_gen (i : Fin P.d) :
    coeff (gen : Ext P) i = if (i : ℕ) = 1 then 1 else 0 := coeff_ofFn _ _

/-- `ofBase` agrees with `1` on the multiplicative unit. -/
@[simp] theorem ofBase_one : ofBase (P := P) (1 : F) = 1 := rfl

/-- `ofBase` agrees with `0`. -/
@[simp] theorem ofBase_zero : ofBase (P := P) (0 : F) = 0 := by
  ext i; simp only [coeff_ofBase, coeff_zero, ite_self]

/-- `ofBase` agrees with the `ℕ`-cast, so scalars and numerals do not diverge. -/
@[simp] theorem ofBase_natCast (n : ℕ) : ofBase (P := P) (n : F) = (n : Ext P) := rfl

/-- `ofBase` agrees with the `ℤ`-cast. -/
@[simp] theorem ofBase_intCast (n : ℤ) : ofBase (P := P) (n : F) = (n : Ext P) := rfl

@[simp] theorem coeff_natCast (n : ℕ) (i : Fin P.d) :
    coeff (n : Ext P) i = if (i : ℕ) = 0 then (n : F) else 0 := coeff_ofFn _ _

@[simp] theorem coeff_intCast (n : ℤ) (i : Fin P.d) :
    coeff (n : Ext P) i = if (i : ℕ) = 0 then (n : F) else 0 := coeff_ofFn _ _

theorem pow_def (x : Ext P) (n : ℕ) : x ^ n = npowBinRec n x := rfl

end Ext

/-! ### Binomial extensions as a special case

A binomial extension `F[X] / (X^d - W)` is the case `lower = (-W, 0, …, 0)`. `BinomialParams`
keeps the ergonomic `W`-only interface (and its dedicated irreducibility criterion in
`Extension/Binomial.lean`); `toGeneral` maps it into the general framework, and `toGeneral_poly`
identifies the two spellings of the defining polynomial.
-/

/--
The data defining a binomial extension `F[X] / (X^d - W)`. A thin front-end for the special
case `GeneralParams` with `lower = (-W, 0, …, 0)`; see `BinomialParams.toGeneral`.
-/
structure BinomialParams (F : Type*) [Field F] [Fintype F] where
  /-- The degree of the extension. -/
  d : ℕ
  /-- The extension adjoins a `d`-th root of `W`. -/
  W : F
  /-- Degree at least two; a degree-one "extension" is just `F`. -/
  two_le : 2 ≤ d
  /-- The cardinality of the base field, as a numeral. Supply as `ZMod.card _`. -/
  q : ℕ
  /-- `q` really is the cardinality of the base field. -/
  card_eq : Fintype.card F = q

namespace BinomialParams

variable [Fintype F] (P : BinomialParams F)

theorem d_pos : 0 < P.d := by have := P.two_le; omega

/-- The defining polynomial `X^d - W`. Part of the specification only. -/
noncomputable def poly : F[X] := X ^ P.d - C P.W

@[simp] theorem natDegree_poly : P.poly.natDegree = P.d := natDegree_X_pow_sub_C

theorem monic_poly : P.poly.Monic := monic_X_pow_sub_C _ (by have := P.two_le; omega)

/-- The general-framework parameters for the binomial modulus `X^d - W`: the lower coefficient
vector is `(-W, 0, …, 0)`. -/
def toGeneral : GeneralParams F where
  d := P.d
  two_le := P.two_le
  lower := Vector.ofFn fun i => if (i : ℕ) = 0 then -P.W else 0
  q := P.q
  card_eq := P.card_eq

@[simp] theorem toGeneral_d : P.toGeneral.d = P.d := rfl
@[simp] theorem toGeneral_q : P.toGeneral.q = P.q := rfl

@[simp] theorem toGeneral_lowerCoeff (i : Fin P.toGeneral.d) :
    P.toGeneral.lowerCoeff i = if (i : ℕ) = 0 then -P.W else 0 := by
  simp only [GeneralParams.lowerCoeff, toGeneral, Vector.getElem_ofFn]

/-- The general-framework polynomial of a binomial agrees with `X^d - W`. -/
theorem toGeneral_poly : P.toGeneral.poly = P.poly := by
  have hsum : (∑ i : Fin P.toGeneral.d, C (P.toGeneral.lowerCoeff i) * X ^ (i : ℕ)) = -C P.W := by
    rw [Finset.sum_eq_single_of_mem (⟨0, P.d_pos⟩ : Fin P.toGeneral.d) (Finset.mem_univ _)]
    · rw [toGeneral_lowerCoeff]; simp
    · intro i _ hi
      have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
      rw [toGeneral_lowerCoeff, if_neg hi0, map_zero, zero_mul]
  rw [GeneralParams.poly, hsum, poly, ← sub_eq_add_neg, toGeneral_d]

end BinomialParams

end CompPoly.Extension

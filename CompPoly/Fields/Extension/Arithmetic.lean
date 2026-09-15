/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Computable arithmetic for monic quotient presentations

`ExtensionParams F` stores the degree, lower modulus coefficients and an explicit inverse-exponent
parameter `q`. `Ext P` is one nominal carrier with coefficient vectors in ascending degree order.
Its coordinate maps require no algebraic structure; arithmetic uses a ring of coefficients.
The presentation index separates parameter values for a fixed coefficient algebra. Operations
and their theorems are relative to the supplied ring or field structure on `F`; the raw carrier
does not separate alternative algebra structures on that same type. Distinct coefficient
presentations should use nominal coefficient types and explicit ring maps. The polynomial quotient
interpretation uses commutative coefficients; the raw formulas are defined for any ring.

Multiplication reduces monomials with `shiftReduce`. The executable reduction-table implementation
`mulTbl` is connected to `mul` by `mul_eq_mulTbl`. Power uses binary exponentiation, and the
canonical inverse candidate uses the literal exponent `q^d - 2`.

This module supplies no cardinality or irreducibility certificate. Polynomial specifications and
quotient correspondence belong to `Extension/Defs.lean` and `Extension/Bridge.lean`; certified field
laws belong to `Extension/Field.lean`. Raw parameters with an incorrect `q` still admit arithmetic
but do not thereby acquire field laws. The binomial conversion describes the modulus `X^d - W`.
-/

@[expose] public section

namespace CompPoly.Extension

variable {F : Type*} [Ring F]

/--
The data defining an extension `F[X] / f` by a monic modulus `f` of degree `d`.

The modulus is stored by its `d` lower coefficients: `f = X^d + ∑_{i < d} lower[i] · X^i`. The
leading coefficient is an implicit `1`, so `f` is monic by construction.

Irreducibility is not part of these parameters: the quotient is a commutative ring for every
monic modulus over a commutative ring. Field laws additionally require finite-cardinality and
irreducibility certificates.
-/
structure ExtensionParams (F : Type*) where
  /-- The degree of the extension. -/
  d : ℕ
  /-- Degree at least two; a degree-one "extension" is just `F`. -/
  two_le : 2 ≤ d
  /-- The lower coefficients of the monic modulus, little-endian: `lower[i]` is the coefficient
  of `X^i` in `poly`, for `i < d`. The coefficient of `X^d` is an implicit `1`. -/
  lower : Vector F d
  /-- The proposed base cardinality, stored explicitly for the inverse exponent.

  Raw arithmetic does not certify this value. Field laws require a separate proof that
  `Nat.card F = q`, together with finiteness and irreducibility. -/
  q : ℕ

namespace ExtensionParams

variable (P : ExtensionParams F)

/-- The coefficient of `X^i` in the lower part of the modulus. -/
@[inline] def lowerCoeff (i : Fin P.d) : F := P.lower[i.val]

/-- The lower modulus coefficient at index `k`, or zero when `P.d ≤ k`. -/
def lowerCoeffNat (k : ℕ) : F := if h : k < P.d then P.lower[k] else 0

@[simp] theorem lowerCoeffNat_coe (i : Fin P.d) : P.lowerCoeffNat (i : ℕ) = P.lowerCoeff i := by
  rw [lowerCoeffNat, dif_pos i.isLt]; rfl

theorem lowerCoeffNat_of_ge {k : ℕ} (h : P.d ≤ k) : P.lowerCoeffNat k = 0 := dif_neg (by omega)

omit [Ring F] in
theorem d_pos : 0 < P.d := by have := P.two_le; omega

end ExtensionParams

/--
The carrier of the quotient by the monic modulus in `P`, with coefficients in ascending
order of powers. The parameter remains part of the type even when two moduli have equal degree.
-/
structure Ext {F : Type*} (P : ExtensionParams F) : Type _ where
  /-- The coefficient of `X^i` is stored at index `i`. -/
  coeffs : Vector F P.d

namespace Ext

variable {P : ExtensionParams F}

/-- Build an element from coefficients in ascending order of powers. -/
@[inline] def ofVector (v : Vector F P.d) : Ext P := ⟨v⟩

omit [Ring F] in
/-- Extracting the coefficients of a constructed element returns the input vector. -/
@[simp] theorem coeffs_ofVector (v : Vector F P.d) : coeffs (ofVector (P := P) v) = v := rfl

omit [Ring F] in
/-- Reconstructing an element from its coefficient vector returns that element. -/
@[simp] theorem ofVector_coeffs (x : Ext P) : ofVector (coeffs x) = x := rfl

omit [Ring F] in
/-- The coefficient vector uniquely determines an element. -/
theorem coeffs_injective : Function.Injective (coeffs (P := P)) :=
  fun _ _ h => congrArg ofVector h

/-- Build an element from a coefficient function. -/
@[inline] def ofFn (g : Fin P.d → F) : Ext P := ofVector (Vector.ofFn g)

/-- The coefficient of `X^i`. -/
@[inline] def coeff (x : Ext P) (i : Fin P.d) : F := (coeffs x)[i.val]

omit [Ring F] in
@[simp] theorem coeff_ofFn (g : Fin P.d → F) (i : Fin P.d) : coeff (ofFn g) i = g i := by
  simp [coeff, ofFn, ofVector]

omit [Ring F] in
/-- Two elements with the same coefficients are equal. -/
@[ext] theorem ext {x y : Ext P} (h : ∀ i, coeff x i = coeff y i) : x = y :=
  coeffs_injective (Vector.ext fun i hi => h ⟨i, hi⟩)

omit [Ring F] in
theorem ofFn_coeff (x : Ext P) : ofFn (coeff x) = x := by ext i; simp

/-- Coefficient vectors are exactly functions out of `Fin d`. -/
def equivFn (P : ExtensionParams F) : Ext P ≃ (Fin P.d → F) where
  toFun := coeff
  invFun := ofFn
  left_inv := ofFn_coeff
  right_inv g := funext fun i => coeff_ofFn g i

/-- The coefficient at index `i`, or zero when `P.d ≤ i`. -/
def coeffNat (x : Ext P) (i : ℕ) : F := if h : i < P.d then coeff x ⟨i, h⟩ else 0

@[simp] theorem coeffNat_coe (x : Ext P) (i : Fin P.d) : coeffNat x (i : ℕ) = coeff x i := by
  rw [coeffNat, dif_pos i.isLt]

theorem coeffNat_of_lt (x : Ext P) {i : ℕ} (h : i < P.d) : coeffNat x i = coeff x ⟨i, h⟩ :=
  dif_pos h

theorem coeffNat_of_ge (x : Ext P) {i : ℕ} (h : P.d ≤ i) : coeffNat x i = 0 :=
  dif_neg (by omega)

/-! ### Distinguished elements

`ofBase` places a coefficient-ring element in the constant coordinate, and `gen` has the
coordinates of `X`. The quotient bridge over a field promotes the constant embedding to an
`Algebra` structure and identifies the reduced power `gen ^ d` with `monomialMod d`.
-/

/-- Place a coefficient-ring element in the constant coordinate. -/
@[inline] def ofBase (c : F) : Ext P := ofFn fun i => if (i : ℕ) = 0 then c else 0

/-- The coordinate vector with coefficient one at `X` and zero elsewhere. -/
def gen : Ext P := ofFn fun i => if (i : ℕ) = 1 then 1 else 0

/-! ### Operations

Multiplication is defined in terms of `shiftReduce` — the "multiply by `X`, reduce mod `f`"
map — whose iterates `monomialMod k = shiftReduce^[k] 1` are the reduced monomials `X^k mod f`.
Everything downstream is proved from the single homomorphism law
`toQuot (shiftReduce e) = rt * toQuot e`.
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
The monic-reduction product formula, representing multiplication in `F[X] / f`
when the coefficient ring is commutative.

Each product monomial `Xⁱ⁺ʲ` is reduced modulo `f` by `monomialMod (i + j)`, so coefficient `m`
of the product collects `xᵢ · yⱼ · [X^(i+j) mod f]ₘ` over all pairs `(i, j)`.
-/
@[inline, specialize]
def mul (x y : Ext P) : Ext P :=
  ofFn fun m =>
    ∑ i : Fin P.d, ∑ j : Fin P.d,
      coeff x i * coeff y j * coeff (monomialMod ((i : ℕ) + (j : ℕ))) m

/--
The reduction table: `red P` holds `X^k mod f` for every `k ≤ 2d - 2`, i.e. every exponent a
product of two reduced elements can reach.

This is the table the `shiftReduce` docstring above refers to. It exists purely for speed: `mul`
is the specification, and `mulTbl` below is the compiled implementation that consults this table.
-/
def red (P : ExtensionParams F) : Vector (Ext P) (2 * P.d - 1) :=
  Vector.ofFn fun k => monomialMod (k : ℕ)

@[simp] theorem red_getElem {k : ℕ} (hk : k < 2 * P.d - 1) :
    (red P)[k] = monomialMod k := by
  simp only [red, Vector.getElem_ofFn]

/--
Table-driven multiplication: the compiled implementation of `mul`.

Mathematically identical to `mul`, but the reduced monomials `X^(i+j) mod f` are computed once
into `red` instead of being re-derived by `monomialMod` for every output coefficient. That drops
the cost from roughly `O(d^5)` to `O(d^3)`: `mul` evaluates `shiftReduce^[i+j]` once per
`(m, i, j)` triple, so the same `d`-fold iteration is repeated `d^3` times.

`mul` remains the definition everything is proved about; `mul_eq_mulTbl` below swaps this in for
compilation via `@[csimp]`.
-/
@[inline, specialize]
def mulTbl (x y : Ext P) : Ext P :=
  let tbl := red P
  ofFn fun m =>
    ∑ i : Fin P.d, ∑ j : Fin P.d,
      coeff x i * coeff y j *
        coeff (tbl[(i : ℕ) + (j : ℕ)]'(by
          have hi := i.isLt; have hj := j.isLt; have hd := P.two_le; omega)) m

@[csimp] theorem mul_eq_mulTbl : @mul = @mulTbl := by
  funext F _ P x y
  refine Ext.ext fun m => ?_
  simp only [mul, mulTbl, coeff_ofFn]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [red_getElem]

instance : Mul (Ext P) := ⟨mul⟩

/-- `Nat`-power by binary exponentiation, so `x ^ n` costs `O(log n)` multiplications. -/
instance : Pow (Ext P) ℕ := ⟨fun x n => npowBinRec n x⟩

instance : NatCast (Ext P) := ⟨fun n => ofFn fun i => if (i : ℕ) = 0 then (n : F) else 0⟩
instance : IntCast (Ext P) := ⟨fun n => ofFn fun i => if (i : ℕ) = 0 then (n : F) else 0⟩

instance [DecidableEq F] : DecidableEq (Ext P) := fun x y =>
  decidable_of_iff (x.coeffs = y.coeffs) coeffs_injective.eq_iff

instance [BEq F] : BEq (Ext P) := ⟨fun x y => x.coeffs == y.coeffs⟩

instance [BEq F] [LawfulBEq F] : LawfulBEq (Ext P) where
  eq_of_beq {x y} h := by
    exact coeffs_injective (eq_of_beq h)
  rfl {x} := by
    change (x.coeffs == x.coeffs) = true
    exact BEq.rfl

instance [Repr F] : Repr (Ext P) := ⟨fun x prec => reprPrec x.coeffs prec⟩
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

/-- The canonical inverse candidate `x ^ (q^d - 2)`.

Inverse laws require finite-cardinality and irreducibility certificates. For arbitrary `q`,
this operation need not send zero to zero. -/
def inv (x : Ext P) : Ext P := x ^ (P.q ^ P.d - 2)

instance instInv : Inv (Ext P) := ⟨inv⟩
instance instDiv : Div (Ext P) := ⟨fun x y => x * inv y⟩

theorem inv_def (x : Ext P) : x⁻¹ = x ^ (P.q ^ P.d - 2) := rfl
theorem div_def (x y : Ext P) : x / y = x * y⁻¹ := rfl

end Ext

/-! ### Binomial extensions as a special case

A binomial extension `F[X] / (X^d - W)` is the case `lower = (-W, 0, …, 0)`. `BinomialParams`
keeps the `W`-only interface; `toExtensionParams` maps it into the general framework. The
polynomial correspondence and binomial irreducibility criterion are proved separately.
-/

/--
Parameters for the quotient `F[X] / (X^d - W)`: the degree, constant `W`, and a proposed
base cardinality. The modulus has lower coefficients `(-W, 0, …, 0)`.
-/
structure BinomialParams (F : Type*) where
  /-- The degree of the extension. -/
  d : ℕ
  /-- The extension adjoins a `d`-th root of `W`. -/
  W : F
  /-- Degree at least two; a degree-one "extension" is just `F`. -/
  two_le : 2 ≤ d
  /-- The proposed base cardinality used by the inverse exponent. -/
  q : ℕ

namespace BinomialParams

variable (P : BinomialParams F)

omit [Ring F] in
theorem d_pos : 0 < P.d := by have := P.two_le; omega

/-- The general-framework parameters for the binomial modulus `X^d - W`: the lower coefficient
vector is `(-W, 0, …, 0)`. -/
def toExtensionParams : ExtensionParams F where
  d := P.d
  two_le := P.two_le
  lower := Vector.ofFn fun i => if (i : ℕ) = 0 then -P.W else 0
  q := P.q

@[simp] theorem toExtensionParams_d : P.toExtensionParams.d = P.d := rfl
@[simp] theorem toExtensionParams_q : P.toExtensionParams.q = P.q := rfl

@[simp] theorem toExtensionParams_lowerCoeff (i : Fin P.toExtensionParams.d) :
    P.toExtensionParams.lowerCoeff i = if (i : ℕ) = 0 then -P.W else 0 := by
  simp only [ExtensionParams.lowerCoeff, toExtensionParams, Vector.getElem_ofFn]

end BinomialParams

end CompPoly.Extension

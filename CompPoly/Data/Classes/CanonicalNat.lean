/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Canonical naturals

`CanonicalNat F` says that every element of `F` has a canonical natural number below a fixed
`bound`, and that every natural reduces to an element by `ofNat`, with `ofNat` acting as
reduction modulo `bound`. The laws make `toNat` a bijection onto `Fin bound`, so `bound` is the
cardinality of `F` and `ofNat` is exactly "the element whose canonical natural is `n % bound`".

For a prime field the canonical natural is the residue in `[0, p)`; for a binary field it is
the bit pattern of the declared basis; for an extension of degree `d` over a base of size `q`
it is the base-`q` expansion of the coefficients.

Serialization is *derived* from this class rather than stated with it. The fixed-width byte
codec of a scalar field is the little-endian bytes of `toNat` (`ByteCodec.ofCanonicalNat` in
`CompPoly.Data.Bytes.CanonicalNat`), and sampling a field element from a longer byte string
is `ofNat` of the string's integer, which is uniform up to a bound proved in `Nat` terms.
Two carriers of the same field agree on `toNat`, so they agree on every derived encoding.
-/

@[expose] public section

universe u

namespace CompPoly

/-- `F` has a canonical natural below `bound` for every element, and every natural reduces to
an element of `F` modulo `bound`. The laws make `toNat` a bijection `F ≃ Fin bound`. -/
class CanonicalNat (F : Type u) where
  /-- The exclusive upper bound on canonical naturals; equal to the cardinality of `F`. -/
  bound : ℕ
  /-- The canonical natural of an element. -/
  toNat : F → ℕ
  /-- The element with canonical natural `n % bound`. -/
  ofNat : ℕ → F
  toNat_lt (x : F) : toNat x < bound
  ofNat_toNat (x : F) : ofNat (toNat x) = x
  toNat_ofNat_of_lt {n : ℕ} (h : n < bound) : toNat (ofNat n) = n
  ofNat_mod (n : ℕ) : ofNat (n % bound) = ofNat n

namespace CanonicalNat

variable {F : Type u} [CanonicalNat F]

attribute [simp] ofNat_toNat ofNat_mod

theorem bound_pos : 0 < bound F :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (toNat_lt (ofNat (F := F) 0))

theorem toNat_injective : Function.Injective (toNat : F → ℕ) :=
  Function.LeftInverse.injective ofNat_toNat

@[simp]
theorem toNat_inj {x y : F} : toNat x = toNat y ↔ x = y :=
  toNat_injective.eq_iff

@[simp]
theorem toNat_ofNat (n : ℕ) : toNat (ofNat (F := F) n) = n % bound F := by
  rw [← ofNat_mod, toNat_ofNat_of_lt (Nat.mod_lt _ bound_pos)]

/-- Decode a natural as an element, failing when it is not a canonical natural. -/
def ofNat? (n : ℕ) : Option F :=
  if n < bound F then some (ofNat n) else none

@[simp]
theorem ofNat?_toNat (x : F) : ofNat? (toNat x) = some x := by
  simp only [ofNat?, toNat_lt, ↓reduceIte, ofNat_toNat]

theorem ofNat?_eq_some_iff {n : ℕ} {x : F} : ofNat? n = some x ↔ n < bound F ∧ toNat x = n := by
  unfold ofNat?
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨h, toNat_ofNat_of_lt h⟩
    · rintro ⟨-, rfl⟩
      exact ofNat_toNat x
  · simp only [reduceCtorEq, false_iff, not_and]
    intro h
    exact absurd h (by assumption)

theorem ofNat?_eq_none_iff {n : ℕ} : ofNat? (F := F) n = none ↔ bound F ≤ n := by
  unfold ofNat?
  split <;> simp only [reduceCtorEq, false_iff, not_le, *, true_iff, not_lt] at *
  all_goals assumption

/-- The canonical natural as an equivalence with `Fin (bound F)`. -/
def equivFin : F ≃ Fin (bound F) where
  toFun x := ⟨toNat x, toNat_lt x⟩
  invFun n := ofNat n.1
  left_inv x := ofNat_toNat x
  right_inv n := Fin.ext (toNat_ofNat_of_lt n.2)

/-- The bound is the cardinality of `F`. -/
theorem card_eq [Fintype F] : Fintype.card F = bound F := by
  rw [Fintype.card_congr (equivFin (F := F)), Fintype.card_fin]

/-! ## Constructors

Two ways a concrete type acquires the structure. A fast carrier of a prime field supplies its
own `toNat` together with the conversion from `ZMod p`; a binary field supplies its bit
pattern. Both are `@[instance_reducible]` definitions so an instance can be
`CanonicalNat.ofToField …` or `CanonicalNat.ofBitVec …` directly. -/

/-- The canonical-natural structure of a carrier of `ZMod p`: the carrier's own `toNat`, with
`ofField` as the way back. The hypothesis `toNat_ofField` is the carrier-agreement law, so
every encoding derived from this structure agrees with the one on `ZMod p`. -/
@[instance_reducible]
def ofToField {p : ℕ} [NeZero p] (toNat : F → ℕ) (ofField : ZMod p → F)
    (toNat_lt : ∀ x, toNat x < p) (ofField_cast_toNat : ∀ x, ofField (toNat x : ZMod p) = x)
    (toNat_ofField : ∀ n : ZMod p, toNat (ofField n) = n.val) : CanonicalNat F where
  bound := p
  toNat := toNat
  ofNat n := ofField (n : ZMod p)
  toNat_lt := toNat_lt
  ofNat_toNat := ofField_cast_toNat
  toNat_ofNat_of_lt h := by rw [toNat_ofField, ZMod.val_natCast, Nat.mod_eq_of_lt h]
  ofNat_mod n := by rw [ZMod.natCast_mod]

/-- The canonical-natural structure of a type presented as `k`-bit patterns: the bit pattern
read as an integer, with `bound = 2 ^ k`. -/
@[instance_reducible]
def ofBitVec {k : ℕ} (toBitVec : F → BitVec k) (ofBitVec : BitVec k → F)
    (ofBitVec_toBitVec : ∀ x, ofBitVec (toBitVec x) = x)
    (toBitVec_ofBitVec : ∀ b, toBitVec (ofBitVec b) = b) : CanonicalNat F where
  bound := 2 ^ k
  toNat x := (toBitVec x).toNat
  ofNat n := ofBitVec (BitVec.ofNat k n)
  toNat_lt x := (toBitVec x).isLt
  ofNat_toNat x := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ofBitVec_toBitVec]
  toNat_ofNat_of_lt h := by rw [toBitVec_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  ofNat_mod n := by
    congr 1
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]

end CanonicalNat

/-- `ZMod p` with the residue in `[0, p)` as canonical natural. -/
instance instCanonicalNatZMod (p : ℕ) [NeZero p] : CanonicalNat (ZMod p) where
  bound := p
  toNat := ZMod.val
  ofNat n := (n : ZMod p)
  toNat_lt := ZMod.val_lt
  ofNat_toNat := ZMod.natCast_zmod_val
  toNat_ofNat_of_lt h := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]
  ofNat_mod n := ZMod.natCast_mod n p

@[simp] theorem CanonicalNat.bound_zmod (p : ℕ) [NeZero p] : CanonicalNat.bound (ZMod p) = p := rfl

@[simp] theorem CanonicalNat.toNat_zmod {p : ℕ} [NeZero p] (x : ZMod p) :
    CanonicalNat.toNat x = x.val := rfl

@[simp] theorem CanonicalNat.ofNat_zmod {p : ℕ} [NeZero p] (n : ℕ) :
    CanonicalNat.ofNat (F := ZMod p) n = (n : ZMod p) := rfl

end CompPoly

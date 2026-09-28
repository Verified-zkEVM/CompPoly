/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Univariate.Basic
public import CompPoly.Univariate.Linear
public import CompPoly.Data.Bytes.Delimited
import all CompPoly.Univariate.Basic

/-!
# Serialization of univariate polynomials

Two encodings of a `CPolynomial R`, and they agree.

* **Fixed width, for protocol messages.** A polynomial of degree below `n`, an element of
  `↥(degreeLT n)`, is its first `n` coefficients, zero-padded: `n * width R` bytes through the
  vector codec. Decoding trims. This is `ByteCodec ↥(degreeLT n)`, unconditionally injective,
  the message shape of a sumcheck round polynomial or a FRI fold.
* **Self-delimiting, for fixtures and hashing.** A `u64` little-endian coefficient count, then
  the coefficients. This is `DelimitedCodec (CPolynomial R)` over any delimited coefficient
  codec, so it nests (`CompPoly.Bivariate.Bytes`). Injective because the representation is
  canonical: no trailing zeros, so equal coefficient lists are equal polynomials. A polynomial
  is `Valid` when its size fits in a `u64` and its coefficients are valid.

`encode_eq_encodeU64_append_toBytes` ties the two: the self-delimiting encoding is the count
followed by the fixed-width encoding at `n = size`.
-/

@[expose] public section

namespace CompPoly.CPolynomial

variable {R : Type*} [Zero R] [BEq R] [LawfulBEq R]

/-- Rebuilding a canonical polynomial from its own coefficient array gives it back. -/
theorem ofArray_val (p : CPolynomial R) : ofArray p.val = p :=
  CPolynomial.ext (Raw.Trim.trim_eq_of_isCanonical p.property)

/-- `ofFn` on `n` coefficients has degree below `n`. -/
theorem ofFn_mem_degreeLT {n : ℕ} (f : Fin n → R) : ofFn f ∈ degreeLT (R := R) n := by
  rw [mem_degreeLT_iff_size_le]
  calc (ofFn f).val.size ≤ (Array.ofFn f).size := Raw.Trim.size_le_size _
    _ = n := Array.size_ofFn

/-- A polynomial of degree below `n` is `ofFn` of its first `n` coefficients. -/
theorem ofFn_coeff_of_mem_degreeLT {n : ℕ} {p : CPolynomial R} (hp : p ∈ degreeLT (R := R) n) :
    ofFn (fun i : Fin n => coeff p i) = p := by
  rw [eq_iff_coeff]
  intro i
  rw [coeff_ofFn]
  split
  · rfl
  · rename_i h
    exact (coeff_eq_zero_of_size_le p
      (le_trans (mem_degreeLT_iff_size_le.mp hp) (Nat.le_of_not_lt h))).symm

/-! ## Fixed width: `degreeLT n` -/

/-- The coefficient vector of a polynomial of degree below `n`, zero-padded. -/
def coeffVector (n : ℕ) (p : ↥(degreeLT (R := R) n)) : Vector R n :=
  Vector.ofFn fun i => coeff p.1 i

/-- The polynomial with the given `n` coefficients, as an element of `degreeLT n`. -/
def ofCoeffVector (n : ℕ) (v : Vector R n) : ↥(degreeLT (R := R) n) :=
  ⟨ofFn fun i => v[i], ofFn_mem_degreeLT _⟩

@[simp]
theorem ofCoeffVector_coeffVector (n : ℕ) (p : ↥(degreeLT (R := R) n)) :
    ofCoeffVector n (coeffVector n p) = p := by
  apply Subtype.ext
  show ofFn (fun i : Fin n => (Vector.ofFn fun j : Fin n => coeff p.1 j)[i]) = p.1
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact ofFn_coeff_of_mem_degreeLT p.2

/-- Degree below `n`: the `n` coefficients, `n * width R` bytes. -/
instance instByteCodecDegreeLT [ByteCodec R] (n : ℕ) : ByteCodec ↥(degreeLT (R := R) n) where
  width := n * ByteCodec.width R
  toBytes p := ByteCodec.toBytes (coeffVector n p)
  ofBytes? b := (ByteCodec.ofBytes? b : Option (Vector R n)).map (ofCoeffVector n)
  ofBytes?_toBytes p := by
    rw [ByteCodec.ofBytes?_toBytes, Option.map_some, ofCoeffVector_coeffVector]

@[simp] theorem width_degreeLT [ByteCodec R] (n : ℕ) :
    ByteCodec.width ↥(degreeLT (R := R) n) = n * ByteCodec.width R := rfl

theorem toBytes_degreeLT [ByteCodec R] {n : ℕ} (p : ↥(degreeLT (R := R) n)) :
    ByteCodec.toBytes p = ByteCodec.toBytes (coeffVector n p) := rfl

/-! ## Self-delimiting: `CPolynomial R` -/

open DelimitedCodec in
/-- A `u64` coefficient count, then the coefficients. -/
instance instDelimitedCodec [DelimitedCodec R] : DelimitedCodec (CPolynomial R) where
  encode p := encode p.val.toList
  decode? l := (decode? (α := List R) l).map fun cl => (ofArray cl.1.toArray, cl.2)
  Valid p := Valid p.val.toList
  decode?_encode_append p rest h := by
    rw [decode?_encode_append _ _ h, Option.map_some, Array.toArray_toList, ofArray_val]

theorem valid_iff [DelimitedCodec R] (p : CPolynomial R) :
    DelimitedCodec.Valid p ↔ p.val.size < 2 ^ 64 ∧ ∀ c ∈ p.val.toList, DelimitedCodec.Valid c := by
  show DelimitedCodec.Valid p.val.toList ↔ _
  rw [DelimitedCodec.valid_list, Array.length_toList]

/-- Over a fixed-width coefficient type, a polynomial is valid exactly when its size fits. -/
theorem valid_iff_size_lt [ByteCodec R] (p : CPolynomial R) :
    DelimitedCodec.Valid p ↔ p.val.size < 2 ^ 64 := by
  rw [valid_iff]
  simp only [DelimitedCodec.valid_ofByteCodec, implies_true, and_true]

theorem encode_eq [DelimitedCodec R] (p : CPolynomial R) :
    DelimitedCodec.encode p
      = DelimitedCodec.encodeU64 p.val.size ++ DelimitedCodec.encodeList p.val.toList := by
  show DelimitedCodec.encode p.val.toList = _
  rw [DelimitedCodec.encode_list, Array.length_toList]

omit [BEq R] [LawfulBEq R] in
/-- The coefficient list of a polynomial is its coefficient function on `Fin p.val.size`. -/
theorem toList_val_eq_ofFn (p : CPolynomial R) :
    p.val.toList = List.ofFn fun i : Fin p.val.size => coeff p i := by
  rw [← Array.toList_ofFn]
  congr 1
  apply Array.ext
  · simp only [Array.size_ofFn]
  · intro i h₁ h₂
    rw [Array.getElem_ofFn, coeff, Raw.coeff, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem h₁, Option.getD_some]

/-- The self-delimiting encoding is the count followed by the fixed-width encoding at
`n = size`: the two formats agree on their common part. -/
theorem encode_eq_encodeU64_append_toBytes [ByteCodec R] (p : CPolynomial R) :
    DelimitedCodec.encode p
      = DelimitedCodec.encodeU64 p.val.size
        ++ (ByteCodec.toBytes (⟨p, mem_degreeLT_iff_size_le.mpr le_rfl⟩ :
            ↥(degreeLT (R := R) p.val.size))).toList := by
  rw [encode_eq, toBytes_degreeLT, ByteCodec.toList_toBytes_vector, coeffVector,
    Vector.toList_ofFn, toList_val_eq_ofFn]
  rfl

end CompPoly.CPolynomial

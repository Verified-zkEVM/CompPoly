import CompPoly.Univariate.Basic
import CompPoly.Univariate.Raw.Core
import CompPoly.Univariate.Raw.Division

namespace CompPoly

open CPolynomial

section Division

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- Quotient of `p` by a monic polynomial `q`. Matches Mathlib's `Polynomial.divByMonic`. -/
def divByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.divByMonic p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.divByMonic p.val q.val)⟩

/-- Remainder of `p` modulo a monic polynomial `q`. Matches Mathlib's `Polynomial.modByMonic`. -/
def modByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonic p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.modByMonic p.val q.val)⟩

/-- Quotient of `p` by `q` (when `R` is a field). -/
def div (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.div p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.div p.val q.val)⟩

/-- Remainder of `p` modulo `q` (when `R` is a field). -/
def mod (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.mod p.val q.val).trim, Raw.Trim.isCanonical_trim (Raw.mod p.val q.val)⟩

instance : Div (CPolynomial R) := ⟨div⟩
instance : Mod (CPolynomial R) := ⟨mod⟩

end Division

section ImplementationCorrectness

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- `div` matches `Polynomial.div` with respect to `toPoly` -/
theorem div_toPoly (p q : CPolynomial R) :
    (div p q).toPoly = (Polynomial.div p.toPoly q.toPoly) := by
  show (Raw.div p.val q.val).trim.toPoly = _
  rw [Raw.toPoly_trim]
  exact Raw.div_toPoly p.val q.val

/-- `mod` matches `Polynomial.mod` with respect to `toPoly` -/
theorem mod_toPoly (p q : CPolynomial R) (hq : q ≠ 0) :
    (mod p q).toPoly = (Polynomial.mod p.toPoly q.toPoly) := by
  show (Raw.mod p.val q.val).trim.toPoly = _
  rw [Raw.toPoly_trim]
  have hq_val : q.val.toPoly ≠ 0 := by
    intro h
    apply hq
    apply CPolynomial.ext
    have hsize := (Raw.trim_size_zero_iff_toPoly_zero q.val).mpr h
    simp_all only [ne_eq, trim_eq, Array.size_eq_zero_iff, Array.empty_eq]
    rfl
  exact Raw.mod_toPoly p.val q.val hq_val

end ImplementationCorrectness

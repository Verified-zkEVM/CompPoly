/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Correctness.Pair
import CompPoly.Univariate.NTTFast.Correctness.Radix4DIT

/-!
# NTTFast multiplication correctness

Plan-level and one-shot correctness theorems for `NTTFast` multiplication.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

open scoped BigOperators

variable {R : Type*} [Field R]

namespace Plan
/-- A well-formed plan's forward transform computes the bit-reversed forward NTT. -/
theorem forwardImpl_correct (P : Plan R) (hP : WellFormed P) (p : CPolynomial.Raw R) :
    forwardImpl P p =
      NTT.Transform.bitRevPermute P.domain (NTT.Forward.forwardSpec P.domain p) := by
  rcases hP with ⟨_, _, htwiddles, _⟩
  simp [forwardImpl, htwiddles, runStagesDIFRadix4WithTwiddles_correct]

/-- A plan built from a domain has a correct forward transform. -/
theorem forwardImpl_ofDomain_correct (D : NTT.Domain R) (p : CPolynomial.Raw R) :
    forwardImpl (ofDomain D) p =
      NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D p) := by
  simpa using forwardImpl_correct (P := ofDomain D) (ofDomain_wellFormed D) p

/-- The paired forward transform equals the pair of individual forward transforms. -/
theorem forwardPairImpl_eq_pair
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial.Raw R) :
    forwardPairImpl P p q = (forwardImpl P p, forwardImpl P q) := by
  rcases hP with ⟨_, _, htwiddles, _⟩
  simp [forwardPairImpl, forwardImpl, htwiddles,
    runStagesDIFRadix4PairWithTwiddles_eq_pair]

/-- The paired forward transform computes the two bit-reversed forward NTT outputs. -/
theorem forwardPairImpl_correct
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial.Raw R) :
    forwardPairImpl P p q =
      (NTT.Transform.bitRevPermute P.domain (NTT.Forward.forwardSpec P.domain p),
        NTT.Transform.bitRevPermute P.domain (NTT.Forward.forwardSpec P.domain q)) := by
  rw [forwardPairImpl_eq_pair P hP p q]
  simp [forwardImpl_correct P hP]

/-- Plan normalization agrees with `NTT.Inverse.normalize` for the same domain. -/
theorem normalize_eq_ntt_normalize (P : Plan R) (hP : WellFormed P) (a : Array R) :
    normalize P a = NTT.Inverse.normalize P.domain a := by
  rcases hP with ⟨_, hnInv, _⟩
  simp [normalize, NTT.Inverse.normalize, hnInv]

/-- A well-formed plan's inverse transform computes the inverse NTT spec. -/
theorem inverseImpl_correct (P : Plan R) (hP : WellFormed P) (v : Array R) :
    inverseImpl P (NTT.Transform.bitRevPermute P.domain v) =
      NTT.Inverse.inverseSpec P.domain v := by
  rcases hP with ⟨hinverseDomain, hnInv, htwiddles, hinverseTwiddles⟩
  rw [inverseImpl, hinverseDomain, hinverseTwiddles]
  rw [runStagesRadix4WithTwiddles_eq_ntt _ _ (by simp [NTT.Transform.bitRevPermute,
    NTT.Domain.inverse])]
  have hbit :
      NTT.Transform.bitRevPermute P.domain v =
        NTT.Transform.bitRevPermute P.domain.inverse v := by
    apply Array.ext
    · simp [NTT.Transform.bitRevPermute, NTT.Domain.inverse]
    · intro i hi₁ hi₂
      simp [NTT.Transform.bitRevPermute, NTT.Domain.inverse]
  rw [hbit]
  rw [normalize_eq_ntt_normalize P ⟨hinverseDomain, hnInv, htwiddles, hinverseTwiddles⟩]
  exact NTT.Inverse.inverseImpl_correct P.domain v

/-- Pointwise multiplication commutes with applying the bit-reversal permutation. -/
theorem pointwiseMul_bitRevPermute_forwardSpec_eq
    (D : NTT.Domain R) (p q : CPolynomial.Raw R) :
    pointwiseMul D
        (NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D p))
        (NTT.Transform.bitRevPermute D (NTT.Forward.forwardSpec D q)) =
      NTT.Transform.bitRevPermute D
        (NTT.FastMul.pointwiseMul D
          (NTT.Forward.forwardSpec D p) (NTT.Forward.forwardSpec D q)) := by
  apply Array.ext
  · simp [pointwiseMul, NTT.FastMul.pointwiseMul, NTT.Transform.bitRevPermute]
  · intro i hiLeft hiRight
    have hrev : NTT.Transform.bitRevNat D.logN i < D.n := by
      simpa [NTT.Domain.n] using NTT.Transform.bitRevNat_lt D.logN i
    have hrevPow : NTT.Transform.bitRevNat D.logN i < 2 ^ D.logN := by
      simpa [NTT.Domain.n] using hrev
    simp [pointwiseMul, NTT.FastMul.pointwiseMul, NTT.Transform.bitRevPermute,
      Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hrevPow]

namespace Raw

/-- The planned raw multiplication implementation computes the raw NTT multiplication spec. -/
theorem fastMulImpl_correct [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial.Raw R) :
    fastMulImpl P p q = NTT.FastMul.Raw.fastMulSpec P.domain p q := by
  rw [fastMulImpl, NTT.FastMul.Raw.fastMulSpec]
  rw [forwardPairImpl_correct P hP p q]
  simp only
  rw [pointwiseMul_bitRevPermute_forwardSpec_eq]
  rw [inverseImpl_correct P hP]

/-- The planned raw multiplication implementation trims to ordinary multiplication. -/
theorem fastMulImpl_trim_eq_mul [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial.Raw R)
    (hfit : NTT.Domain.fits P.domain p q) :
    (fastMulImpl P p q).trim = p * q := by
  rw [fastMulImpl_correct P hP p q]
  exact NTT.FastMul.Raw.fastMulSpec_trim_eq_mul P.domain p q hfit

end Raw

/-- The planned multiplication implementation computes the NTT multiplication spec. -/
theorem fastMulImpl_correct [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial R) :
    fastMulImpl P p q = NTT.FastMul.fastMulSpec P.domain p q := by
  apply CPolynomial.ext
  simp [fastMulImpl, NTT.FastMul.fastMulSpec, Raw.fastMulImpl_correct P hP]

/-- The planned multiplication implementation agrees with ordinary multiplication. -/
theorem fastMulImpl_eq_mul [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (p q : CPolynomial R)
    (hfit : NTT.Domain.fits P.domain p.val q.val) :
    fastMulImpl P p q = p * q := by
  rw [fastMulImpl_correct P hP p q]
  exact NTT.FastMul.fastMulSpec_eq_mul P.domain p q hfit

end Plan

namespace Raw

/-- The one-shot raw multiplication implementation computes the raw NTT multiplication spec. -/
theorem fastMulImpl_correct [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial.Raw R) :
    fastMulImpl D p q = NTT.FastMul.Raw.fastMulSpec D p q := by
  simpa [fastMulImpl] using
    Plan.Raw.fastMulImpl_correct (P := Plan.ofDomain D) (Plan.ofDomain_wellFormed D) p q

/-- The one-shot raw multiplication implementation trims to ordinary multiplication. -/
theorem fastMulImpl_trim_eq_mul [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial.Raw R)
    (hfit : NTT.Domain.fits D p q) :
    (fastMulImpl D p q).trim = p * q := by
  rw [fastMulImpl_correct D p q]
  exact NTT.FastMul.Raw.fastMulSpec_trim_eq_mul D p q hfit

end Raw

/-- The one-shot multiplication implementation computes the NTT multiplication spec. -/
theorem fastMulImpl_correct [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R) :
    fastMulImpl D p q = NTT.FastMul.fastMulSpec D p q := by
  simpa [fastMulImpl] using
    Plan.fastMulImpl_correct (P := Plan.ofDomain D) (Plan.ofDomain_wellFormed D) p q

/-- The one-shot multiplication implementation agrees with ordinary multiplication. -/
theorem fastMulImpl_eq_mul [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R)
    (hfit : NTT.Domain.fits D p.val q.val) :
    fastMulImpl D p q = p * q := by
  rw [fastMulImpl_correct D p q]
  exact NTT.FastMul.fastMulSpec_eq_mul D p q hfit

/-- The safe one-shot wrapper agrees with ordinary multiplication. -/
theorem safeFastMul_eq_mul [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R)
    (hfit : NTT.Domain.fits D p.val q.val) :
    safeFastMul D p q hfit = p * q := by
  exact fastMulImpl_eq_mul D p q hfit

end NTTFast
end CPolynomial
end CompPoly

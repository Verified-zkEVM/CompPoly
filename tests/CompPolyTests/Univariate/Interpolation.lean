/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Univariate.BatchEval.Interpolation
public meta import CompPoly.Univariate.ReedSolomon.GaoNTT
public meta import CompPolyTests.Univariate.NTT.Common

/-!
  # Fast Interpolation Tests

  Executable checks for subproduct-tree interpolation on arbitrary nodes, across the naive
  and NTT-backed contexts, and for Gao decoding on an NTT domain.
-/

public meta section

namespace CompPoly
namespace CPolynomial
namespace InterpolationTests

private abbrev F := _root_.KoalaBear.Field

private def xs : Array F := #[1, 2, 5, 7, 11, 13, 17]

private def ys : Array F := #[3, 1, 4, 1, 5, 9, 2]

/-! ### Subproduct-tree interpolation -/

#guard interpolateSubproduct MulContext.naive ModContext.naive xs ys ==
  CLagrange.interpolateArrays xs ys

#guard interpolateSubproduct (MulContext.ntt NTT.KoalaBear.bestDomainForLength?)
    (ModContext.reversalNtt NTT.KoalaBear.bestDomainForLength?) xs ys ==
  CLagrange.interpolateArrays xs ys

#guard (xs.zip ys).all fun (x, y) =>
  (interpolateSubproduct MulContext.naive ModContext.naive xs ys).eval x == y

-- Missing values default to zero, as in `interpolateArrays`.
#guard interpolateSubproduct MulContext.naive ModContext.naive xs #[3, 1] ==
  CLagrange.interpolateArrays xs #[3, 1]

#guard interpolateSubproduct MulContext.naive ModContext.naive #[] ys == 0

#guard interpolateSubproduct MulContext.naive ModContext.naive (#[4] : Array F) #[9] == C 9

/-! ### Gao decoding on an NTT domain -/

private def D : NTT.Domain F := NTT.TestCommon.testDomain8

private def msg : Vector F 3 := ⟨#[2, 7, 1], rfl⟩

private def codeword : Vector F D.n :=
  (ReedSolomon.encode (ReedSolomon.nttDomainToRS D) msg).cast (ReedSolomon.nttDomainToRS_n D)

private def received : Vector F D.n :=
  Vector.ofFn fun i =>
    if i.1 = 1 then codeword.get i + 1 else if i.1 = 6 then 0 else codeword.get i

#guard ReedSolomon.Gao.decodeNTT 3 D received == some (ReedSolomon.messagePoly msg)

#guard ReedSolomon.Gao.decodeNTT 3 D received ==
  ReedSolomon.Gao.decode 3 (ReedSolomon.nttDomainToRS D) (ReedSolomon.Gao.castToRS D received)

#guard ReedSolomon.Gao.decodePlan 3 (NTTFast.Plan.ofDomain D) received ==
  some (ReedSolomon.messagePoly msg)

end InterpolationTests
end CPolynomial
end CompPoly

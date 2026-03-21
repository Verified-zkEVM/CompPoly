/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
import CompPoly.Univariate.NTT.FastMul
import CompPoly.Fields.KoalaBear

/-!
  # Univariate NTT FastMul Tests

  Concrete executable checks for the temporary spec-backed NTT multiplication path.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace FastMul

def testLogN : Nat := 3

def testBits : Fin (KoalaBear.twoAdicity + 1) := ⟨testLogN, by decide⟩

def testDomain : Domain KoalaBear.Field where
  logN := testLogN
  omega := KoalaBear.twoAdicGenerators[testBits]
  primitive := by
    simpa [testLogN, testBits] using KoalaBear.isPrimitiveRoot_twoAdicGenerator testBits
  natCast_ne_zero := by
    change ((8 : Nat) : KoalaBear.Field) ≠ 0
    decide

def testLogN32 : Nat := 5

def testBits32 : Fin (KoalaBear.twoAdicity + 1) := ⟨testLogN32, by decide⟩

def testDomain32 : Domain KoalaBear.Field where
  logN := testLogN32
  omega := KoalaBear.twoAdicGenerators[testBits32]
  primitive := by
    simpa [testLogN32, testBits32] using KoalaBear.isPrimitiveRoot_twoAdicGenerator testBits32
  natCast_ne_zero := by
    change ((32 : Nat) : KoalaBear.Field) ≠ 0
    decide

def testLogN64 : Nat := 6

def testBits64 : Fin (KoalaBear.twoAdicity + 1) := ⟨testLogN64, by decide⟩

def testDomain64 : Domain KoalaBear.Field where
  logN := testLogN64
  omega := KoalaBear.twoAdicGenerators[testBits64]
  primitive := by
    simpa [testLogN64, testBits64] using KoalaBear.isPrimitiveRoot_twoAdicGenerator testBits64
  natCast_ne_zero := by
    change ((64 : Nat) : KoalaBear.Field) ≠ 0
    decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 4, 5]
    CompPoly.CPolynomial.NTT.Forward.forwardImpl testDomain p =
      CompPoly.CPolynomial.NTT.Forward.forwardSpec testDomain p := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 0, 0]
    CompPoly.CPolynomial.NTT.Forward.forwardImpl testDomain p =
      CompPoly.CPolynomial.NTT.Forward.forwardSpec testDomain p := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[
      (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
    ]
    CompPoly.CPolynomial.NTT.Forward.forwardImpl testDomain32 p =
      CompPoly.CPolynomial.NTT.Forward.forwardSpec testDomain32 p := by
  native_decide

example :
    let v : Array KoalaBear.Field := #[
      (1 : KoalaBear.Field), 4, 2, 7, 3, 6, 5, 8
    ]
    CompPoly.CPolynomial.NTT.Inverse.inverseImpl testDomain v =
      CompPoly.CPolynomial.NTT.Inverse.inverseSpec testDomain v := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 4, 5]
    let v := CompPoly.CPolynomial.NTT.Forward.forwardSpec testDomain p
    CompPoly.CPolynomial.NTT.Inverse.inverseImpl testDomain v =
      CompPoly.CPolynomial.NTT.Inverse.inverseSpec testDomain v := by
  native_decide

example :
    let v : Array KoalaBear.Field := #[
      (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7, 8,
      9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24,
      25, 26, 27, 28, 29, 30, 31, 32
    ]
    CompPoly.CPolynomial.NTT.Inverse.inverseImpl testDomain32 v =
      CompPoly.CPolynomial.NTT.Inverse.inverseSpec testDomain32 v := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(0 : KoalaBear.Field)]
    let q : CPolynomial.Raw KoalaBear.Field := #[(5 : KoalaBear.Field), 7, 9]
    fastMulImpl testDomain p q = p * q := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 4, 5]
    let q : CPolynomial.Raw KoalaBear.Field := #[(7 : KoalaBear.Field), 2]
    fastMulImpl testDomain p q = p * q := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 3, 4, 5]
    let q : CPolynomial.Raw KoalaBear.Field := #[(6 : KoalaBear.Field), 7, 8, 9]
    fastMulImpl testDomain p q = p * q := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 0, 0]
    let q : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 0, 4, 0]
    fastMulImpl testDomain p q = p * q := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 3, 4, 5, 6]
    let q : CPolynomial.Raw KoalaBear.Field := #[(7 : KoalaBear.Field), 8, 9, 10, 11]
    mulWithFastPath testDomain p q = p * q := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[
      (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
    ]
    let q : CPolynomial.Raw KoalaBear.Field := #[
      (11 : KoalaBear.Field), 10, 9, 8, 7, 6, 5, 4, 3, 2, 1
    ]
    fastMulImpl testDomain32 p q = p * q := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[
      (2 : KoalaBear.Field), 4, 6, 8, 10, 12, 14, 16,
      18, 20, 22, 24, 26, 28, 30, 32
    ]
    let q : CPolynomial.Raw KoalaBear.Field := #[
      (1 : KoalaBear.Field), 3, 5, 7, 9, 11, 13, 15,
      17, 19, 21, 23, 25, 27, 29, 31
    ]
    fastMulImpl testDomain32 p q = p * q := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[
      (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7,
      8, 9, 10, 11, 12, 13, 14,
      15, 16, 17, 18, 19, 20, 21
    ]
    let q : CPolynomial.Raw KoalaBear.Field := #[
      (21 : KoalaBear.Field), 20, 19, 18, 17, 16, 15,
      14, 13, 12, 11, 10, 9, 8,
      7, 6, 5, 4, 3, 2, 1
    ]
    fastMulImpl testDomain64 p q = p * q := by
  native_decide

end FastMul
end NTT
end CPolynomial
end CompPoly

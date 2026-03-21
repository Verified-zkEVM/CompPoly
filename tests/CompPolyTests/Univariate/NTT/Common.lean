/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Fields.KoalaBear

/-!
  # Univariate NTT Test Helpers

  Shared concrete KoalaBear domains used by the NTT test files.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace TestCommon

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

end TestCommon
end NTT
end CPolynomial
end CompPoly

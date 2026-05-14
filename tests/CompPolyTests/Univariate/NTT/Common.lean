/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.KoalaBear

/-!
  # Univariate NTT Test Helpers

  Shared concrete KoalaBear domains used by the NTT test files.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace TestCommon

def testBitsOfLogN (logN : Nat) (hlogN : logN ≤ _root_.KoalaBear.twoAdicity) :
    Fin (_root_.KoalaBear.twoAdicity + 1) :=
  CPolynomial.NTT.KoalaBear.bitsOfLogN logN hlogN

def testDomainOfLogN (logN : Nat) (hlogN : logN ≤ _root_.KoalaBear.twoAdicity) :
    Domain _root_.KoalaBear.Field :=
  CPolynomial.NTT.KoalaBear.domainOfLogN logN hlogN

def testDomain8 : Domain _root_.KoalaBear.Field :=
  testDomainOfLogN 3 (by decide)

def testDomain32 : Domain _root_.KoalaBear.Field :=
  testDomainOfLogN 5 (by decide)

def testDomain64 : Domain _root_.KoalaBear.Field :=
  testDomainOfLogN 6 (by decide)

end TestCommon
end NTT
end CPolynomial
end CompPoly

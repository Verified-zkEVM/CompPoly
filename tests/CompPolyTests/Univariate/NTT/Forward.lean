/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Forward
import CompPolyTests.Univariate.NTT.Common

/-!
  # Univariate NTT Forward Tests

  Concrete executable checks for the iterative butterfly forward NTT path.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace ForwardTests

open TestCommon

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 4, 5]
  let expected : Array KoalaBear.Field := #[
    12, 517011757, 2063859715, 1647565118,
    4, 1446577892, 66846714, 650258111
  ]
  Forward.forwardImpl testDomain p == expected

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 0, 0]
  let expected : Array KoalaBear.Field := #[
    3, 1365638292, 2097283076, 782003361,
    2130706432, 765068143, 33423359, 1348703074
  ]
  Forward.forwardImpl testDomain p == expected

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[
    (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
  ]
  let expected : Array KoalaBear.Field := #[
    66, 2128037983, 1386385011, 317825687,
    285219972, 1675575282, 723256402, 1870799833,
    2030436353, 422828684, 804733907, 974303083,
    1862421689, 645795420, 1126387232, 1800562034,
    6, 2126072758, 1518241107, 1742591062,
    1611522965, 1498208997, 616595096, 1360674089,
    100270068, 1985703746, 217819229, 1125521350,
    502248260, 1098774848, 2129407684, 533789490
  ]
  Forward.forwardImpl testDomain32 p == expected

end ForwardTests
end NTT
end CPolynomial
end CompPoly

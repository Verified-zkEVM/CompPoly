/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.FastMul
import CompPolyTests.Univariate.NTT.Common

/-!
  # Univariate NTT FastMul Tests

  Concrete executable checks for the temporary spec-backed NTT multiplication path.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace FastMulTests

open TestCommon

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(0 : KoalaBear.Field)]
  let q : CPolynomial.Raw KoalaBear.Field := #[(5 : KoalaBear.Field), 7, 9]
  FastMul.fastMulImpl testDomain p q == p * q

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 4, 5]
  let q : CPolynomial.Raw KoalaBear.Field := #[(7 : KoalaBear.Field), 2]
  FastMul.fastMulImpl testDomain p q == p * q

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 3, 4, 5]
  let q : CPolynomial.Raw KoalaBear.Field := #[(6 : KoalaBear.Field), 7, 8, 9]
  FastMul.fastMulImpl testDomain p q == p * q

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 0, 0]
  let q : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 0, 4, 0]
  FastMul.fastMulImpl testDomain p q == p * q

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 3, 4, 5, 6]
  let q : CPolynomial.Raw KoalaBear.Field := #[(7 : KoalaBear.Field), 8, 9, 10, 11]
  FastMul.fastMulImpl testDomain32 p q == p * q

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[
    (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
  ]
  let q : CPolynomial.Raw KoalaBear.Field := #[
    (11 : KoalaBear.Field), 10, 9, 8, 7, 6, 5, 4, 3, 2, 1
  ]
  FastMul.fastMulImpl testDomain32 p q == p * q

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[
    (2 : KoalaBear.Field), 4, 6, 8, 10, 12, 14, 16,
    18, 20, 22, 24, 26, 28, 30, 32
  ]
  let q : CPolynomial.Raw KoalaBear.Field := #[
    (1 : KoalaBear.Field), 3, 5, 7, 9, 11, 13, 15,
    17, 19, 21, 23, 25, 27, 29, 31
  ]
  FastMul.fastMulImpl testDomain32 p q == p * q

#guard
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
  FastMul.fastMulImpl testDomain64 p q == p * q

end FastMulTests
end NTT
end CPolynomial
end CompPoly

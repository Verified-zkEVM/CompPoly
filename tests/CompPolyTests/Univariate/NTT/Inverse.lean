/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Inverse
import CompPolyTests.Univariate.NTT.Common

/-!
  # Univariate NTT Inverse Tests

  Concrete executable checks for the iterative butterfly inverse NTT path.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace InverseTests

open TestCommon

#guard
  let v : Array KoalaBear.Field := #[
    (1 : KoalaBear.Field), 4, 2, 7, 3, 6, 5, 8
  ]
  let expected : Array KoalaBear.Field := #[
    1065353221, 1641696606, 1587585025, 758523484,
    1598029823, 2074505892, 10444799, 1917393316
  ]
  Inverse.inverseImpl testDomain8 v == expected

#guard
  let v : Array KoalaBear.Field := #[
    (12 : KoalaBear.Field), 517011757, 2063859715, 1647565118,
    4, 1446577892, 66846714, 650258111
  ]
  let expected : Array KoalaBear.Field := #[(3 : KoalaBear.Field), 4, 5, 0, 0, 0, 0, 0]
  Inverse.inverseImpl testDomain8 v == expected

#guard
  let v : Array KoalaBear.Field := #[
    (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32
  ]
  let expected : Array KoalaBear.Field := #[
    1065353233, 1056272652, 1228590511, 860044133,
    1061231181, 1527679415, 427698416, 1176438001,
    2122350593, 833475271, 402519128, 722641158,
    1077942860, 4647300, 1236834581, 729798062,
    1065353216, 1400908370, 893871851, 2126059132,
    1052763572, 1408065274, 1728187304, 1297231161,
    8355839, 954268431, 1703008016, 603027017,
    1069475251, 1270662299, 902115921, 1074433780
  ]
  Inverse.inverseImpl testDomain32 v == expected

end InverseTests
end NTT
end CPolynomial
end CompPoly

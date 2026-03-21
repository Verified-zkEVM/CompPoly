/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Inverse
import CompPolyTests.Univariate.NTT.Common

/-!
  # Univariate NTT Inverse Tests

  Concrete executable checks for the temporary spec-backed inverse NTT path.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace InverseTests

open TestCommon

example :
    let v : Array KoalaBear.Field := #[
      (1 : KoalaBear.Field), 4, 2, 7, 3, 6, 5, 8
    ]
    Inverse.inverseImpl testDomain v = Inverse.inverseSpec testDomain v := by
  native_decide

example :
    let p : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 4, 5]
    let v := Forward.forwardSpec testDomain p
    Inverse.inverseImpl testDomain v = Inverse.inverseSpec testDomain v := by
  native_decide

example :
    let v : Array KoalaBear.Field := #[
      (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7, 8,
      9, 10, 11, 12, 13, 14, 15, 16,
      17, 18, 19, 20, 21, 22, 23, 24,
      25, 26, 27, 28, 29, 30, 31, 32
    ]
    Inverse.inverseImpl testDomain32 v = Inverse.inverseSpec testDomain32 v := by
  native_decide

end InverseTests
end NTT
end CPolynomial
end CompPoly

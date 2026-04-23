/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Forward
import CompPolyTests.Univariate.NTT.Common

/-!
  # Univariate NTT Forward Tests

  Concrete executable checks for the temporary spec-backed forward NTT path.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace ForwardTests

open TestCommon

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(3 : KoalaBear.Field), 4, 5]
  Forward.forwardImpl testDomain p == Forward.forwardSpec testDomain p

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[(1 : KoalaBear.Field), 2, 0, 0]
  Forward.forwardImpl testDomain p == Forward.forwardSpec testDomain p

#guard
  let p : CPolynomial.Raw KoalaBear.Field := #[
    (1 : KoalaBear.Field), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
  ]
  Forward.forwardImpl testDomain32 p == Forward.forwardSpec testDomain32 p

end ForwardTests
end NTT
end CPolynomial
end CompPoly

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.Tower.Concrete.BasisCoordinates
import CompPoly.Fields.Binary.Tower.Concrete.CoordinateArithmetic

/-!
# Concrete binary tower import boundary

The concrete field, basis, coordinate, and quadratic arithmetic APIs must be usable without
loading the abstract tower construction.
-/

namespace CompPolyTests.ConcreteTowerImports

open Lean Elab Command in
run_cmd do
  for name in (← getEnv).header.moduleNames do
    if name.toString.startsWith "CompPoly.Fields.Binary.Tower.Abstract." then
      throwError "Concrete tower API imported an abstract tower module: {name}"

end CompPolyTests.ConcreteTowerImports

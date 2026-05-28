/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear

/-!
# KoalaBear GS Field-Root Tests

Executable coverage for canonical and fast KoalaBear finite-field root backends.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan

namespace GuruswamiSudan.Root.FieldRoots.KoalaBear

private def koalaPoly : CPolynomial _root_.KoalaBear.Field :=
  CPolynomial.linearFactor (3 : _root_.KoalaBear.Field) *
    CPolynomial.linearFactor (5 : _root_.KoalaBear.Field)

private def koalaRoots : Array _root_.KoalaBear.Field :=
  koalaBearFieldRootBackend.rootsInField koalaPoly

private def koalaNttRoots : Array _root_.KoalaBear.Field :=
  koalaBearNttFieldRootBackend.rootsInField koalaPoly

private def koalaNttFastRoots : Array _root_.KoalaBear.Field :=
  koalaBearNttFastFieldRootBackend.rootsInField koalaPoly

#guard (3 : _root_.KoalaBear.Field) ∈ koalaRoots.toList
#guard (5 : _root_.KoalaBear.Field) ∈ koalaRoots.toList
#guard koalaRoots.size = 2
#guard koalaNttRoots == koalaRoots
#guard koalaNttFastRoots == koalaRoots

private def fastKoalaPoly : CPolynomial _root_.KoalaBear.Fast.Field :=
  CPolynomial.linearFactor (3 : _root_.KoalaBear.Fast.Field) *
    CPolynomial.linearFactor (5 : _root_.KoalaBear.Fast.Field)

private def fastKoalaRoots : Array _root_.KoalaBear.Fast.Field :=
  fastKoalaBearFieldRootBackend.rootsInField fastKoalaPoly

private def fastKoalaNttRoots : Array _root_.KoalaBear.Fast.Field :=
  fastKoalaBearNttFieldRootBackend.rootsInField fastKoalaPoly

private def fastKoalaNttFastRoots : Array _root_.KoalaBear.Fast.Field :=
  fastKoalaBearNttFastFieldRootBackend.rootsInField fastKoalaPoly

#guard (3 : _root_.KoalaBear.Fast.Field) ∈ fastKoalaRoots.toList
#guard (5 : _root_.KoalaBear.Fast.Field) ∈ fastKoalaRoots.toList
#guard fastKoalaRoots.size = 2
#guard fastKoalaNttRoots == fastKoalaRoots
#guard fastKoalaNttFastRoots == fastKoalaRoots

end GuruswamiSudan.Root.FieldRoots.KoalaBear

end CompPolyTests

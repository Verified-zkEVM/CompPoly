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
  koalaBearFieldRootContext.rootsInField koalaPoly

private def koalaNttRoots : Array _root_.KoalaBear.Field :=
  koalaBearNttFieldRootContext.rootsInField koalaPoly

private def koalaNttFastRoots : Array _root_.KoalaBear.Field :=
  koalaBearNttFastFieldRootContext.rootsInField koalaPoly

#guard (3 : _root_.KoalaBear.Field) ∈ koalaRoots.toList
#guard (5 : _root_.KoalaBear.Field) ∈ koalaRoots.toList
#guard koalaRoots.size = 2
#guard koalaNttRoots == koalaRoots
#guard koalaNttFastRoots == koalaRoots

private def koalaCounterexampleA : _root_.KoalaBear.Field := (3446241 : Nat)

private def koalaCounterexampleB : _root_.KoalaBear.Field := (3750964 : Nat)

private def koalaCounterexamplePoly : CPolynomial _root_.KoalaBear.Field :=
  CPolynomial.linearFactor koalaCounterexampleA *
    CPolynomial.linearFactor koalaCounterexampleB

private def koalaCounterexampleRoots : Array _root_.KoalaBear.Field :=
  koalaBearFieldRootContext.rootsInField koalaCounterexamplePoly

private def koalaCounterexampleNttRoots : Array _root_.KoalaBear.Field :=
  koalaBearNttFieldRootContext.rootsInField koalaCounterexamplePoly

private def koalaCounterexampleNttFastRoots : Array _root_.KoalaBear.Field :=
  koalaBearNttFastFieldRootContext.rootsInField koalaCounterexamplePoly

#guard koalaCounterexampleA ∈ koalaCounterexampleRoots.toList
#guard koalaCounterexampleB ∈ koalaCounterexampleRoots.toList
#guard koalaCounterexampleRoots.size = 2
#guard koalaCounterexampleNttRoots == koalaCounterexampleRoots
#guard koalaCounterexampleNttFastRoots == koalaCounterexampleRoots

private def koalaZeroRootPoly : CPolynomial _root_.KoalaBear.Field :=
  CPolynomial.linearFactor (0 : _root_.KoalaBear.Field) *
    CPolynomial.linearFactor (7 : _root_.KoalaBear.Field)

private def koalaZeroRoots : Array _root_.KoalaBear.Field :=
  koalaBearFieldRootContext.rootsInField koalaZeroRootPoly

#guard (0 : _root_.KoalaBear.Field) ∈ koalaZeroRoots.toList
#guard (7 : _root_.KoalaBear.Field) ∈ koalaZeroRoots.toList
#guard koalaZeroRoots.size = 2

private def koalaRepeatedRootPoly : CPolynomial _root_.KoalaBear.Field :=
  CPolynomial.linearFactor (11 : _root_.KoalaBear.Field) *
    CPolynomial.linearFactor (11 : _root_.KoalaBear.Field) *
      CPolynomial.linearFactor (13 : _root_.KoalaBear.Field)

private def koalaRepeatedRoots : Array _root_.KoalaBear.Field :=
  koalaBearFieldRootContext.rootsInField koalaRepeatedRootPoly

#guard (11 : _root_.KoalaBear.Field) ∈ koalaRepeatedRoots.toList
#guard (13 : _root_.KoalaBear.Field) ∈ koalaRepeatedRoots.toList
#guard koalaRepeatedRoots.size = 2

private def koalaNoRootPoly : CPolynomial _root_.KoalaBear.Field :=
  CPolynomial.ofArray #[-_root_.KoalaBear.primitiveRoot, 0, 1]

#guard (koalaBearFieldRootContext.rootsInField koalaNoRootPoly).isEmpty

private def fastKoalaPoly : CPolynomial _root_.KoalaBear.Fast.Field :=
  CPolynomial.linearFactor (3 : _root_.KoalaBear.Fast.Field) *
    CPolynomial.linearFactor (5 : _root_.KoalaBear.Fast.Field)

private def fastKoalaRoots : Array _root_.KoalaBear.Fast.Field :=
  fastKoalaBearFieldRootContext.rootsInField fastKoalaPoly

private def fastKoalaNttRoots : Array _root_.KoalaBear.Fast.Field :=
  fastKoalaBearNttFieldRootContext.rootsInField fastKoalaPoly

private def fastKoalaNttFastRoots : Array _root_.KoalaBear.Fast.Field :=
  fastKoalaBearNttFastFieldRootContext.rootsInField fastKoalaPoly

#guard (3 : _root_.KoalaBear.Fast.Field) ∈ fastKoalaRoots.toList
#guard (5 : _root_.KoalaBear.Fast.Field) ∈ fastKoalaRoots.toList
#guard fastKoalaRoots.size = 2
#guard fastKoalaNttRoots == fastKoalaRoots
#guard fastKoalaNttFastRoots == fastKoalaRoots

end GuruswamiSudan.Root.FieldRoots.KoalaBear

end CompPolyTests

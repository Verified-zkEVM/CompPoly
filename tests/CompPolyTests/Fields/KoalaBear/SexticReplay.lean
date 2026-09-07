/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.KoalaBear.Ext6.SexticIrreducible
meta import Lean

/-!
# Sextic certificate replay

Recheck the imported proof body against its original statement with a fresh kernel checker.
The explicit import also makes Lake rerun this test when the certificate module changes.
-/

open Lean

run_elab do
  let env ← importModules #[{ module := `CompPoly.Fields.KoalaBear.Ext6.SexticIrreducible }]
    {} (trustLevel := 0) (loadExts := false) (level := .private)
  let some (.thmInfo info) := env.toKernelEnv.find? `KoalaBear.sexticPoly_irreducible
    | throwError "Missing sextic irreducibility proof"
  let declaration := Declaration.thmDecl {
    name := `CompPolyTests.KoalaBear.replayed_sextic_irreducible
    levelParams := info.levelParams
    type := info.type
    value := info.value }
  match env.toKernelEnv.addDeclCore 0 0 declaration none with
  | .ok _ => pure ()
  | .error error => throwError "Sextic kernel replay failed: {← error.toMessageData {} |>.toString}"

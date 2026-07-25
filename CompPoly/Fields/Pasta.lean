/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

import CompPoly.Fields.Pasta.Basic
import CompPoly.Fields.Pasta.Fast

/-!
# Pasta (Pallas / Vesta) fields

Facade module for the Pasta base fields.  It re-exports the canonical `ZMod` models with
their primality certificates from `CompPoly.Fields.Pasta.Basic` and the native-word
eight-limb Montgomery implementations from `CompPoly.Fields.Pasta.Fast`.
-/

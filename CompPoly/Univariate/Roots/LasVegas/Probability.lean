/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.Basic
import CompPoly.Univariate.Roots.LasVegas.Probability.Uniform
import CompPoly.Univariate.Roots.LasVegas.Probability.OddBuckets
import CompPoly.Univariate.Roots.LasVegas.Probability.OddTrial
import CompPoly.Univariate.Roots.LasVegas.Probability.EvenTrace
import CompPoly.Univariate.Roots.LasVegas.Probability.Repeated
import CompPoly.Univariate.Roots.LasVegas.Probability.Recursive

/-!
# Probability Surface for Las Vegas Root Splitting

Import facade for the PMF-based theorem surface of the randomized performance
story of the Las Vegas finite-field root splitter. The probability modules are
intentionally separate from the executable splitter modules: runtime root
search remains pure and deterministic for a fixed `ProbeFamily`, while these
modules model idealized uniform probes.

- `Probability.Basic`: event probabilities, uniform enumeration models, trial
  results, and small PMF mass lemmas.
- `Probability.Uniform`: uniform field-element, coefficient-array, and probe
  distributions, plus pair-evaluation uniformity.
- `Probability.OddBuckets`: Euler criterion bridge and bucket counting for the
  deterministic classifier in `LasVegas.OddBucket`.
- `Probability.OddTrial`: the single odd Cantor-Zassenhaus trial PMF, the
  half-success theorem for uniform probes, and the root-product adapters.
- `Probability.EvenTrace`: trace-fiber counting and the half-success and
  geometric fallback theorems for the characteristic-two trace branch.
- `Probability.Repeated`: repeated one-factor trials and geometric fallback
  bounds.
- `Probability.Recursive`: the abstract recursive fallback model, the
  multi-factor splitting process that witnesses it, and the binomial-tail
  bound on full recursive fallback.
-/

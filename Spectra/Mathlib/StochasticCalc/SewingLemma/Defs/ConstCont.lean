/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/Defs.lean
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic

open Real Set Filter

variable {E : Type*} [NormedAddCommGroup E]

namespace Spectra.Mathlib.StochCalc

section ContinuousControl

/-- A continuous super-additive control (standalone, not extending LipControl). -/
structure ContControl (ω : ℝ → ℝ → ℝ) (a b : ℝ) : Prop where
  /-- Nonnegativity. -/
  nonneg : ∀ s t, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω s t
  /-- Vanishes on diagonal. -/
  diag : ∀ s, ω s s = 0
  /-- Super-additivity. -/
  superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ω s u + ω u t ≤ ω s t
  /-- Continuity near the diagonal (uniform on `[a, b]`). -/
  cont_diag : ∀ ε > 0, ∃ δ > 0, ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    t - s < δ → ω s t < ε

end ContinuousControl

end Spectra.Mathlib.StochCalc

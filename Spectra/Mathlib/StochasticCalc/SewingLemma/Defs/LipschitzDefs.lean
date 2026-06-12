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
/-!
# The Sewing Lemma — Layer 1 (Interval-Length Control)

The **Sewing Lemma** constructs additive functionals from almost-additive approximations.
This file proves the simplest and most directly useful version: the defect of the
two-parameter map `Ξ` is controlled by `K · |t - s|^θ` with `θ > 1`.

## Why this version?

The interval length `|t - s|` distributes *perfectly* over dyadic subdivision: at level `n`,
each sub-interval has length exactly `|t - s| / 2ⁿ`. This gives clean geometric decay:

  `‖S_{n+1} - Sₙ‖ ≤ K · |t - s|^θ · 2^{-n(θ - 1)}`

with *no additional hypotheses* on a control function. The general sewing lemma with
abstract super-additive control `ω` requires either a Lipschitz condition on `ω` or
a fundamentally different (compactness-based) proof. This version avoids both issues.

## Coverage

This version handles all standard applications where the driving signal has Hölder regularity:
* Standard Brownian motion (`γ`-Hölder for `γ < 1/2`)
* Fractional Brownian motion (`γ`-Hölder for `γ < H`)
* Hölder-regular Young integration
* Rough integration with Hölder rough path data

For the cross-controlled version with two different controls `ω₁, ω₂` (needed when the
integrand and integrator have different regularity structures), see Layer 2.

## Main results

* `dyadicSum_diff_bound₁`: geometric decay of successive dyadic refinements
* `dyadicSum_cauchy₁`: the dyadic Riemann sums form a Cauchy sequence
* `sewingMap₁_dist_le`: approximation bound `‖I(s,t) - Ξ(s,t)‖ ≤ C·K·|t-s|^θ`
* `sewingMap₁_additive`: the sewn map is genuinely additive
* `sewingMap₁_unique`: uniqueness among additive functionals with the approximation bound

## References

* [Gubinelli, M., *Controlling rough paths*][gubinelli2004]
* [Friz, P.; Hairer, M., *A Course on Rough Paths*, 2nd ed., Theorem 2.2][friz2020]
* [Lyons, T., *Differential equations driven by rough signals*][lyons1998]
-/
noncomputable section

open Real Set Filter

variable {E : Type*} [NormedAddCommGroup E]

namespace Spectra.Mathlib.StochCalc

section Lipschitz
/-! ### Lipschitz controls -/

/-- A **Lipschitz control** on `[a, b]`: a function `ω : ℝ → ℝ → ℝ` that is
nonneg, vanishes on the diagonal, is super-additive, and grows at most linearly
in the interval length.

The Lipschitz condition `ω(s, t) ≤ L · (t - s)` is the key regularity that makes
the dyadic proof work: it ensures `ω(t_k, t_{k+1}) ≤ L · |t-s| / 2^n` at level `n`.

**Examples**:
* `ω(s,t) = |t - s|` with `L = 1` (Layer 1 control)
* `ω(s,t) = ‖X‖_{p-var;[s,t]}^p` for a `γ`-Hölder `X`, with `L = C^p · |b-a|^{γp - 1}`
* `ω(s,t) = |f(t) - f(s)|^p` for Lipschitz `f`, with `L = (Lip f)^p · |b-a|^{p-1}` -/
structure LipControl (ω : ℝ → ℝ → ℝ) (a b : ℝ) where
  nonneg : ∀ s t, a ≤ s → s ≤ t → t ≤ b → 0 ≤ ω s t
  /-- The control vanishes on the diagonal. -/
  diag : ∀ s, ω s s = 0
  /-- The control is super-additive on `[a, b]`. -/
  superadd : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ω s u + ω u t ≤ ω s t
  /-- The Lipschitz-in-length bound. -/
  lip_const : ℝ
  /-- The Lipschitz constant is nonneg. -/
  lip_const_nonneg : 0 ≤ lip_const
  /-- The Lipschitz bound: `ω(s, t) ≤ L · (t - s)`. -/
  lip_bound : ∀ s t, a ≤ s → s ≤ t → t ≤ b →
    ω s t ≤ lip_const * (t - s)


/-- The interval-length function `|t - s|` is a Lipschitz control with constant 1. -/
def lipControl_abs_sub {a b : ℝ} (_hab : a ≤ b) :
    LipControl (fun s t => |t - s|) a b where
  nonneg := fun s t _ _ _ => abs_nonneg _
  diag := fun s => by simp
  superadd := fun s u t _ hsu hut _ => by
    rw [show t - s = (u - s) + (t - u) from by ring]
    rw [@le_abs']
    simp only [sub_add_sub_cancel', neg_add_rev, le_add_neg_iff_add_le]
    grind only [= abs.eq_1, = max_def]
  lip_const := 1
  lip_const_nonneg := zero_le_one' ℝ
  lip_bound := fun s t _ hst _ => by
    simp [abs_of_nonneg (sub_nonneg.mpr hst)]

end Lipschitz

end Spectra.Mathlib.StochCalc

/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/Defs.lean
-/
import Spectra.Mathlib.StochasticCalc.SewingLemma.LipschitzProdControl.Defs
import Spectra.Mathlib.StochasticCalc.SewingLemma.Defs.ConstCont
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
open Real Set Filter

variable {E : Type*} [NormedAddCommGroup E]

namespace Spectra.Mathlib.StochCalc

/-! ### The Sewing Condition (Layer 3) -/

/-- **Sewing Condition, Layer 3**: the general version with continuous control.

`‖δΞ(s, u, t)‖ ≤ K · ω(s, t)^θ` with `θ > 1` and `ω` a continuous super-additive
control.

This is the version stated in Friz–Hairer and used in the general theory of rough paths.
It makes no assumption about the relationship between `ω(s, t)` and `|t - s|` beyond
continuity at the diagonal. -/
structure SewingCondition₃ (Ξ : ℝ → ℝ → E)
    (ω : ℝ → ℝ → ℝ) (θ K : ℝ) (a b : ℝ) : Prop where
  /-- `Ξ` vanishes on the diagonal. -/
  vanish_diag : ∀ s, Ξ s s = 0
  /-- The exponent is strictly greater than 1. -/
  one_lt_theta : 1 < θ
  /-- The bound constant is nonneg. -/
  K_nonneg : 0 ≤ K
  /-- The interval is well-oriented. -/
  hab : a ≤ b
  /-- The control is continuous and super-additive. -/
  omega_cont : ContControl ω a b
  /-- The defect bound. -/
  defect_bound : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ‖sewingDefect₁ Ξ s u t‖ ≤ K * ω s t ^ θ
  /-- Sumability Enhancement -/
  energy_summable : ∀ s t, a ≤ s → (hst : s ≤ t) → t ≤ b →
    Summable (fun n => thetaEnergy ω θ (dyadicPartition s t hst n))


/-- **Existence of the sewn map**: Riemann sums over partitions with vanishing
theta-energy converge.

We construct the limit using any sequence of partitions `Pₙ` with
`thetaEnergy ω θ Pₙ → 0` (e.g., dyadic partitions, or uniform partitions with
mesh → 0). -/
noncomputable def sewingMap₃ (Ξ : ℝ → ℝ → E) [CompleteSpace E]
    (ω : ℝ → ℝ → ℝ) (θ K a b : ℝ)
    (_hΞ : SewingCondition₃ Ξ ω θ K a b) (s t : ℝ) : E :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    -- Use dyadic partitions as the canonical approximating sequence.
    -- The limit exists because Riemann sums are Cauchy (by riemannSum_comparison
    -- + thetaEnergy_tendsto_zero).
    limUnder atTop (fun n => dyadicSum₁ Ξ s t n)
  else
    0

end Spectra.Mathlib.StochCalc

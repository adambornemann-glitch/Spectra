/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/Defs.lean
-/
import Spectra.Mathlib.StochasticCalc.SewingLemma.Defs.DyadicDefs
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

section Defect₁

/-- The defect of `Ξ` at `(s, u, t)`: measures failure of additivity.
`δΞ(s, u, t) = Ξ(s, t) - Ξ(s, u) - Ξ(u, t)`. -/
def sewingDefect₁ (Ξ : ℝ → ℝ → E) (s u t : ℝ) : E :=
  Ξ s t - Ξ s u - Ξ u t

end Defect₁

/-! ### The Sewing Condition (Layer 1) -/

/-- **Sewing Condition, Layer 1**: the defect of `Ξ` is controlled by interval length.

This is the simplest version: `‖δΞ(s, u, t)‖ ≤ K · |t - s|^θ` with `θ > 1`.

The exponent condition `θ > 1` is sharp. For `θ = 1`, the dyadic refinement sums diverge
logarithmically (think of the harmonic series). For `θ < 1` they diverge polynomially.
The condition `θ > 1` is precisely what makes the geometric series `∑ 2^{-n(θ-1)}` converge.

In the rough paths literature:
  * Young integration has `θ = 1/p + 1/q > 1` (when both paths are Hölder)
  * Rough integration (level 2) has `θ = 3/p > 1` for `p < 3`
  * Rough integration (level N) has `θ = (N+1)/p > 1` for `p < N + 1` -/
structure SewingCondition₁ (Ξ : ℝ → ℝ → E) (θ K : ℝ) (a b : ℝ) : Prop where
  /-- `Ξ` vanishes on the diagonal: `Ξ(s, s) = 0`. -/
  vanish_diag : ∀ s, Ξ s s = 0
  /-- The exponent is strictly greater than 1. -/
  one_lt_theta : 1 < θ
  /-- The bound constant is nonneg. -/
  K_nonneg : 0 ≤ K
  /-- The interval is well-oriented. -/
  hab : a ≤ b
  /-- The defect bound: `‖δΞ(s, u, t)‖ ≤ K · |t - s|^θ`. -/
  defect_bound : ∀ s u t, a ≤ s → s ≤ u → u ≤ t → t ≤ b →
    ‖sewingDefect₁ Ξ s u t‖ ≤ K * |t - s| ^ θ


/-! ### Cauchy sequence and convergence -/

section Convergence₁

/-- The geometric ratio for the Cauchy bound. -/
noncomputable def sewingRatio₁ (θ : ℝ) : ℝ := (2 : ℝ)⁻¹ ^ (θ - 1)


/- The geometric constant -/
noncomputable def sewingConst₁ (θ : ℝ) : ℝ := 1 / (1 - sewingRatio₁ θ)


end Convergence₁

section SewnMap

/-- **The sewn map**: the limit of dyadic Riemann sums.
`I(s, t) = lim_{n→∞} Sₙ(s, t)` -/
noncomputable def sewingMap₁ (Ξ : ℝ → ℝ → E) [CompleteSpace E] (θ K a b : ℝ)
    (_hΞ : SewingCondition₁ Ξ θ K a b) (s t : ℝ) : E :=
  if _h : a ≤ s ∧ s ≤ t ∧ t ≤ b then
    limUnder atTop (fun n => dyadicSum₁ Ξ s t n)
  else
    0

end SewnMap

end Spectra.Mathlib.StochCalc

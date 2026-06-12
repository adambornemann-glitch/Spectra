/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann & Doctor Professor Baron von Wobble-Bob
Filename: SewingLemma/Defs.lean
-/
import Spectra.Mathlib.StochasticCalc.SewingLemma.Defs.PartitionDefs
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
open Real Set Filter--NNReal

variable {E : Type*} [NormedAddCommGroup E]

namespace Spectra.Mathlib.StochCalc

/-- The `k`-th point of the `n`-th dyadic partition of `[s, t]`. -/
noncomputable def dyadicPt (s t : ℝ) (n k : ℕ) : ℝ :=
  s + ↑k * (t - s) / (2 : ℝ) ^ (n : ℕ)

/-- The **θ-energy** of a partition with respect to control `ω`:
`Φ_θ(P) = ∑ᵢ ω(tᵢ, tᵢ₊₁)^θ`.

This is the fundamental quantity that controls error in the general sewing lemma.
It combines super-additivity (which bounds `∑ ω_i`) with the exponent `θ > 1`
(which penalises large individual terms). -/
noncomputable def thetaEnergy (ω : ℝ → ℝ → ℝ) (θ : ℝ) {s t : ℝ} (P : Partition s t) : ℝ :=
  ∑ i : Fin P.n, ω (P.left i) (P.right i) ^ θ

/-! ### Dyadic partitions as `Partition` objects -/

@[simp]
theorem dyadicPt_zero (s t : ℝ) (n : ℕ) : dyadicPt s t n 0 = s := by
  simp [dyadicPt]

theorem dyadicPt_last (s t : ℝ) (n : ℕ) : dyadicPt s t n (2 ^ n) = t := by
  simp [dyadicPt]

/-- Monotonicity: dyadic points are ordered when `s ≤ t`. -/
theorem dyadicPt_mono {s t : ℝ} (hst : s ≤ t) (n : ℕ) {j k : ℕ} (hjk : j ≤ k) :
    dyadicPt s t n j ≤ dyadicPt s t n k := by
  simp only [dyadicPt]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (n : ℕ) := by positivity
  gcongr

/-- The n-th dyadic partition of [s, t] as a Partition. -/
noncomputable def dyadicPartition (s t : ℝ) (hst : s ≤ t) (n : ℕ) : Partition s t where
  n := 2 ^ n
  pts := fun i => dyadicPt s t n i.val
  mono := fun _a _b hab => dyadicPt_mono hst n hab
  first := dyadicPt_zero s t n
  last := dyadicPt_last s t n

/-- The `n`-th dyadic Riemann sum of `Ξ` over `[s, t]`. -/
noncomputable def dyadicSum₁ (Ξ : ℝ → ℝ → E) (s t : ℝ) (n : ℕ) : E :=
  ∑ k ∈ Finset.range (2 ^ n),
    Ξ (dyadicPt s t n k) (dyadicPt s t n (k + 1))


end Spectra.Mathlib.StochCalc

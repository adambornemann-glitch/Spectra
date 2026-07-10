/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Basic definitions for resolvent theory

Foundational definitions for resolvent theory: the type `OffRealAxis` of complex numbers off the
real axis, and the Neumann series machinery for inverting `1 - T` when `‖T‖ < 1`. This is the
bottom of the `Resolvent` hierarchy: `Analytic.lean`, `Identities.lean`, and everything built on
top of them reduce the local invertibility of `A - z` to the Neumann series constructed here.

## Main definitions

* `OffRealAxis` — complex numbers with nonzero imaginary part.
* `neumannSeries` — the limit `∑_{k=0}^∞ Tᵏ` for `‖T‖ < 1`.

## Main statements

* `opNorm_pow_le` — submultiplicativity `‖Tⁿ‖ ≤ ‖T‖ⁿ` of the operator norm.
* `opNorm_pow_tendsto_zero` — `‖Tⁿ‖ → 0` when `‖T‖ < 1`.
* `neumannSeries_summable` / `tsum_eq_neumannSeries` — the series `∑ Tⁿ` is summable with sum
  `neumannSeries T`.
* `neumannSeries_hasSum` — the series `∑ Tⁿ` converges to `neumannSeries T`.
* `neumannSeries_mul_left` / `neumannSeries_mul_right` — `1 - T` and `neumannSeries T` are
  two-sided inverses.
* `isUnit_one_sub` — `1 - T` is a unit when `‖T‖ < 1`.
* `im_ne_zero_of_near` — the off-axis condition `z.im ≠ 0` is open: any point close enough to a
  fixed off-axis `z₀` is itself off-axis. Feeds the power-series expansion of the resolvent around
  `z₀` in `Resolvent/Analytic.lean`, the sole consumer of this lemma.

## Implementation notes

`neumannSeries` is built from `Units.oneSub T hT : (E →L[ℂ] E)ˣ`, mathlib's ready-made unit witness
for `1 - T` when `‖T‖ < 1`, rather than from the `Ring.inverse`-based route
(`hasSum_geom_series_inverse`/`geom_series_eq_inverse`) that scalar geometric series use. That
route needs a (possibly noncommutative) `DivisionRing`/`Inv` structure on the ambient ring; the
operator ring `E →L[ℂ] E` has no such `Inv` in general (most operators aren't invertible), so the
unit-based construction is the only one available here.

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section IV.1
-/
open Complex Filter Topology
namespace Spectra.Resolvent

/-! ## Spectral Region Types -/

/-- Complex numbers with nonzero imaginary part (complement of the real axis). -/
def OffRealAxis : Type := {z : ℂ // z.im ≠ 0}

/-! ## Neumann Series -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Operator-norm submultiplicativity of powers: `‖Tⁿ‖ ≤ ‖T‖ⁿ`. -/
lemma opNorm_pow_le (T : E →L[ℂ] E) (n : ℕ) : ‖T^n‖ ≤ ‖T‖^n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    calc ‖T^(n+1)‖
        = ‖T^n * T‖ := by rw [pow_succ]
      _ ≤ ‖T^n‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖^n * ‖T‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = ‖T‖^(n+1) := by rw [pow_succ]

omit [CompleteSpace E] in
/-- For `‖T‖ < 1`, the operator norms `‖Tⁿ‖` tend to `0`. -/
lemma opNorm_pow_tendsto_zero (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Tendsto (fun n => ‖T^n‖) atTop (𝓝 0) := by
  have h_geom : Tendsto (fun n => ‖T‖^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rwa [norm_norm])
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => opNorm_pow_le T n) h_geom

/-- The **Neumann series** `∑_{k=0}^∞ Tᵏ = (1 - T)⁻¹` for `‖T‖ < 1`,
realized as the inverse of the unit `1 - T`. -/
noncomputable def neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : E →L[ℂ] E :=
  ↑(Units.oneSub T hT)⁻¹

/-- For `‖T‖ < 1`, the geometric series `∑ Tⁿ` is summable. A direct specialization of mathlib's
`summable_geometric_of_norm_lt_one` to the operator norm. -/
lemma neumannSeries_summable (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Summable (fun n => T ^ n) :=
  summable_geometric_of_norm_lt_one hT

/-- The sum `∑' n, Tⁿ` equals `neumannSeries T`. -/
lemma tsum_eq_neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    ∑' n, T ^ n = neumannSeries T hT := rfl

/-- The series `∑ Tⁿ` has sum `neumannSeries T` for `‖T‖ < 1`. -/
lemma neumannSeries_hasSum (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    HasSum (fun n => T ^ n) (neumannSeries T hT) := by
  rw [← tsum_eq_neumannSeries T hT]
  exact (neumannSeries_summable T hT).hasSum

/-- `(1 - T) · neumannSeries T = 1`: the Neumann series left-inverts `1 - T`. -/
lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E :=
  (Units.oneSub T hT).mul_inv

/-- `neumannSeries T · (1 - T) = 1`: the Neumann series right-inverts `1 - T`. -/
lemma neumannSeries_mul_right (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T) = ContinuousLinearMap.id ℂ E :=
  (Units.oneSub T hT).inv_mul

/-- **`1 - T` is a unit** when `‖T‖ < 1`. A direct specialization of mathlib's
`isUnit_one_sub_of_norm_lt_one` to the operator norm. -/
lemma isUnit_one_sub (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    IsUnit (ContinuousLinearMap.id ℂ E - T) :=
  isUnit_one_sub_of_norm_lt_one hT

/-! ## Auxiliary Lemmas -/

/-- The **off-axis condition is open**: a point within `|z₀.im|` of `z₀` also has nonzero
imaginary part. -/
lemma im_ne_zero_of_near {z₀ : ℂ} {z : ℂ}
    (hz : ‖z - z₀‖ < |z₀.im|) : z.im ≠ 0 := by
  have h_im_diff : |z.im - z₀.im| ≤ ‖z - z₀‖ := abs_im_le_norm (z - z₀)
  have h_im_close : |z.im - z₀.im| < |z₀.im| := lt_of_le_of_lt h_im_diff hz
  intro hz_eq
  simp [hz_eq] at h_im_close

end Spectra.Resolvent

/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Resolvent/Basic.lean
-/
import Spectra.UnitaryEvolution.BochnerIntegration.Resolvent
/-!
# Basic Definitions for Resolvent Theory

This file provides foundational definitions and tools for resolvent theory:
* Types for spectral regions (`OffRealAxis`, `UpperHalfPlane`, `LowerHalfPlane`)
* Neumann series machinery for inverting `(1 - T)` when `‖T‖ < 1`

## Main definitions

* `OffRealAxis`: Complex numbers with nonzero imaginary part
* `UpperHalfPlane`: Complex numbers with positive imaginary part
* `LowerHalfPlane`: Complex numbers with negative imaginary part
* `neumannPartialSum`: Partial sums `∑_{k<n} Tᵏ`
* `neumannSeries`: The limit `∑_{k=0}^∞ Tᵏ` for `‖T‖ < 1`

## Main statements

* `neumannSeries_mul_left`: `(1 - T) * neumannSeries T = 1`
* `neumannSeries_mul_right`: `neumannSeries T * (1 - T) = 1`
* `isUnit_one_sub`: `(1 - T)` is a unit when `‖T‖ < 1`
* `neumannSeries_hasSum`: The series `∑ Tⁿ` converges to `neumannSeries T`

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section IV.1
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology

/-! ## Spectral Region Types -/

/-- Complex numbers with nonzero imaginary part (complement of the real axis). -/
def OffRealAxis : Type := {z : ℂ // z.im ≠ 0}

/-! ## Neumann Series -/

-- (`opNorm_pow_le` and `opNorm_pow_tendsto_zero` stay above, unchanged —
--  keep them; they're likely used elsewhere and don't depend on completeness.)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma opNorm_pow_le (T : E →L[ℂ] E) (n : ℕ) : ‖T^n‖ ≤ ‖T‖^n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    calc ‖T^(n+1)‖
        = ‖T^n * T‖ := by rw [pow_succ]
      _ ≤ ‖T^n‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖^n * ‖T‖ := by
          apply mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = ‖T‖^(n+1) := by rw [pow_succ]

omit [CompleteSpace E] in
lemma opNorm_pow_tendsto_zero (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Tendsto (fun n => ‖T^n‖) atTop (𝓝 0) := by
  have h_geom : Tendsto (fun n => ‖T‖^n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_norm]
    exact hT
  have h_bound : ∀ n, ‖T^n‖ ≤ ‖T‖^n := fun n => opNorm_pow_le T n
  have h_nonneg : ∀ n, 0 ≤ ‖T^n‖ := fun n => norm_nonneg _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_geom h_nonneg h_bound

/-- Partial sums of the Neumann series `∑_{k<n} Tᵏ`. -/
noncomputable def neumannPartialSum (T : E →L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  Finset.sum (Finset.range n) (fun k => T^k)

/-- The Neumann series `∑_{k=0}^∞ Tᵏ = (1 - T)⁻¹` for `‖T‖ < 1`,
realized as the inverse of the unit `1 - T`. -/
noncomputable def neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : E →L[ℂ] E :=
  ↑(Units.oneSub T hT)⁻¹

lemma neumannSeries_summable (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    Summable (fun n => T ^ n) :=
  summable_geometric_of_norm_lt_one hT

lemma tsum_eq_neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    ∑' n, T ^ n = neumannSeries T hT := rfl

lemma neumannSeries_hasSum (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    HasSum (fun n => T ^ n) (neumannSeries T hT) := by
  rw [← tsum_eq_neumannSeries T hT]
  exact (neumannSeries_summable T hT).hasSum

lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E :=
  (Units.oneSub T hT).mul_inv

lemma neumannSeries_mul_right (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    neumannSeries T hT * (ContinuousLinearMap.id ℂ E - T) = ContinuousLinearMap.id ℂ E :=
  (Units.oneSub T hT).inv_mul

lemma isUnit_one_sub (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    IsUnit (ContinuousLinearMap.id ℂ E - T) :=
  isUnit_one_sub_of_norm_lt_one hT

/-! ## Auxiliary Lemmas -/

lemma im_ne_zero_of_near {z₀ : ℂ} (_ : z₀.im ≠ 0) {z : ℂ}
    (hz : ‖z - z₀‖ < |z₀.im|) : z.im ≠ 0 := by
  have h_im_diff : |z.im - z₀.im| ≤ ‖z - z₀‖ := abs_im_le_norm (z - z₀)
  have h_im_close : |z.im - z₀.im| < |z₀.im| := lt_of_le_of_lt h_im_diff hz
  intro hz_eq
  rw [hz_eq, zero_sub, abs_neg] at h_im_close
  exact lt_irrefl _ h_im_close

end QuantumMechanics.Resolvent

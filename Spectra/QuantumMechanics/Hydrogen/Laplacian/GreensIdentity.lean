/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Green's identity for radial functions with a Kato cusp

Infrastructure for the **reverse direction** of `hydrogen_discrete_spectrum` (`ℓ = 0`, `Z = 1`).

The transported `s`-state eigenfunction is the purely radial `f(x) = c·R_{n0}(‖x‖)`: continuous
everywhere, `C^∞` away from the origin, but with the **Kato cusp** at `x = 0` (`∇f` is bounded
but discontinuous there).  To establish `MemSobolevH2 f` and compute its weak Laplacian we use
the Fourier characterisation `memSobolevH2_of_fourier_decay`, which requires
`(1 + ‖ξ‖²)·𝓕f ∈ L²`.  That reduces to the distributional **Green's identity**

  `∫ f·(Δφ) = ∫ (Δf)·φ`   for all test functions `φ`,

with no Dirac delta at the origin (the gradient is bounded, so the single point carries no `H¹`
capacity).  The identity is proved by a smooth cutoff: multiply by `χ_ε` vanishing near the
origin, apply the classical integration by parts, and let `ε → 0`; the cutoff shell terms vanish
because `f` and `∇f` are bounded near `0`, against the `O(1/ε)`-and-`O(1/ε²)` cutoff derivatives
on a shell of volume `O(ε³)`.

## This file (so far)

The **1-D cutoff profile** `cutoffP` (`0` on `(-∞,1]`, `1` on `[2,∞)`, `C³`, valued in `[0,1]`)
with globally bounded first and second derivatives (compactly supported in `[1,2]`).  The radial
cutoff is `χ_ε(x) = cutoffP(‖x‖/ε)`, whose gradient and Laplacian are then `O(1/ε)` and `O(1/ε²)`.
-/

noncomputable section

namespace Spectra.QuantumMechanics.Hydrogen

open MeasureTheory Real

/-! ## The 1-D cutoff profile -/

/-- The 1-D cutoff profile: `0` on `(-∞,1]`, `1` on `[2,∞)`, `C^∞`, valued in `[0,1]`. -/
def cutoffP : ℝ → ℝ := fun t => Real.smoothTransition (t - 1)

lemma cutoffP_contDiff : ContDiff ℝ 3 cutoffP := by
  have h1 : ContDiff ℝ 3 (fun t : ℝ => t - 1) := by fun_prop
  exact Real.smoothTransition.contDiff.comp h1

lemma cutoffP_eq_zero {t : ℝ} (ht : t ≤ 1) : cutoffP t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma cutoffP_eq_one {t : ℝ} (ht : 2 ≤ t) : cutoffP t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma cutoffP_nonneg (t : ℝ) : 0 ≤ cutoffP t := Real.smoothTransition.nonneg _

lemma cutoffP_le_one (t : ℝ) : cutoffP t ≤ 1 := Real.smoothTransition.le_one _

lemma deriv_cutoffP_continuous : Continuous (deriv cutoffP) :=
  cutoffP_contDiff.continuous_deriv (by norm_num)

/-- The derivative of the profile is supported in `[1,2]`. -/
lemma deriv_cutoffP_support : Function.support (deriv cutoffP) ⊆ Set.Icc 1 2 := by
  intro t ht
  by_contra hmem
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  apply ht
  rcases hmem with h | h
  · have : cutoffP =ᶠ[nhds t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      exact cutoffP_eq_zero (le_of_lt hs)
    rw [this.deriv_eq, deriv_const']
  · have : cutoffP =ᶠ[nhds t] (fun _ => 1) := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      exact cutoffP_eq_one (le_of_lt hs)
    rw [this.deriv_eq, deriv_const']

lemma hasCompactSupport_deriv_cutoffP : HasCompactSupport (deriv cutoffP) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1:ℝ)) (b := 2))
    deriv_cutoffP_support

/-- The profile derivative is globally bounded. -/
lemma deriv_cutoffP_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv cutoffP t| ≤ M := by
  obtain ⟨M, hM⟩ := deriv_cutoffP_continuous.bounded_above_of_compact_support
    hasCompactSupport_deriv_cutoffP
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  have := hM t
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma deriv2_cutoffP_continuous : Continuous (deriv (deriv cutoffP)) :=
  (cutoffP_contDiff.deriv' (n := 2)).continuous_deriv (by norm_num)

/-- The second derivative of the profile is supported in `[1,2]`. -/
lemma deriv2_cutoffP_support : Function.support (deriv (deriv cutoffP)) ⊆ Set.Icc 1 2 := by
  intro t ht
  by_contra hmem
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  apply ht
  rcases hmem with h | h
  · have hconst : deriv cutoffP =ᶠ[nhds t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      have : cutoffP =ᶠ[nhds s] (fun _ => 0) := by
        filter_upwards [Iio_mem_nhds hs] with u hu
        exact cutoffP_eq_zero (le_of_lt hu)
      rw [this.deriv_eq, deriv_const']
    rw [hconst.deriv_eq, deriv_const']
  · have hconst : deriv cutoffP =ᶠ[nhds t] (fun _ => 0) := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      have : cutoffP =ᶠ[nhds s] (fun _ => 1) := by
        filter_upwards [Ioi_mem_nhds hs] with u hu
        exact cutoffP_eq_one (le_of_lt hu)
      rw [this.deriv_eq, deriv_const']
    rw [hconst.deriv_eq, deriv_const']

lemma hasCompactSupport_deriv2_cutoffP : HasCompactSupport (deriv (deriv cutoffP)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1:ℝ)) (b := 2))
    deriv2_cutoffP_support

/-- The profile second derivative is globally bounded. -/
lemma deriv2_cutoffP_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv (deriv cutoffP) t| ≤ M := by
  obtain ⟨M, hM⟩ := deriv2_cutoffP_continuous.bounded_above_of_compact_support
    hasCompactSupport_deriv2_cutoffP
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  have := hM t
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

end Spectra.QuantumMechanics.Hydrogen

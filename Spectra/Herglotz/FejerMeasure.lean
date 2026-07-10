/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Herglotz.FejerMeans

/-!
# The Fejér mean measure

Packages the Fejér mean density `fejerMeanDensity` from `Herglotz.FejerMeans` into an honest
`MeasureTheory.Measure ℝ`: `σ_N = (1/2π) · F_N(θ) dθ` on `[0, 2π)`, and proves its core structural
facts — total mass `‖ψ‖²` and the weight's limiting behaviour `w_N(n) → 1`.

## Main definitions

* `fejerMeasure`: the measure `σ_N = (1/2π) F_N(θ) dθ` on `[0, 2π)`.

## Main results

* `fejerMeasure_total`: `σ_N([0, 2π)) = ‖ψ‖²`.
* `fejerWeight_tendsto` / `fejerWeight_tendsto_complex`: `w_N(n) → 1` as `N → ∞`.

## References

* See `PositiveDefinite/Unitary.lean` for the Herglotz-theorem programme this file is a step of.
-/

open Complex MeasureTheory Topology
open Spectra.PositiveDefinite
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Herglotz

variable (U : H →L[ℂ] H) (hU : Operator.Unitary U)

/-- The **Fejér mean measure** on `𝕋 ≅ [0, 2π)`:
`σ_N = (1/2π) F_N(θ) dθ`.

Unitarity of `U` is not needed to construct the measure itself (only for its downstream
properties, e.g. non-negativity feeding `fejerMeasure_total`), so it is not a parameter here. -/
noncomputable def fejerMeasure (ψ : H) (N : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 (2 * Real.pi))).withDensity
    (fun θ => ENNReal.ofReal ((1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re))

/-- The Fejér mean density is continuous. -/
lemma fejerMeanDensity_continuous (ψ : H) (N : ℕ) :
    Continuous (fejerMeanDensity U ψ N) := by
  unfold fejerMeanDensity
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

/-- Total mass of the Fejér mean measure: `σ_N(𝕋) = ‖ψ‖²`. -/
lemma fejerMeasure_total (hU : Operator.Unitary U) (ψ : H) (N : ℕ) :
    (fejerMeasure U ψ N (Set.Icc 0 (2 * Real.pi))).toReal = ‖ψ‖ ^ 2 := by
  set S := Set.Icc (0 : ℝ) (2 * Real.pi) with _hS
  set f := fun θ : ℝ => (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re with hf_def
  -- Non-negativity of density
  have hf_nn : ∀ θ, 0 ≤ f θ := by
    intro θ; simp only [hf_def]
    exact mul_nonneg (by positivity) (fejerMeanDensity_nonneg U hU ψ N θ)
  -- Continuity / integrability of density
  have hf_cts : Continuous f :=
    continuous_const.mul (Complex.continuous_re.comp (fejerMeanDensity_continuous U ψ N))
  have hf_int : IntegrableOn f S volume :=
    hf_cts.continuousOn.integrableOn_compact isCompact_Icc
  -- Step 1: Unfold and simplify the measure
  unfold fejerMeasure
  rw [withDensity_apply (fun θ => ENNReal.ofReal (1 / (2 * Real.pi) *
        (fejerMeanDensity U ψ N θ).re)) measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, Set.inter_self]
  -- Step 2: Convert lintegral to Bochner integral
  rw [← ofReal_integral_eq_lintegral_ofReal hf_int (ae_of_all _ hf_nn),
      ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_of_all _ (fun θ => hf_nn θ)))]
  -- Step 3: Pull out 1/(2π)
  rw [show f = fun θ => (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re from rfl,
      integral_const_mul]
  -- Step 4: Commute re and ∫ via ContinuousLinearMap.integral_comp_comm
  have hF_int : IntegrableOn (fejerMeanDensity U ψ N) S volume :=
    (fejerMeanDensity_continuous U ψ N).continuousOn.integrableOn_compact isCompact_Icc
  rw [show (fun θ => (fejerMeanDensity U ψ N θ).re) =
      (fun θ => Complex.reCLM (fejerMeanDensity U ψ N θ)) from rfl]
  -- reCLM commutes with set integral (term-mode to avoid notation issues)
  rw [show (∫ θ in S, Complex.reCLM (fejerMeanDensity U ψ N θ)) =
      Complex.reCLM (∫ θ in S, fejerMeanDensity U ψ N θ)
      from ContinuousLinearMap.integral_comp_comm _ hF_int]
  rw [fejerMeanDensity_integral U ψ N]
  -- Step 5: Simplify: (1/2π) * re(2π * c(0)) = re(c(0)) = ‖ψ‖²
  rw [unitaryCorrelation_zero]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
             mul_zero, sub_zero, Complex.ofReal_re]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  field_simp; abel

/-- The Fejér weight converges pointwise to 1: `w_N(n) → 1` as `N → ∞`. -/
lemma fejerWeight_tendsto (n : ℤ) :
    Filter.Tendsto (fun N : ℕ => fejerWeight N n) Filter.atTop (𝓝 1) := by
  -- Step 1: Eventually w_N(n) = 1 - |n|/(N+1)
  have h_ev : (fun N : ℕ => fejerWeight N n) =ᶠ[Filter.atTop]
      (fun N : ℕ => 1 - ↑n.natAbs / (↑N + 1 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop n.natAbs] with N hN
    simp only [fejerWeight, if_pos hN]
  rw [Filter.tendsto_congr' h_ev]
  -- Step 2: (↑N + 1 : ℝ) → atTop
  have h_atTop : Filter.Tendsto (fun N : ℕ => (↑N + 1 : ℝ))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr; intro b
    filter_upwards [Filter.eventually_ge_atTop ⌈b⌉₊] with N hN
    calc b ≤ ↑⌈b⌉₊ := Nat.le_ceil b
      _ ≤ ↑N := by exact_mod_cast hN
      _ ≤ ↑N + 1 := le_add_of_nonneg_right zero_le_one
  -- Step 3: |n|/(N+1) → 0  (constant / atTop → 0)
  have h_div : Filter.Tendsto (fun N : ℕ => (↑n.natAbs : ℝ) / (↑N + 1))
      Filter.atTop (𝓝 0) := by
    have h_inv := tendsto_inv_atTop_zero.comp h_atTop
    have := (tendsto_const_nhds (x := (↑n.natAbs : ℝ))).mul h_inv
    rwa [mul_zero] at this
  -- Step 4: 1 - |n|/(N+1) → 1 - 0 = 1
  have h_sub := (tendsto_const_nhds (x := (1 : ℝ))).sub h_div
  rwa [sub_zero] at h_sub

/-- The Fejér weight converges pointwise to 1 in ℂ. -/
lemma fejerWeight_tendsto_complex (n : ℤ) :
    Filter.Tendsto (fun N : ℕ => (fejerWeight N n : ℂ)) Filter.atTop (𝓝 1) := by
  have := (Complex.continuous_ofReal.tendsto 1).comp (fejerWeight_tendsto n)
  simp only [Complex.ofReal_one] at this
  exact this

end Spectra.Herglotz

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.Borel.Identity.CauchyTransform
import Spectra.Bochner.Borel.Identity.BoundedCDF
import Spectra.Herglotz.Basic

/-!
# Vague Convergence of the Cauchy Transform

This file upgrades the pointwise convergence of `borel_cauchy_approx_tendsto`
(`Identity/CauchyTransform.lean`) to full vague convergence of the underlying measures: the
Cauchy transform of the approximate density along the Helly subsequence converges to the Cauchy
transform of the limit measure `borelMeasure U_grp ξ`, for every `z` off the real axis. This is
the identity `m_eq_cauchy_transform` (`Bochner/Borel/Measure/Basic.lean`) ultimately relies on to
identify the Herglotz function `m` with the Cauchy transform of the spectral measure, feeding
`Spectra.Bochner.bochner_theorem`.

## Main statements

* `borel_cauchy_vague`: `borelCauchyApprox U_grp ξ z` tends to `∫ (λ - z)⁻¹ ∂(borelMeasure U_grp
  ξ)` along the Helly subsequence, for every `z` with `z.im ≠ 0`.

## Implementation notes

The approximate and limit measures are first identified as Stieltjes measures of their CDFs
(`withDensity_ofReal_eq_stieltjes_measure`), which lets the bounded-window convergence
`integral_Ioc_tendsto_of_cdf_tendsto` (`Identity/BoundedCDF.lean`) apply on any window `[-R, R]`
whose endpoints avoid the countable discontinuity set of the limit CDF. The proof selects such an
`R` large enough that the tail mass outside `[-R, R]` is small for both measures (a uniform bound
on `‖∫ (λ - z)⁻¹‖` over the tail, using only that the total mass is at most `‖ξ‖²`), then combines
the bounded-window convergence with the two tail bounds via a three-term triangle inequality.

## References

* Reed, Simon, *Methods of Modern Mathematical Physics I*, Section VII (Stieltjes–Perron
  inversion and the Cauchy/Poisson representation of the resolvent).

## Tags

Cauchy transform, vague convergence, Herglotz representation, Helly selection
-/

open Complex MeasureTheory Filter Topology
open Spectra.Resolvent
open Spectra.Kernels
open Spectra.Herglotz
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open scoped InnerProductSpace ComplexConjugate

namespace Spectra.Borel

/-- The approximate Cauchy transforms converge, along the Helly subsequence, to the Cauchy
transform of the limit measure `borelMeasure U_grp ξ` — vague convergence for `z` off the real
axis. -/
lemma borel_cauchy_vague
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (borelCauchyApprox U_grp ξ z) atTop
      (𝓝 (∫ lambda, ((lambda : ℂ) - z)⁻¹ ∂(borelMeasure U_grp ξ))) := by
  -- Setup: the density/measure/mass notation used throughout the proof.
  set g  : ℝ → ℂ           := fun l => ((l : ℂ) - z)⁻¹ with _hg_def
  set G  : ℝ → ℝ           := borelLimitCDF U_grp ξ with _hG_def
  set μ  : Measure ℝ       := borelMeasure U_grp ξ  with _hμ_def
  set ρ  : ℕ → ℝ → ℝ       :=
    fun k => borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) with _hρ_def
  set μk : ℕ → Measure ℝ   :=
    fun k => volume.withDensity (fun l => ENNReal.ofReal (ρ k l)) with _hμk_def
  set M  : ℝ               := ‖ξ‖ ^ 2 with _hM_def
  have hM_nn   : 0 ≤ M := by positivity
  have _hzim    : 0 < |z.im| := abs_pos.mpr hz
  have hG_mono : Monotone G := borelLimitCDF_mono U_grp ξ
  have _hG_bnd  : ∀ x, G x ∈ Set.Icc (0 : ℝ) M :=
    (borelHelly U_grp ξ).choose_spec.choose_spec.2.2.1
  -- Properties of `g` (the Cauchy kernel) and `ρ` (the approximate density).
  have hg_cont : Continuous g := by
    refine (Complex.continuous_ofReal.sub continuous_const).inv₀ (fun l h => ?_)
    have : -z.im = 0 := by
      have := congrArg Complex.im h
      simpa [Complex.sub_im, Complex.ofReal_im] using this
    exact hz (neg_eq_zero.mp this)
  have hg_bdd  : ∀ l, ‖g l‖ ≤ 1 / |z.im| :=
    fun l => resolvent_integrand_bound z hz l
  have hρnn    : ∀ k l, 0 ≤ ρ k l := fun k l => borelDensity_nonneg _ _ _ l
  have hρcont  : ∀ k, Continuous (ρ k) := fun k => borelDensity_continuous _ _ _
  have hρmeas  : ∀ k, Measurable (ρ k) := fun k => (hρcont k).measurable
  have hρenn   : ∀ k, Measurable (fun l => ENNReal.ofReal (ρ k l)) :=
    fun k => (hρmeas k).ennreal_ofReal
  have hρint   : ∀ k, Integrable (ρ k) volume :=
    fun k => (borelDensity_mass _ _ _).1
  have hmass   : ∀ k, ∫ l, ρ k l ∂volume = M :=
    fun k => (borelDensity_mass _ _ _).2
  -- `μk k univ = ofReal M`, hence each `μk k` is a finite measure.
  have hμk_univ : ∀ k, μk k Set.univ = ENNReal.ofReal M := fun k => by
    change (volume.withDensity (fun l => ENNReal.ofReal (ρ k l))) Set.univ = _
    rw [withDensity_apply _ MeasurableSet.univ, MeasureTheory.setLIntegral_univ,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hρint k)
              (Filter.Eventually.of_forall (hρnn k)),
        hmass]
  haveI μk_fin : ∀ k, IsFiniteMeasure (μk k) := fun k =>
    ⟨by rw [hμk_univ k]; exact ENNReal.ofReal_lt_top⟩
  have hμk_real : ∀ k, (μk k Set.univ).toReal = M := fun k => by
    rw [hμk_univ k, ENNReal.toReal_ofReal hM_nn]
  -- `μ` is definitionally the Stieltjes measure of the limit CDF `G`.
  have μ_st : μ = (borelLimitCDF_mono U_grp ξ).stieltjesFunction.measure := rfl
  -- `μ`'s total mass is bounded by `M` (the `IsFiniteMeasure μ` instance is found via `μ_st`).
  have hμM : (μ Set.univ).toReal ≤ M := borelMeasure_real_univ_le U_grp ξ
  -- `g` is integrable with respect to both `μk k` and `μ`.
  have hg_int_μ : Integrable g μ :=
    Integrable.of_bound hg_cont.aestronglyMeasurable (1 / |z.im|)
      (Filter.Eventually.of_forall hg_bdd)
  have hg_int_μk : ∀ k, Integrable g (μk k) := fun k => by
    haveI := μk_fin k
    exact Integrable.of_bound hg_cont.aestronglyMeasurable (1 / |z.im|)
      (Filter.Eventually.of_forall hg_bdd)
  -- The `k`-th Cauchy approximant equals `∫ g ∂(μk k)`.
  have cauchy_eq : ∀ k, borelCauchyApprox U_grp ξ z k = ∫ l, g l ∂(μk k) := fun k => by
    change ∫ lambda : ℝ, ((lambda : ℂ) - z)⁻¹ * (ρ k lambda : ℂ) = ∫ l, g l ∂(μk k)
    rw [show μk k = volume.withDensity (fun l => ENNReal.ofReal (ρ k l)) from rfl,
        integral_withDensity_eq_integral_toReal_smul (hρenn k)
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards with l
    rw [ENNReal.toReal_ofReal (hρnn k l), Complex.real_smul,
        show (ρ k l : ℂ) * g l = g l * (ρ k l : ℂ) from mul_comm _ _]
  -- `μk k` is the Stieltjes measure of the approximate CDF (the identification `borel_cauchy_vague`
  -- most depends on): both are finite and agree on `Iic a` for every `a`, since
  -- `borelApproxCDF a = ∫ in Iic a, ρ`.
  have μk_st : ∀ k, μk k =
      (borelApproxCDF_mono U_grp ξ (borelSubseq U_grp ξ k)).stieltjesFunction.measure := fun k =>
    withDensity_ofReal_eq_stieltjes_measure
      (hρnn k) (hρint k)
      (fun _ => rfl)
      (borelApproxCDF_mono U_grp ξ _)
      (borelCDF_continuous U_grp ξ _)
      (borelCDF_tendsto_atBot U_grp ξ _)
  -- ε-δ unwrap and `R`-selection: choose `R > |z.re|` a continuity point of `G` and of `-G(-·)`
  -- with `2 * M / (R - |z.re|) < ε / 2`; the tail bound for `μk`/`μ` on `(Ioc (-R) R)ᶜ` is
  -- factored out below as the parametric lemma `tail`.
  rw [Metric.tendsto_atTop]; intro ε hε
  obtain ⟨R, hRz, hRneg, hRpos, hRsmall⟩ :
      ∃ R : ℝ, |z.re| < R ∧ ContinuousAt G (-R) ∧ ContinuousAt G R ∧
        2 * M / (R - |z.re|) < ε / 2 := by
    set c : ℝ := |z.re| + 4 * M / ε + 1 with hc_def
    have h4Mε_nn : 0 ≤ 4 * M / ε := div_nonneg (by linarith) hε.le
    have hc_gt : |z.re| < c := by rw [hc_def]; linarith
    -- Bad sets: discontinuities of G, and of (G ∘ Neg.neg).
    set D₁ : Set ℝ := {x | ¬ ContinuousAt G x}
    set D₂ : Set ℝ := Neg.neg '' D₁
    have hD₁_count : D₁.Countable := hG_mono.countable_not_continuousAt
    have hD₂_count : D₂.Countable := hD₁_count.image _
    have hD_count  : (D₁ ∪ D₂).Countable := hD₁_count.union hD₂_count
    have hD_null   : volume (D₁ ∪ D₂) = 0 := hD_count.measure_zero volume
    have h_Ioo_pos : volume (Set.Ioo c (c + 1)) ≠ 0 := by
      rw [Real.volume_Ioo]
      simp [show (c + 1 - c : ℝ) = 1 by ring]
    have h_diff_ne : volume (Set.Ioo c (c + 1) \ (D₁ ∪ D₂)) ≠ 0 := by
      rw [measure_diff_null hD_null]; exact h_Ioo_pos
    obtain ⟨R, hR_mem, hR_good⟩ := nonempty_of_measure_ne_zero h_diff_ne
    have hRc : c < R := hR_mem.1
    have hRcontR : ContinuousAt G R := by
      by_contra h; exact hR_good (Or.inl h)
    have hRcontNeg : ContinuousAt G (-R) := by
      by_contra h
      have : -R ∈ D₁ := h
      have : R ∈ D₂ := ⟨-R, this, by simp⟩
      exact hR_good (Or.inr this)
    have _hRgap : 4 * M / ε + 1 < R - |z.re| := by linarith
    have hRsm : 2 * M / (R - |z.re|) < ε / 2 := by
      rcases eq_or_lt_of_le hM_nn with hM0 | hMp
      · rw [← hM0]; simp; linarith
      · have hden : 0 < R - |z.re| := by linarith
        rw [div_lt_iff₀ hden]
        have h_step : 4 * M / ε < R - |z.re| := by linarith
        have h_target : 2 * M < ε / 2 * (R - |z.re|) := by
          have h_eq : ε / 2 * (4 * M / ε) = 2 * M := by field_simp; ring
          calc 2 * M = ε / 2 * (4 * M / ε) := h_eq.symm
            _ < ε / 2 * (R - |z.re|) :=
                mul_lt_mul_of_pos_left h_step (by linarith)
        exact h_target
    exact ⟨R, lt_trans hc_gt hRc, hRcontNeg, hRcontR, hRsm⟩
  have _hRgap : 0 < R - |z.re| := by linarith
  -- Tail bound, parametric in the finite measure `ν` (applied to both `μk k` and `μ` below).
  have tail : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], (ν Set.univ).toReal ≤ M →
      ‖∫ l in (Set.Ioc (-R) R)ᶜ, ((l : ℂ) - z)⁻¹ ∂ν‖ ≤ M / (R - |z.re|) := fun ν _ hνM =>
    (norm_setIntegral_cauchy_kernel_outside_le hRz).trans
      (div_le_div_of_nonneg_right hνM (by linarith))
  -- Convergence on the bounded window `[-R, R]`.
  -- Right-continuity of F = borelApproxCDF n holds trivially since F is continuous.
  have rc_F : ∀ N x, Function.rightLim (borelApproxCDF U_grp ξ N) x = borelApproxCDF U_grp ξ N x :=
    fun N x =>
      ((borelApproxCDF_mono U_grp ξ N).continuousWithinAt_Ioi_iff_rightLim_eq).mp
        (borelCDF_continuous U_grp ξ (borelEps_pos N)).continuousAt.continuousWithinAt
  have middle :
      Tendsto (fun k => ∫ l in Set.Ioc (-R) R, g l ∂(μk k)) atTop
        (𝓝 (∫ l in Set.Ioc (-R) R, g l ∂μ)) := by
    have h := integral_Ioc_tendsto_of_cdf_tendsto
      (mono_F := borelApproxCDF_mono U_grp ξ)
      (mono_G := borelLimitCDF_mono U_grp ξ)
      (rc_F := rc_F)
      (conv := fun x hx => borelApproxCDF_tendsto_continuousAt U_grp ξ hx)
      (by
        -- |z.re| < R is the hypothesis hRz; we need -R ≤ R.
        have : (0 : ℝ) ≤ |z.re| := abs_nonneg _
        linarith)
      hRneg hRpos hg_cont
    -- rewrite μ via μ_st
    rw [μ_st]
    exact h.congr (fun k => by rw [μk_st k])
  -- Assemble: split both integrals as `Ioc (-R) R` plus complement, then apply the triangle
  -- inequality using `middle` for the bounded part and `tail` for the two complements.
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 middle) (ε / 2) (by linarith)
  refine ⟨K, fun k hk => ?_⟩
  -- split both integrals as Ioc + complement
  have sk : ∫ l, g l ∂(μk k)
      = (∫ l in Set.Ioc (-R) R, g l ∂(μk k))
        + ∫ l in (Set.Ioc (-R) R)ᶜ, g l ∂(μk k) :=
    (integral_add_compl measurableSet_Ioc (hg_int_μk k)).symm
  have sμ : ∫ l, g l ∂μ
      = (∫ l in Set.Ioc (-R) R, g l ∂μ)
        + ∫ l in (Set.Ioc (-R) R)ᶜ, g l ∂μ :=
    (integral_add_compl measurableSet_Ioc hg_int_μ).symm
  rw [Complex.dist_eq, cauchy_eq k, sk, sμ]
  -- triangle: ‖(a+b) - (c+d)‖ ≤ ‖a-c‖ + ‖b‖ + ‖d‖
  set a := ∫ l in Set.Ioc (-R) R, g l ∂(μk k)
  set b := ∫ l in (Set.Ioc (-R) R)ᶜ, g l ∂(μk k)
  set c := ∫ l in Set.Ioc (-R) R, g l ∂μ
  set d := ∫ l in (Set.Ioc (-R) R)ᶜ, g l ∂μ
  have h_tri : ‖(a + b) - (c + d)‖ ≤ ‖a - c‖ + ‖b‖ + ‖d‖ := by
    have h_eq : (a + b) - (c + d) = (a - c) + (b - d) := by ring
    calc ‖(a + b) - (c + d)‖
        = ‖(a - c) + (b - d)‖   := by rw [h_eq]
      _ ≤ ‖a - c‖ + ‖b - d‖     := norm_add_le _ _
      _ ≤ ‖a - c‖ + (‖b‖ + ‖d‖) := by gcongr; exact norm_sub_le _ _
      _ = ‖a - c‖ + ‖b‖ + ‖d‖   := by ring
  -- Now run the calc.  All ≤ until the final strict step.
  calc ‖(a + b) - (c + d)‖
      ≤ ‖a - c‖ + ‖b‖ + ‖d‖ := h_tri
    _ ≤ ε / 2 + M / (R - |z.re|) + M / (R - |z.re|) := by
        gcongr
        · -- ‖a - c‖ ≤ ε/2
          have := hK k hk
          rw [Complex.dist_eq] at this
          exact this.le
        · -- ‖b‖ ≤ M/(R-|z.re|)
          have hμkM : (μk k Set.univ).toReal ≤ M := le_of_eq (hμk_real k)
          exact tail (μk k) hμkM
        · -- ‖d‖ ≤ M/(R-|z.re|)
          exact tail μ hμM
    _ = ε / 2 + 2 * M / (R - |z.re|) := by ring
    _ < ε := by linarith

end Spectra.Borel

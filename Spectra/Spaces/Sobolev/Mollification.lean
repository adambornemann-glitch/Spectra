/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.Submodules
import Mathlib.Analysis.Convex.Integral

/-!
# Mollification of compactly supported `L²` functions on `ℝ³`

The mollification step of Meyers–Serrin: convolving a compactly supported `L²` function against a
smooth bump approximates both the function and its weak derivative(s) simultaneously by a genuine
`C^∞` compactly supported function, within any `ε > 0`.

## Main definitions

* `bumpConvolve` — complex-valued convolution against a `ContDiffBump`, defined component-wise
  through real and imaginary parts to reuse Mathlib's real-valued convolution API.

## Main statements

* `mollify_compactly_supported_family` — the shared construction, parametrized by an arbitrary
  nonempty `Finite` index `ι` of directions: one bump convolution `ε`-approximates a compactly
  supported `L²` function and, for every `j : ι`, its weak derivative in direction `dir j`,
  simultaneously.
* `mollify_compactly_supported` — the `ι := Unit` specialization: a single bump convolution
  `ε`-approximates a compactly supported `L²` function and its weak derivative in direction `i`.
* `mollify_compactly_supported_multi` — the `ι := Fin d`, `dir := id` specialization: one bump
  convolution `ε`-approximates the function and all three of its weak partial derivatives at once.

## Implementation notes

Convolution is done component-wise via `Complex.reCLM`/`Complex.imCLM` rather than natively on
`ℂ`, since Mathlib's convolution API (`HasCompactSupport.contDiff_convolution_left`,
`dist_normed_convolution_le`, etc.) is stated for real-valued kernels and functions. The
derivative-commutes-with-convolution identity `∂ᵢ(ρ ⋆ h) = ρ ⋆ (∂ᵢh)` (`bumpConvolve_fderiv_eq`) is
the mechanism coupling the function and derivative approximations: its two real/imaginary cases
are both instances of one generic lemma (`bumpConvolve_fderiv_eq_component`) parametrized by the
projection `L : ℂ →L[ℝ] ℝ`.

## References

* [Evans, *Partial Differential Equations*][evans2010], Section 5.3 (mollifiers)
* [Brezis, *Functional Analysis, Sobolev Spaces and PDEs*][brezis2010], Section 4.4
-/

open MeasureTheory Complex
open scoped ENNReal Pointwise ContDiff

namespace Spectra.Sobolev

variable {d : ℕ}

/-- Continuous linear projections preserve local integrability. -/
private lemma locallyIntegrable_complexCLM (L : ℂ →L[ℝ] ℝ) {f : Rn d → ℂ}
    (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y => L (f y)) volume := by
  exact locallyIntegrableOn_univ.mp <| by
    simpa [Function.comp_def] using
      L.locallyIntegrableOn_comp (s := Set.univ) (μ := volume)
        (f := f) (locallyIntegrableOn_univ.mpr hf)

/-- Complex-valued convolution with a ContDiffBump mollifier, defined component-wise
    through real and imaginary parts (matching Mathlib's real-valued convolution API). -/
private noncomputable def bumpConvolve (ρ : ContDiffBump (0 : Rn d)) (f : Rn d → ℂ) :
    Rn d → ℂ :=
  fun x => ⟨MeasureTheory.convolution (ρ.normed volume) (fun y => (f y).re)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x,
            MeasureTheory.convolution (ρ.normed volume) (fun y => (f y).im)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x⟩

/-- Convolution with a smooth bump is smooth.
    Discharge: HasCompactSupport.contDiff_convolution_left for each component,
    then recombine via ofRealCLM.contDiff + mul contDiff_const
    (as in exists_smooth_uniform_approx). -/
private lemma bumpConvolve_smooth (ρ : ContDiffBump (0 : Rn d)) (f : Rn d → ℂ)
    (hf : LocallyIntegrable f volume) :
    ContDiff ℝ ∞ (bumpConvolve ρ f) := by
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  have hli_re : LocallyIntegrable (fun y => (f y).re) volume :=
    locallyIntegrable_complexCLM Complex.reCLM hf
  have hli_im : LocallyIntegrable (fun y => (f y).im) volume :=
    locallyIntegrable_complexCLM Complex.imCLM hf
  have hsmooth_re : ContDiff ℝ ∞ (fun x => MeasureTheory.convolution
      (ρ.normed volume) (fun y => (f y).re) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) :=
    HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      ρ.hasCompactSupport_normed ρ.contDiff_normed hli_re
  have hsmooth_im : ContDiff ℝ ∞ (fun x => MeasureTheory.convolution
      (ρ.normed volume) (fun y => (f y).im) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) :=
    HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      ρ.hasCompactSupport_normed ρ.contDiff_normed hli_im
  set ψ_re := fun x => MeasureTheory.convolution (ρ.normed volume) (fun y => (f y).re)
    (ContinuousLinearMap.lsmul ℝ ℝ) volume x with _hψ_re_def
  set ψ_im := fun x => MeasureTheory.convolution (ρ.normed volume) (fun y => (f y).im)
    (ContinuousLinearMap.lsmul ℝ ℝ) volume x with _hψ_im_def
  have hrw : bumpConvolve ρ f = fun x =>
      ((ψ_re x : ℂ) + (ψ_im x : ℂ) * Complex.I) := by
    ext x; apply Complex.ext
    · simp [bumpConvolve, ψ_re, ψ_im, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
    · simp [bumpConvolve, ψ_re, ψ_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_re, Complex.I_im]
  rw [hrw]
  exact (Complex.ofRealCLM.contDiff.comp hsmooth_re).add
    ((Complex.ofRealCLM.contDiff.comp hsmooth_im).mul contDiff_const)


/-- Convolution with a compactly supported function is compactly supported.
    Discharge: HasCompactSupport.convolution for each component,
    tsupport of ψ ⊆ tsupport ψ_re ∪ tsupport ψ_im (as in exists_smooth_uniform_approx). -/
private lemma bumpConvolve_hasCompactSupport (ρ : ContDiffBump (0 : Rn d)) (f : Rn d → ℂ)
    (hf_supp : HasCompactSupport f) :
    HasCompactSupport (bumpConvolve ρ f) := by
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  have hsupp_re : HasCompactSupport (fun y => (f y).re) := hf_supp.comp_left Complex.zero_re
  have hsupp_im : HasCompactSupport (fun y => (f y).im) := hf_supp.comp_left Complex.zero_im
  have hcs_re : HasCompactSupport (fun x => MeasureTheory.convolution (ρ.normed volume)
      (fun y => (f y).re) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) :=
    ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hsupp_re
  have hcs_im : HasCompactSupport (fun x => MeasureTheory.convolution (ρ.normed volume)
      (fun y => (f y).im) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) :=
    ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hsupp_im
  have h_sub : tsupport (bumpConvolve ρ f) ⊆
      tsupport (fun x => MeasureTheory.convolution (ρ.normed volume)
        (fun y => (f y).re) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) ∪
      tsupport (fun x => MeasureTheory.convolution (ρ.normed volume)
        (fun y => (f y).im) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) := by
    apply closure_minimal
    · intro x hx
      rw [Function.mem_support] at hx
      by_contra h
      rw [Set.mem_union, not_or] at h
      apply hx
      have hre0 := image_eq_zero_of_notMem_tsupport h.1
      have him0 := image_eq_zero_of_notMem_tsupport h.2
      change (⟨_, _⟩ : ℂ) = 0
      rw [hre0, him0]; rfl
    · exact (isClosed_tsupport _).union (isClosed_tsupport _)
  exact (hcs_re.isCompact.union hcs_im.isCompact).of_isClosed_subset
    (isClosed_tsupport _) h_sub

/-- bumpConvolve ρ g vanishes at x when g vanishes on ball(x, rOut). -/
private lemma bumpConvolve_eq_zero (ρ : ContDiffBump (0 : Rn d)) (g : Rn d → ℂ) (x : (Rn d))
    (hg_zero : ∀ t ∈ Metric.closedBall (0 : Rn d) ρ.rOut, g (x - t) = 0) :
    bumpConvolve ρ g x = 0 := by
  have hρ_zero : ∀ t, t ∉ Metric.closedBall (0 : Rn d) ρ.rOut → ρ.normed volume t = 0 := by
    intro t ht
    have : t ∉ Metric.ball (0 : Rn d) ρ.rOut := fun h => ht (Metric.ball_subset_closedBall h)
    have h_zero : (ρ : Rn d → ℝ) t = 0 := by
      by_contra h
      exact this (ρ.support_eq ▸ Function.mem_support.mpr h)
    simp [ρ.normed_def, h_zero]
  have h_component : ∀ (proj : ℂ → ℝ) (_hproj : proj 0 = 0),
      MeasureTheory.convolution (ρ.normed volume) (fun y => proj (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
    intro proj hproj
    simp only [MeasureTheory.convolution_def]
    refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    by_cases ht : t ∈ Metric.closedBall (0 : Rn d) ρ.rOut
    · rw [hg_zero t ht, hproj, mul_zero]; rfl
    · rw [hρ_zero t ht, zero_mul]; rfl
  change (⟨_, _⟩ : ℂ) = 0
  rw [h_component Complex.re Complex.zero_re, h_component Complex.im Complex.zero_im]
  rfl

/-- For continuous c.s. g, bumpConvolve ρ g → g in L² as rOut → 0.
    Discharge: uniform continuity of g gives pointwise oscillation < δ on
    small balls, dist_normed_convolution_le converts to pointwise bound,
    eLpNorm_le_of_compactSupport_bound converts to L². -/
private lemma bumpConvolve_tendsto_continuous (g : Rn d → ℂ)
    (hcont : Continuous g) (hsupp : HasCompactSupport g)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ (ρ : ContDiffBump (0 : Rn d)), ρ.rOut ≤ δ₀ →
      eLpNorm (g - bumpConvolve ρ g) 2 volume < ENNReal.ofReal ε := by
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Rn d)) := inferInstance
  -- Support geometry
  set K := tsupport g with _hK_def
  have hK : IsCompact K := hsupp.isCompact
  set K₁ := K + Metric.closedBall (0 : Rn d) 1 with _hK₁_def
  have _hK₁ : IsCompact K₁ := hK.add (isCompact_closedBall _ _)
  set K₂ := K + Metric.closedBall (0 : Rn d) 2 with _hK₂_def
  have hK₂ : IsCompact K₂ := hK.add (isCompact_closedBall _ _)
  have hK₁_sub_K₂ : K₁ ⊆ K₂ :=
    Set.add_subset_add_left (Metric.closedBall_subset_closedBall (by norm_num))
  -- Choose δ so that δ · √μ(K₂) < ε
  set M_sqrt := Real.sqrt ((volume : Measure (Rn d)) K₂).toReal
  have hM_nn : 0 ≤ M_sqrt := Real.sqrt_nonneg _
  set δ := ε / (M_sqrt + 1) with hδ_def
  have hδ_pos : 0 < δ := div_pos hε (by linarith)
  have hδM_lt : δ * M_sqrt < ε := by
    rw [hδ_def]
    rcases eq_or_lt_of_le hM_nn with hM0 | hM_pos
    · rw [← hM0, mul_zero]; exact hε
    · calc ε / (M_sqrt + 1) * M_sqrt
          < ε / (M_sqrt + 1) * (M_sqrt + 1) := by gcongr; linarith
        _ = ε := div_mul_cancel₀ ε (by linarith)
  -- Uniform continuity on K₂
  have huc := hK₂.uniformContinuousOn_of_continuous hcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη_pos, hη_spec⟩ := huc (δ / 2) (half_pos hδ_pos)
  -- δ₀ controls oscillation and support
  refine ⟨min (η / 2) 1, lt_min (by positivity) one_pos, fun ρ hρ => ?_⟩
  have hrOut_le_one : ρ.rOut ≤ 1 := hρ.trans (min_le_right _ _)
  have hrOut_lt_η : ρ.rOut < η :=
    lt_of_le_of_lt (hρ.trans (min_le_left _ _)) (half_lt_self hη_pos)
  -- Ball containment: x₀ ∈ K₁, y ∈ ball(x₀, rOut) ⟹ y ∈ K₂
  have ball_in_K₂ : ∀ x₀ ∈ K₁, ∀ y ∈ Metric.ball x₀ ρ.rOut, y ∈ K₂ := by
    intro x₀ hx₀ y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx₀
    exact Set.mem_add.mpr ⟨a, ha, b + (y - (a + b)), by
      rw [Metric.mem_closedBall] at hb ⊢
      calc dist (b + (y - (a + b))) 0
          = ‖b + (y - (a + b))‖ := by simp [dist_zero_right]
        _ ≤ ‖b‖ + ‖y - (a + b)‖ := norm_add_le _ _
        _ = dist b 0 + dist y (a + b) := by simp [dist_eq_norm]
        _ ≤ 1 + ρ.rOut := by gcongr; exact le_of_lt (Metric.mem_ball.mp hy)
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num, by abel⟩
  -- Measurability
  set g_re : Rn d → ℝ := fun x => (g x).re
  set g_im : Rn d → ℝ := fun x => (g x).im
  have hmeas_re : AEStronglyMeasurable g_re volume :=
    (Complex.continuous_re.comp hcont).aestronglyMeasurable
  have hmeas_im : AEStronglyMeasurable g_im volume :=
    (Complex.continuous_im.comp hcont).aestronglyMeasurable
  -- Pointwise bound: ‖g(x) - bumpConvolve ρ g (x)‖ ≤ δ
  have hpointwise : ∀ x, ‖g x - bumpConvolve ρ g x‖ ≤ δ := by
    intro x₀
    by_cases hx₀ : x₀ ∈ K₁
    · -- x₀ ∈ K₁: use dist_normed_convolution_le per component
      have hx₀_K₂ := hK₁_sub_K₂ hx₀
      have hosc_re : ∀ y ∈ Metric.ball x₀ ρ.rOut,
          dist (g_re y) (g_re x₀) ≤ δ / 2 := by
        intro y hy
        rw [Real.dist_eq]
        calc |g_re y - g_re x₀|
            = |(g y - g x₀).re| := by simp [g_re, Complex.sub_re]
          _ ≤ ‖g y - g x₀‖ := abs_re_le_norm _
          _ = ‖g x₀ - g y‖ := norm_sub_rev _ _
          _ ≤ δ / 2 := by
              rw [← dist_eq_norm]
              exact le_of_lt (hη_spec x₀ hx₀_K₂ y (ball_in_K₂ x₀ hx₀ y hy)
                (lt_trans (by rw [dist_comm]; exact Metric.mem_ball.mp hy) hrOut_lt_η))
      have hosc_im : ∀ y ∈ Metric.ball x₀ ρ.rOut,
          dist (g_im y) (g_im x₀) ≤ δ / 2 := by
        intro y hy
        rw [Real.dist_eq]
        calc |g_im y - g_im x₀|
            = |(g y - g x₀).im| := by simp [g_im, Complex.sub_im]
          _ ≤ ‖g y - g x₀‖ := abs_im_le_norm _
          _ = ‖g x₀ - g y‖ := norm_sub_rev _ _
          _ ≤ δ / 2 := by
              rw [← dist_eq_norm]
              exact le_of_lt (hη_spec x₀ hx₀_K₂ y (ball_in_K₂ x₀ hx₀ y hy)
                (lt_trans (by rw [dist_comm]; exact Metric.mem_ball.mp hy) hrOut_lt_η))
      have hre := ρ.dist_normed_convolution_le hmeas_re hosc_re
      have him := ρ.dist_normed_convolution_le hmeas_im hosc_im
      have hdiff_re : (g x₀ - bumpConvolve ρ g x₀).re = g_re x₀ -
          MeasureTheory.convolution (ρ.normed volume) g_re
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀ := by
        simp [bumpConvolve, g_re, Complex.sub_re]
      have hdiff_im : (g x₀ - bumpConvolve ρ g x₀).im = g_im x₀ -
          MeasureTheory.convolution (ρ.normed volume) g_im
            (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀ := by
        simp [bumpConvolve, g_im, Complex.sub_im]
      calc ‖g x₀ - bumpConvolve ρ g x₀‖
          ≤ |(g x₀ - bumpConvolve ρ g x₀).re| + |(g x₀ - bumpConvolve ρ g x₀).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = |g_re x₀ - MeasureTheory.convolution (ρ.normed volume) g_re
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀| +
            |g_im x₀ - MeasureTheory.convolution (ρ.normed volume) g_im
              (ContinuousLinearMap.lsmul ℝ ℝ) volume x₀| := by
            rw [hdiff_re, hdiff_im]
        _ ≤ δ / 2 + δ / 2 := by
            gcongr
            · rwa [abs_sub_comm, ← Real.dist_eq]
            · rwa [abs_sub_comm, ← Real.dist_eq]
        _ = δ := add_halves δ
    · -- x₀ ∉ K₁: both g(x₀) = 0 and bumpConvolve ρ g (x₀) = 0
      have hgx : g x₀ = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        exact fun h => hx₀ (Set.mem_add.mpr ⟨x₀, h, 0,
          Metric.mem_closedBall_self one_pos.le, by simp⟩)
      have hρgx : bumpConvolve ρ g x₀ = 0 := bumpConvolve_eq_zero ρ g x₀ (by
        intro t ht
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hx₀ (Set.mem_add.mpr ⟨x₀ - t, hmem, t,
          Metric.closedBall_subset_closedBall hrOut_le_one ht, by abel⟩))
      rw [hgx, hρgx, sub_self, norm_zero]; exact hδ_pos.le
  -- Compact support and measurability of the difference
  have hcs_diff : HasCompactSupport (g - bumpConvolve ρ g) :=
    hsupp.sub (bumpConvolve_hasCompactSupport ρ g hsupp)
  -- Support containment: tsupport(g - bumpConvolve ρ g) ⊆ K₂
  have hsupp_sub : tsupport (g - bumpConvolve ρ g) ⊆ K₂ := by
    apply closure_minimal _ hK₂.isClosed
    intro x hx
    rw [Function.mem_support, Pi.sub_apply, sub_ne_zero] at hx
    by_contra h_out
    exact hx (by
      have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
        h_out (Set.mem_add.mpr ⟨x, h, 0,
          Metric.mem_closedBall_self (by norm_num : (0:ℝ) ≤ 2), by simp⟩))
      have hρgx : bumpConvolve ρ g x = 0 := bumpConvolve_eq_zero ρ g x (fun t ht =>
        image_eq_zero_of_notMem_tsupport (fun hmem =>
          h_out (Set.mem_add.mpr ⟨x - t, hmem, t,
            (Metric.closedBall_subset_closedBall (by linarith : ρ.rOut ≤ 2)) ht, by abel⟩)))
      rw [hgx, hρgx])
  -- L² bound via compact support + pointwise bound
  have h_eLpNorm := eLpNorm_le_of_compactSupport_bound (g - bumpConvolve ρ g)
    hcs_diff δ hpointwise
  have h_meas_le : (volume : Measure (Rn d)) (tsupport (g - bumpConvolve ρ g)) ≤
      (volume : Measure (Rn d)) K₂ := measure_mono hsupp_sub
  have h_chain : eLpNorm (g - bumpConvolve ρ g) 2 volume ≤
      ENNReal.ofReal δ * ((volume : Measure (Rn d)) K₂) ^ ((1 : ℝ) / 2) :=
    h_eLpNorm.trans (by gcongr)
  -- Convert to ℝ and close with arithmetic
  have h_ne_top : eLpNorm (g - bumpConvolve ρ g) 2 volume ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK₂.measure_lt_top.ne)) h_chain
  rw [← ENNReal.ofReal_toReal h_ne_top]
  apply ENNReal.ofReal_lt_ofReal_iff hε |>.mpr
  calc (eLpNorm (g - bumpConvolve ρ g) 2 volume).toReal
      ≤ (ENNReal.ofReal δ * ((volume : Measure (Rn d)) K₂) ^ ((1 : ℝ) / 2)).toReal :=
        ENNReal.toReal_le_toReal h_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK₂.measure_lt_top.ne)) |>.mpr h_chain
    _ = δ * M_sqrt := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ_pos.le, ← ENNReal.toReal_rpow]
        exact congr_arg (δ * ·) (Real.sqrt_eq_rpow _).symm
    _ < ε := hδM_lt

/-- Integrability of bump convolution integrand. -/
private lemma integrable_bump_smul_comp (ρ : ContDiffBump (0 : Rn d))
    (h : Rn d → ℝ) (hh : LocallyIntegrable h volume) (x : (Rn d)) :
    Integrable (fun t => ρ.normed volume t * h (x - t)) volume := by
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  have hce : ConvolutionExists (ρ.normed volume) h
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Rn d)) :=
    HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      ρ.hasCompactSupport_normed ρ.continuous_normed hh
  have hat : Integrable
      (fun t => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
        (ρ.normed volume t) (h (x - t))) volume := hce x
  exact hat.congr <| Filter.Eventually.of_forall fun t => by
    simp [ContinuousLinearMap.lsmul_apply]

/-- Componentwise convolution distributes over subtraction. -/
private lemma convolution_component_sub (ρ : ContDiffBump (0 : Rn d)) (L : ℂ →L[ℝ] ℝ)
    (f g : Rn d → ℂ)
    (hf : LocallyIntegrable (fun y => L (f y)) volume)
    (hg : LocallyIntegrable (fun y => L (g y)) volume)
    (x : (Rn d)) :
    MeasureTheory.convolution (ρ.normed volume) (fun y => L ((f - g) y))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
    MeasureTheory.convolution (ρ.normed volume) (fun y => L (f y))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x -
    MeasureTheory.convolution (ρ.normed volume) (fun y => L (g y))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [show (fun t => ρ.normed volume t * L ((f - g) (x - t))) =
      (fun t => ρ.normed volume t * L (f (x - t))) -
      (fun t => ρ.normed volume t * L (g (x - t))) from by
        ext t
        simp [Pi.sub_apply, mul_sub]]
  exact integral_sub (integrable_bump_smul_comp ρ _ hf x)
    (integrable_bump_smul_comp ρ _ hg x)

/-- bumpConvolve is linear: ρ ⋆ (f - g) = ρ ⋆ f - ρ ⋆ g. -/
private lemma bumpConvolve_sub (ρ : ContDiffBump (0 : Rn d)) (f g : Rn d → ℂ)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    bumpConvolve ρ (f - g) = bumpConvolve ρ f - bumpConvolve ρ g := by
  have hf_re : LocallyIntegrable (fun y => (f y).re) volume :=
    locallyIntegrable_complexCLM Complex.reCLM hf
  have hg_re : LocallyIntegrable (fun y => (g y).re) volume :=
    locallyIntegrable_complexCLM Complex.reCLM hg
  have hf_im : LocallyIntegrable (fun y => (f y).im) volume :=
    locallyIntegrable_complexCLM Complex.imCLM hf
  have hg_im : LocallyIntegrable (fun y => (g y).im) volume :=
    locallyIntegrable_complexCLM Complex.imCLM hg
  ext x; simp only [bumpConvolve, Pi.sub_apply]; rw [Complex.mk.injEq]
  simp only [sub_re, sub_im]
  constructor
  · exact convolution_component_sub ρ Complex.reCLM f g hf_re hg_re x
  · exact convolution_component_sub ρ Complex.imCLM f g hf_im hg_im x

/-- **L² contraction for bump convolution** (real-valued case).
If `ψ` is a normalized bump function (nonneg, integrates to one, compactly supported,
continuous) and `g ∈ L²`, then `ψ ⋆ g` is also in `L²` with `‖ψ ⋆ g‖₂ ≤ ‖g‖₂`. -/
private lemma eLpNorm_real_convolve_le (ρ : ContDiffBump (0 : Rn d))
    (g : Rn d → ℝ) (hg : MemLp g 2 volume) :
    eLpNorm (MeasureTheory.convolution (ρ.normed volume) g
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ eLpNorm g 2 volume := by
  -- ===== Setup =====
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  set ψ := ρ.normed volume with _hψ_def
  have hψ_nn   : ∀ x, 0 ≤ ψ x := ρ.nonneg_normed
  have hψ_cont : Continuous ψ := ρ.continuous_normed
  have hψ_meas : Measurable ψ := hψ_cont.measurable
  have hψ_supp : HasCompactSupport ψ := ρ.hasCompactSupport_normed
  have hψ_int_eq_one : ∫ t, ψ t ∂(volume : Measure (Rn d)) = 1 := ρ.integral_normed
  have hψ_intble : Integrable ψ volume := hψ_cont.integrable_of_hasCompactSupport hψ_supp
  have hψ_ae_nn : 0 ≤ᵐ[volume] ψ := Filter.Eventually.of_forall hψ_nn
  have hg_sq_intble : Integrable (fun t => g t * g t) volume := hg.integrable_mul hg
  have hg_sq_intble' : Integrable (fun t => (g t) ^ 2) volume := by
    convert hg_sq_intble using 1; ext t; ring
  have _hg_sq_nn : ∀ t, 0 ≤ (g t) ^ 2 := fun t => sq_nonneg _
  set ψg  := MeasureTheory.convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume with _hψg_def
  set ψg_sq := MeasureTheory.convolution ψ (fun t => (g t) ^ 2)
              (ContinuousLinearMap.lsmul ℝ ℝ) volume with _hψg_sq_def
  -- ===== STEP 1: Build the probability measure ν₀ = ψ · volume =====
  let ν₀ : Measure (Rn d) := volume.withDensity (fun t => ENNReal.ofReal (ψ t))
  haveI hν_prob : IsProbabilityMeasure ν₀ := by
    refine ⟨?_⟩
    change (volume.withDensity _) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal hψ_intble hψ_ae_nn,
        hψ_int_eq_one, ENNReal.ofReal_one]
  -- ===== STEP 2: Both sides of the convolution as integrals against ν =====
  -- ∫ f dν = ∫ ψ(t) • f(t) ∂volume. `ν` is `ν₀` re-spelled with `Real.toNNReal` in place of
  -- `ENNReal.ofReal` (the two are defeq, `ENNReal.ofReal r := r.toNNReal`), because
  -- `integral_withDensity_eq_integral_smul` below needs the density in `NNReal`-coercion form.
  let ν : Measure (Rn d) := volume.withDensity (fun t => (Real.toNNReal (ψ t) : ℝ≥0∞))
  have hν₀_eq_ν : ν₀ = ν := rfl
  have h_lhs : ∀ x, ψg x = ∫ t, g (x - t) ∂ν := by
    intro x
    change MeasureTheory.convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = _
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [integral_withDensity_eq_integral_smul
          hψ_meas.real_toNNReal (fun t => g (x - t))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hψ_nn t)]
  have h_rhs : ∀ x, ψg_sq x = ∫ t, (g (x - t)) ^ 2 ∂ν := by
    intro x
    change MeasureTheory.convolution ψ (fun t => (g t) ^ 2)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x = _
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [integral_withDensity_eq_integral_smul
          hψ_meas.real_toNNReal (fun t => (g (x - t)) ^ 2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hψ_nn t)]
  -- ===== STEP 3: Pointwise Cauchy–Schwarz via Jensen for ν =====
  have h_pointwise : ∀ x, (ψg x) ^ 2 ≤ ψg_sq x := by
    intro x
    rw [h_lhs x, h_rhs x]
    -- Common: g and g² are locally integrable on volume
    have hg_locInt : MeasureTheory.LocallyIntegrable g volume :=
      hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hg2_locInt : MeasureTheory.LocallyIntegrable (fun t => (g t)^2) volume :=
      hg_sq_intble'.locallyIntegrable
    -- ψ · g(x-·) and ψ · g²(x-·) integrable on volume via convolution_exists_left
    have hψ_g_x_intble : Integrable (fun t => ψ t * g (x - t)) volume := by
      have hat : Integrable
          (fun t => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
            (ψ t) (g (x - t))) volume :=
        HasCompactSupport.convolutionExists_left
          (ContinuousLinearMap.lsmul ℝ ℝ) hψ_supp hψ_cont hg_locInt x
      exact hat.congr <| Filter.Eventually.of_forall fun t => by
        simp [ContinuousLinearMap.lsmul_apply]
    have hψ_g2_x_intble : Integrable (fun t => ψ t * (g (x - t)) ^ 2) volume := by
      have hat : Integrable
          (fun t => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
            (ψ t) ((g (x - t)) ^ 2)) volume :=
        HasCompactSupport.convolutionExists_left
          (ContinuousLinearMap.lsmul ℝ ℝ) hψ_supp hψ_cont hg2_locInt x
      exact hat.congr <| Filter.Eventually.of_forall fun t => by
        simp [ContinuousLinearMap.lsmul_apply]
    -- Hoist measure-preserving + AEStronglyMeasurable (used by both ν-integrability proofs)
    have hmp : MeasureTheory.MeasurePreserving (fun a : (Rn d) => x - a) volume volume := by
      have h1 : MeasureTheory.MeasurePreserving (fun a : (Rn d) => x + a) volume volume :=
        measurePreserving_add_left volume x
      have h2 : MeasureTheory.MeasurePreserving (fun a : (Rn d) => -a) volume volume :=
        Measure.measurePreserving_neg volume
      have heq : (fun a : (Rn d) => x - a) = (fun a => x + a) ∘ (fun a => -a) := by
        ext a; simp [sub_eq_add_neg]
      rw [heq]; exact h1.comp h2
    have hg_x_aesm : AEStronglyMeasurable (fun t => g (x - t)) volume := by
      have hg_pre : AEStronglyMeasurable g (Measure.map (fun a : (Rn d) => x - a) volume) := by
        rw [hmp.map_eq]; exact hg.1
      exact hg_pre.comp_measurable (measurable_const.sub measurable_id)
    have hg2_x_aesm : AEStronglyMeasurable (fun t => (g (x - t))^2) volume :=
      hg_x_aesm.pow 2
    -- Now the two ν-integrability facts, in parallel
    have hg_x_intble_ν : Integrable (fun t => g (x - t)) ν := by
      refine ⟨?_, ?_⟩
      · exact hg_x_aesm.mono_ac (withDensity_absolutelyContinuous _ _)
      · change ∫⁻ t, ‖g (x - t)‖ₑ ∂ν < ⊤
        rw [show (ν : Measure (Rn d)) =
              volume.withDensity (fun t => ((ψ t).toNNReal : ℝ≥0∞)) from rfl,
            lintegral_withDensity_eq_lintegral_mul₀'
              hψ_meas.real_toNNReal.coe_nnreal_ennreal.aemeasurable
              (hg_x_aesm.enorm.mono_ac (withDensity_absolutelyContinuous _ _))]
        have hψ_g_finite : ∫⁻ t, ‖ψ t * g (x - t)‖ₑ ∂volume < ⊤ := hψ_g_x_intble.2
        refine lt_of_le_of_lt ?_ hψ_g_finite
        refine lintegral_mono fun t => ?_
        change ((ψ t).toNNReal : ℝ≥0∞) * ‖g (x - t)‖ₑ ≤ ‖ψ t * g (x - t)‖ₑ
        rw [show ((ψ t).toNNReal : ℝ≥0∞) = ‖ψ t‖ₑ by
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hψ_nn t)]; rfl,
            ← enorm_mul]
    have hg2_x_intble_ν : Integrable (fun t => (g (x - t))^2) ν := by
      refine ⟨?_, ?_⟩
      · exact hg2_x_aesm.mono_ac (withDensity_absolutelyContinuous _ _)
      · change ∫⁻ t, ‖(g (x - t))^2‖ₑ ∂ν < ⊤
        rw [show (ν : Measure (Rn d)) =
              volume.withDensity (fun t => ((ψ t).toNNReal : ℝ≥0∞)) from rfl,
            lintegral_withDensity_eq_lintegral_mul₀'
              hψ_meas.real_toNNReal.coe_nnreal_ennreal.aemeasurable
              (hg2_x_aesm.enorm.mono_ac (withDensity_absolutelyContinuous _ _))]
        have hψ_g2_finite : ∫⁻ t, ‖ψ t * (g (x - t))^2‖ₑ ∂volume < ⊤ := hψ_g2_x_intble.2
        refine lt_of_le_of_lt ?_ hψ_g2_finite
        refine lintegral_mono fun t => ?_
        change ((ψ t).toNNReal : ℝ≥0∞) * ‖(g (x - t))^2‖ₑ ≤ ‖ψ t * (g (x - t))^2‖ₑ
        rw [show ((ψ t).toNNReal : ℝ≥0∞) = ‖ψ t‖ₑ by
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hψ_nn t)]; rfl,
            ← enorm_mul]
    -- Jensen with φ(u) = u² on Set.univ
    haveI : IsProbabilityMeasure ν := hν₀_eq_ν ▸ hν_prob
    have h_even : Even 2 := by decide
    have h_jensen := (h_even.convexOn_pow).map_integral_le
      (μ := ν) (f := fun t => g (x - t))
      (continuous_pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      hg_x_intble_ν
      (by
        change Integrable ((fun u => u ^ 2) ∘ fun t => g (x - t)) ν
        exact hg2_x_intble_ν)
    exact h_jensen
  -- ===== STEP 4: Integrate and apply integral_convolution =====
  have h_conv_g2_intble : Integrable ψg_sq volume :=
    hψ_intble.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg_sq_intble'
  have hψg_sq_intble : Integrable (fun x => (ψg x) ^ 2) volume := by
    refine Integrable.mono' h_conv_g2_intble ?_ (Filter.Eventually.of_forall fun x => ?_)
    · have hg_locInt : MeasureTheory.LocallyIntegrable g volume :=
        hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      exact ((HasCompactSupport.continuous_convolution_left
          (ContinuousLinearMap.lsmul ℝ ℝ) hψ_supp hψ_cont hg_locInt
        ).aestronglyMeasurable).pow 2
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_pointwise x
  have h_integral_le : ∫ x, (ψg x) ^ 2 ∂volume ≤ ∫ x, ψg_sq x ∂volume :=
    integral_mono hψg_sq_intble h_conv_g2_intble (h_pointwise)
  have h_integral_eq : ∫ x, ψg_sq x ∂volume = ∫ x, (g x) ^ 2 ∂volume := by
    change ∫ x, MeasureTheory.convolution ψ (fun t => (g t) ^ 2)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume x ∂volume = _
    rw [MeasureTheory.integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
          hψ_intble hg_sq_intble']
    simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_int_eq_one]
  have h_sq_le : ∫ x, (ψg x) ^ 2 ∂volume ≤ ∫ x, (g x) ^ 2 ∂volume :=
    h_integral_le.trans_eq h_integral_eq
  -- ===== STEP 5: Bridge real ∫(·)² to eLpNorm² and conclude =====
  have hψg_sq_ae_nn : 0 ≤ᵐ[volume] fun x => (ψg x) ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have hg_sq_ae_nn : 0 ≤ᵐ[volume] fun x => (g x) ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  -- ∫⁻ ‖f‖ₑ² = ENNReal.ofReal (∫ f²) for real-valued integrable f²
  have h_lintegral_eq_lhs :
      ∫⁻ x, ‖ψg x‖ₑ ^ (2 : ℝ) ∂volume = ENNReal.ofReal (∫ x, (ψg x) ^ 2 ∂volume) := by
    -- Pointwise: ‖ψg x‖ₑ ^ (2:ℝ) = ENNReal.ofReal ((ψg x)^2)
    have h_eq : ∀ x, ‖ψg x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((ψg x) ^ 2) := fun x => by
      rw [Real.enorm_eq_ofReal_abs,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          ENNReal.rpow_natCast,
          ← ENNReal.ofReal_pow (abs_nonneg _),
          sq_abs]
    simp_rw [h_eq]
    rw [← ofReal_integral_eq_lintegral_ofReal hψg_sq_intble hψg_sq_ae_nn]
  have h_lintegral_eq_rhs :
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂volume = ENNReal.ofReal (∫ x, (g x) ^ 2 ∂volume) := by
    have h_eq : ∀ x, ‖g x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((g x) ^ 2) := fun x => by
      rw [Real.enorm_eq_ofReal_abs,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          ENNReal.rpow_natCast,
          ← ENNReal.ofReal_pow (abs_nonneg _),
          sq_abs]
    simp_rw [h_eq]
    rw [← ofReal_integral_eq_lintegral_ofReal hg_sq_intble' hg_sq_ae_nn]
  -- Apply via the eLpNorm = (∫⁻ ‖·‖ₑ^p)^(1/p) characterization
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top  : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  simp only [ENNReal.toReal_ofNat]
  -- Goal: (∫⁻ ‖ψg‖ₑ²)^(1/2) ≤ (∫⁻ ‖g‖ₑ²)^(1/2)
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
  rw [h_lintegral_eq_lhs, h_lintegral_eq_rhs]
  exact ENNReal.ofReal_le_ofReal h_sq_le


/-- **L² contraction for bump convolution** (complex-valued case).
The component-wise bump convolution on ℂ-valued L² functions is a contraction. -/
private lemma eLpNorm_bumpConvolve_le (ρ : ContDiffBump (0 : Rn d))
    (h : Rn d → ℂ) (hh : MemLp h 2 volume) :
    eLpNorm (bumpConvolve ρ h) 2 volume ≤ eLpNorm h 2 volume := by
  -- ===== Setup: real and imaginary parts =====
  set ψ := ρ.normed volume with _hψ_def
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  have hψ_cont : Continuous ψ := ρ.continuous_normed
  have hψ_supp : HasCompactSupport ψ := ρ.hasCompactSupport_normed
  let h_re : Rn d → ℝ := fun x => (h x).re
  let h_im : Rn d → ℝ := fun x => (h x).im
  -- h_re, h_im ∈ L²(ℝ)
  have hh_re : MemLp h_re 2 volume := by
    refine ⟨hh.aestronglyMeasurable.re, ?_⟩
    refine lt_of_le_of_lt
      (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)) hh.eLpNorm_lt_top
    change ‖(h x).re‖ ≤ ‖h x‖
    exact Complex.abs_re_le_norm (h x)
  have hh_im : MemLp h_im 2 volume := by
    refine ⟨hh.aestronglyMeasurable.im, ?_⟩
    refine lt_of_le_of_lt
      (eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)) hh.eLpNorm_lt_top
    change ‖(h x).im‖ ≤ ‖h x‖
    exact Complex.abs_im_le_norm (h x)
  set ψ_h_re := MeasureTheory.convolution ψ h_re (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with _hψ_h_re_def
  set ψ_h_im := MeasureTheory.convolution ψ h_im (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with _hψ_h_im_def
  -- bumpConvolve's components are exactly the real convolutions
  have h_bC_re : ∀ x, (bumpConvolve ρ h x).re = ψ_h_re x := fun _ => rfl
  have h_bC_im : ∀ x, (bumpConvolve ρ h x).im = ψ_h_im x := fun _ => rfl
  -- ===== Apply helper to each component =====
  have h_re_bound : eLpNorm ψ_h_re 2 volume ≤ eLpNorm h_re 2 volume :=
    eLpNorm_real_convolve_le ρ h_re hh_re
  have h_im_bound : eLpNorm ψ_h_im 2 volume ≤ eLpNorm h_im 2 volume :=
    eLpNorm_real_convolve_le ρ h_im hh_im
  -- ===== Pointwise: ‖z‖ₑ² = ‖z.re‖ₑ² + ‖z.im‖ₑ² for z : ℂ =====
  have h_cx_enorm_sq : ∀ (z : ℂ),
      ‖z‖ₑ ^ (2:ℝ) = ‖z.re‖ₑ ^ (2:ℝ) + ‖z.im‖ₑ ^ (2:ℝ) := by
    intro z
    have h_real : (‖z‖)^2 = z.re^2 + z.im^2 := by
      rw [ Complex.sq_norm, Complex.normSq_apply, sq, sq]
    have real_lemma : ∀ (a : ℝ), ‖a‖ₑ ^ (2:ℝ) = ENNReal.ofReal (a^2) := fun a => by
      rw [Real.enorm_eq_ofReal_abs,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have cx_lemma : ‖z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖z‖^2) := by
      rw [show (‖z‖ₑ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [cx_lemma, h_real, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ← real_lemma, ← real_lemma]
  -- ===== Convert eLpNorm bounds to lintegral bounds =====
  have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_ne_top  : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have lift_to_lintegral : ∀ {f g : Rn d → ℝ},
      eLpNorm f 2 volume ≤ eLpNorm g 2 volume →
      ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂volume ≤ ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume := by
    intros f g hfg
    have hfg' := hfg
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top] at hfg'
    simp only [ENNReal.toReal_ofNat] at hfg'
    -- hfg' : (∫⁻ ‖f‖ₑ^2)^(1/2) ≤ (∫⁻ ‖g‖ₑ^2)^(1/2)
    have h2 : (1/2 : ℝ) * 2 = 1 := by norm_num
    calc ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂volume
        = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂volume) ^ (1:ℝ) := by rw [ENNReal.rpow_one]
      _ = (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂volume) ^ ((1/2 : ℝ) * 2) := by rw [h2]
      _ = ((∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) ^ (2:ℝ) :=
          ENNReal.rpow_mul _ _ _
      _ ≤ ((∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2:ℝ)) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow hfg' (by norm_num : (0:ℝ) ≤ 2)
      _ = (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume) ^ ((1/2:ℝ) * 2) := (ENNReal.rpow_mul _ _ _).symm
      _ = (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume) ^ (1:ℝ) := by rw [h2]
      _ = ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂volume := by rw [ENNReal.rpow_one]
  have h_re_lint : ∫⁻ x, ‖ψ_h_re x‖ₑ ^ (2:ℝ) ∂volume ≤ ∫⁻ x, ‖h_re x‖ₑ ^ (2:ℝ) ∂volume :=
    lift_to_lintegral h_re_bound
  have h_im_lint : ∫⁻ x, ‖ψ_h_im x‖ₑ ^ (2:ℝ) ∂volume ≤ ∫⁻ x, ‖h_im x‖ₑ ^ (2:ℝ) ∂volume :=
    lift_to_lintegral h_im_bound
  -- ===== Split lintegrals via the complex norm identity =====
  -- AEMeasurability for lintegral_add_left'
  have hψ_h_re_aem : AEMeasurable (fun x => ‖ψ_h_re x‖ₑ ^ (2:ℝ)) volume := by
    have hh_re_locInt : MeasureTheory.LocallyIntegrable h_re volume :=
      hh_re.locallyIntegrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
    have : Continuous ψ_h_re :=
      HasCompactSupport.continuous_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) hψ_supp hψ_cont hh_re_locInt
    exact this.aestronglyMeasurable.enorm.pow_const _
  have hh_re_aem : AEMeasurable (fun x => ‖h_re x‖ₑ ^ (2:ℝ)) volume :=
    hh_re.aestronglyMeasurable.enorm.pow_const _
  have h_bC_lint : ∫⁻ x, ‖bumpConvolve ρ h x‖ₑ ^ (2:ℝ) ∂volume =
      (∫⁻ x, ‖ψ_h_re x‖ₑ ^ (2:ℝ) ∂volume) + ∫⁻ x, ‖ψ_h_im x‖ₑ ^ (2:ℝ) ∂volume := by
    have h_pt : ∀ x, ‖bumpConvolve ρ h x‖ₑ ^ (2:ℝ) =
        ‖ψ_h_re x‖ₑ ^ (2:ℝ) + ‖ψ_h_im x‖ₑ ^ (2:ℝ) := by
      intro x; rw [h_cx_enorm_sq (bumpConvolve ρ h x), h_bC_re, h_bC_im]
    simp_rw [h_pt]
    rw [lintegral_add_left' hψ_h_re_aem]
  have h_h_lint : ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂volume =
      (∫⁻ x, ‖h_re x‖ₑ ^ (2:ℝ) ∂volume) + ∫⁻ x, ‖h_im x‖ₑ ^ (2:ℝ) ∂volume := by
    have h_pt : ∀ x, ‖h x‖ₑ ^ (2:ℝ) = ‖h_re x‖ₑ ^ (2:ℝ) + ‖h_im x‖ₑ ^ (2:ℝ) :=
      fun x => h_cx_enorm_sq (h x)
    simp_rw [h_pt]
    rw [lintegral_add_left' hh_re_aem]
  -- ===== Combine and conclude =====
  have h_sum_le : ∫⁻ x, ‖bumpConvolve ρ h x‖ₑ ^ (2:ℝ) ∂volume ≤
      ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) ∂volume := by
    rw [h_bC_lint, h_h_lint]
    exact add_le_add h_re_lint h_im_lint
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow h_sum_le (by norm_num : (0:ℝ) ≤ 1/2)


private lemma eLpNorm_bumpConvolve_sub (ρ : ContDiffBump (0 : Rn d))
    (f g : Rn d → ℂ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    eLpNorm (bumpConvolve ρ f - bumpConvolve ρ g) 2 volume ≤
    eLpNorm (f - g) 2 volume := by
  haveI : IsLocallyFiniteMeasure (volume : Measure (Rn d)) := inferInstance
  rw [← bumpConvolve_sub ρ f g
    (hf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
  exact eLpNorm_bumpConvolve_le ρ (f - g) (hf.sub hg)

/-- L² convergence of convolution: for compactly supported f ∈ L²,
    mollification is ε-close for all sufficiently concentrated bumps -/
private lemma bumpConvolve_L2_tendsto (f : Rn d → ℂ)
    (hf : MemLp f 2 volume)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ (ρ : ContDiffBump (0 : Rn d)), ρ.rOut ≤ δ₀ →
      eLpNorm (f - bumpConvolve ρ f) 2 volume < ENNReal.ofReal ε := by
  have hε3 : 0 < ε / 3 := by positivity
  -- Step 1: approximate f by continuous c.s. φ within ε/3
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Rn d)) := inferInstance
  haveI : (volume : Measure (Rn d)).Regular := inferInstance
  haveI : WeaklyLocallyCompactSpace (Rn d) := inferInstance
  haveI : R1Space (Rn d) := inferInstance
  have hε3' : (ENNReal.ofReal (ε / 3)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hε3
  obtain ⟨φ, hφ_supp, hφ_close, hφ_cont, hφ_mem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hε3'
  -- hφ_close : eLpNorm (φ - f) 2 volume ≤ ENNReal.ofReal (ε / 3)
  -- Step 2: for continuous φ, find δ₀ for L² convergence of mollification
  obtain ⟨δ₀, hδ₀_pos, hδ₀_spec⟩ :=
    bumpConvolve_tendsto_continuous φ hφ_cont hφ_supp (ε / 3) hε3
  -- Step 3: assemble via triangle inequality
  refine ⟨δ₀, hδ₀_pos, fun ρ hρ => ?_⟩
  -- Measurability witnesses
  haveI : IsLocallyFiniteMeasure (volume : Measure (Rn d)) := inferInstance
  have hf_li : LocallyIntegrable f volume :=
    hf.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hφ_li : LocallyIntegrable φ volume :=
    hφ_mem.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hρf_smooth := bumpConvolve_smooth ρ f hf_li
  have hρφ_smooth := bumpConvolve_smooth ρ φ hφ_li
  have hρf_meas : AEStronglyMeasurable (bumpConvolve ρ f) volume :=
    hρf_smooth.continuous.aestronglyMeasurable
  have hρφ_meas : AEStronglyMeasurable (bumpConvolve ρ φ) volume :=
    hρφ_smooth.continuous.aestronglyMeasurable
  have hf_meas := hf.aestronglyMeasurable
  have hφ_meas := hφ_mem.aestronglyMeasurable
  -- Three-way triangle: f - ρ⋆f = (f - φ) + (φ - ρ⋆φ) + (ρ⋆φ - ρ⋆f)
  have h_split : (f - bumpConvolve ρ f) =
      (f - φ) + (φ - bumpConvolve ρ φ) + (bumpConvolve ρ φ - bumpConvolve ρ f) := by
    ext x; simp
  -- Bound each piece
  have h1 : eLpNorm (f - φ) 2 volume ≤ ENNReal.ofReal (ε / 3) := hφ_close
  have h2 : eLpNorm (φ - bumpConvolve ρ φ) 2 volume < ENNReal.ofReal (ε / 3) :=
    hδ₀_spec ρ hρ
  have h3 : eLpNorm (bumpConvolve ρ φ - bumpConvolve ρ f) 2 volume ≤
      ENNReal.ofReal (ε / 3) :=
    (eLpNorm_bumpConvolve_sub ρ φ f hφ_mem hf).trans (by rwa [eLpNorm_sub_comm])
  -- Chain: two applications of eLpNorm triangle inequality
  have h_tri₁ : eLpNorm ((f - φ) + (φ - bumpConvolve ρ φ)) 2 volume ≤
      eLpNorm (f - φ) 2 volume + eLpNorm (φ - bumpConvolve ρ φ) 2 volume :=
    eLpNorm_add_le (hf_meas.sub hφ_meas) (hφ_meas.sub hρφ_meas) one_le_two
  have h_tri₂ : eLpNorm (f - bumpConvolve ρ f) 2 volume ≤
      eLpNorm ((f - φ) + (φ - bumpConvolve ρ φ)) 2 volume +
      eLpNorm (bumpConvolve ρ φ - bumpConvolve ρ f) 2 volume := by
    rw [h_split]
    exact eLpNorm_add_le ((hf_meas.sub hφ_meas).add (hφ_meas.sub hρφ_meas))
      (hρφ_meas.sub hρf_meas) one_le_two
  -- Final arithmetic
  calc eLpNorm (f - bumpConvolve ρ f) 2 volume
      ≤ (eLpNorm (f - φ) 2 volume + eLpNorm (φ - bumpConvolve ρ φ) 2 volume) +
        eLpNorm (bumpConvolve ρ φ - bumpConvolve ρ f) 2 volume :=
          le_add_of_le_add_right h_tri₂ h_tri₁
    _ ≤ (eLpNorm (f - φ) 2 volume + eLpNorm (φ - bumpConvolve ρ φ) 2 volume) +
        ENNReal.ofReal (ε / 3) :=
          add_le_add_right h3 (eLpNorm (f - φ) 2 volume + eLpNorm (φ - bumpConvolve ρ φ) 2 volume)
    _ < (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) + ENNReal.ofReal (ε / 3) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top
          (ENNReal.add_lt_add_of_le_of_lt
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1) h1 h2)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε3.le hε3.le, ← ENNReal.ofReal_add (by linarith) hε3.le]
        congr 1; ring

/-- Chain rule for `u ↦ ρ.normed(x - u)`: the partial derivative in direction `eᵢ`
    is the negation of the partial derivative of `ρ.normed` at the translated point. -/
private lemma fderiv_bump_translate_apply (ρ : ContDiffBump (0 : Rn d)) (x u : Rn d) (i : Fin d) :
    fderiv ℝ (fun y => ρ.normed volume (x - y)) u (EuclideanSpace.single i 1) =
    -(fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1)) := by
  set eᵢ := EuclideanSpace.single i (1 : ℝ)
  -- ρ.normed is differentiable (it's C^1, hence differentiable)
  have hρ_C1 : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed (n := 1)
  have hρ_diff : Differentiable ℝ (ρ.normed volume) := hρ_C1.differentiable one_ne_zero
  -- The translation u ↦ x - u has derivative -id at every point
  have hτ : HasFDerivAt (fun y : (Rn d) => x - y) (-ContinuousLinearMap.id ℝ (Rn d)) u := by
    have hneg : HasFDerivAt (fun y : (Rn d) => -y) (-ContinuousLinearMap.id ℝ (Rn d)) u :=
      (hasFDerivAt_id u).neg
    have hsub : (fun y : (Rn d) => x - y) = fun y => x + (-y) := by
      funext y; rw [sub_eq_add_neg]
    rw [hsub]
    exact HasFDerivAt.const_add x hneg
  -- Compose: HasFDerivAt for u ↦ ρ.normed (x - u)
  have hcomp : HasFDerivAt (fun u => ρ.normed volume (x - u))
      ((fderiv ℝ (ρ.normed volume) (x - u)).comp (-ContinuousLinearMap.id ℝ (Rn d))) u :=
    (hρ_diff.differentiableAt.hasFDerivAt).comp u hτ
  rw [hcomp.fderiv]
  -- Evaluate at eᵢ: ((fderiv ρ.normed (x-u)).comp (-id)) eᵢ = -fderiv ρ.normed (x-u) eᵢ
  simp [ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_apply]

/-- Real part of `bumpConvolve` is Mathlib's real convolution against `h.re`. -/
private lemma bumpConvolve_re_apply (ρ : ContDiffBump (0 : Rn d)) (h : Rn d → ℂ) (x : (Rn d)) :
    (bumpConvolve ρ h x).re =
      MeasureTheory.convolution (ρ.normed volume) (fun y => (h y).re)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := rfl

/-- Imaginary part of `bumpConvolve` is Mathlib's real convolution against `h.im`. -/
private lemma bumpConvolve_im_apply (ρ : ContDiffBump (0 : Rn d)) (h : Rn d → ℂ) (x : (Rn d)) :
    (bumpConvolve ρ h x).im =
      MeasureTheory.convolution (ρ.normed volume) (fun y => (h y).im)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := rfl

/-- A projection of the derivative of `bumpConvolve` is computed by differentiating the
    real convolution for the corresponding projected component. -/
private lemma fderiv_bumpConvolve_component_apply
    (L : ℂ →L[ℝ] ℝ) (component : Rn d → ℝ)
    (ρ : ContDiffBump (0 : Rn d)) (h : Rn d → ℂ) (hh : MemLp h 2 volume)
    (x : (Rn d)) (i : Fin d)
    (hcomponent_li : LocallyIntegrable component volume)
    (hcomponent_eq : (fun y => L (bumpConvolve ρ h y)) =
      MeasureTheory.convolution (ρ.normed volume) component
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) :
    L (fderiv ℝ (bumpConvolve ρ h) x (EuclideanSpace.single i 1)) =
    (MeasureTheory.convolution (fderiv ℝ (ρ.normed volume)) component
      (ContinuousLinearMap.precompL (Rn d) (ContinuousLinearMap.lsmul ℝ ℝ)) volume x)
      (EuclideanSpace.single i 1) := by
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  haveI : IsLocallyFiniteMeasure (volume : Measure (Rn d)) := inferInstance
  have hh_li : LocallyIntegrable h volume :=
    hh.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hρ_C1 : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed (n := 1)
  have hcomponent_fd : HasFDerivAt
      (MeasureTheory.convolution (ρ.normed volume) component
        (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      (MeasureTheory.convolution (fderiv ℝ (ρ.normed volume)) component
        (ContinuousLinearMap.precompL (Rn d) (ContinuousLinearMap.lsmul ℝ ℝ)) volume x) x :=
    HasCompactSupport.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      ρ.hasCompactSupport_normed hρ_C1 hcomponent_li x
  have hbc_smooth : ContDiff ℝ ∞ (bumpConvolve ρ h) := bumpConvolve_smooth ρ h hh_li
  have hbc_hfd : HasFDerivAt (bumpConvolve ρ h) (fderiv ℝ (bumpConvolve ρ h) x) x :=
    ((hbc_smooth.differentiable
        (by exact_mod_cast ENat.top_ne_zero)).differentiableAt).hasFDerivAt
  have hcomponent_alt : HasFDerivAt (fun y => L (bumpConvolve ρ h y))
      (L.comp (fderiv ℝ (bumpConvolve ρ h) x)) x :=
    L.hasFDerivAt.comp x hbc_hfd
  rw [hcomponent_eq] at hcomponent_alt
  have hD_eq := hcomponent_fd.unique hcomponent_alt
  rw [hD_eq]
  simp [ContinuousLinearMap.comp_apply]

/-- The real part of the partial derivative of `bumpConvolve` at `x` in direction
    `eᵢ` is an explicit real integral involving `∂ᵢρ.normed` and `h.re`. -/
private lemma fderiv_bumpConvolve_re_apply
    (ρ : ContDiffBump (0 : Rn d)) (h : Rn d → ℂ) (hh : MemLp h 2 volume)
    (x : (Rn d)) (i : Fin d) :
    (fderiv ℝ (bumpConvolve ρ h) x (EuclideanSpace.single i 1)).re =
    (MeasureTheory.convolution (fderiv ℝ (ρ.normed volume)) (fun u => (h u).re)
      (ContinuousLinearMap.precompL (Rn d) (ContinuousLinearMap.lsmul ℝ ℝ)) volume x)
      (EuclideanSpace.single i 1) := by
  have hh_li : LocallyIntegrable h volume :=
    hh.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact fderiv_bumpConvolve_component_apply Complex.reCLM (fun u => (h u).re)
    ρ h hh x i (locallyIntegrable_complexCLM Complex.reCLM hh_li)
    (by funext y; exact bumpConvolve_re_apply ρ h y)

/-- The imaginary part of the partial derivative of `bumpConvolve` at `x` in direction
    `eᵢ`, in CLM-application form (mirror of `fderiv_bumpConvolve_re_apply`). -/
private lemma fderiv_bumpConvolve_im_apply
    (ρ : ContDiffBump (0 : Rn d)) (h : Rn d → ℂ) (hh : MemLp h 2 volume)
    (x : (Rn d)) (i : Fin d) :
    (fderiv ℝ (bumpConvolve ρ h) x (EuclideanSpace.single i 1)).im =
    (MeasureTheory.convolution (fderiv ℝ (ρ.normed volume)) (fun u => (h u).im)
      (ContinuousLinearMap.precompL (Rn d) (ContinuousLinearMap.lsmul ℝ ℝ)) volume x)
      (EuclideanSpace.single i 1) := by
  have hh_li : LocallyIntegrable h volume :=
    hh.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact fderiv_bumpConvolve_component_apply Complex.imCLM (fun u => (h u).im)
    ρ h hh x i (locallyIntegrable_complexCLM Complex.imCLM hh_li)
    (by funext y; exact bumpConvolve_im_apply ρ h y)

/-- Complex-coerced chain rule for the translated bump: the partial derivative
    of `u ↦ (ρ.normed(x-u) : ℂ)` in direction `eᵢ` equals the complex coercion
    of `-(∂ᵢρ.normed)(x-u)`.  Lifts `fderiv_bump_translate_apply` through
    `Complex.ofRealCLM`. -/
private lemma fderiv_bump_translate_ofReal_apply
    (ρ : ContDiffBump (0 : Rn d)) (x u : (Rn d)) (i : Fin d) :
    fderiv ℝ (fun y => ((ρ.normed volume) (x - y) : ℂ)) u (EuclideanSpace.single i 1) =
    -((fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1) : ℂ)) := by
  have hρ_C1 : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed (n := 1)
  have hτ_diff : Differentiable ℝ (fun y : (Rn d) => x - y) :=
    (differentiable_const _).sub differentiable_id
  have hρ_diff_at : DifferentiableAt ℝ (ρ.normed volume) (x - u) :=
    (hρ_C1.differentiable (by norm_num)).differentiableAt
  have hf_diff : DifferentiableAt ℝ (fun y => (ρ.normed volume) (x - y)) u :=
    hρ_diff_at.comp u hτ_diff.differentiableAt
  -- Rewrite as Complex.ofRealCLM ∘ (real translated bump), then chain rule for fderiv
  rw [show (fun y => ((ρ.normed volume) (x - y) : ℂ)) =
        Complex.ofRealCLM ∘ (fun y => (ρ.normed volume) (x - y)) from rfl,
      fderiv_comp u Complex.ofRealCLM.differentiableAt hf_diff]
  rw [ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_bump_translate_apply ρ x u i]
  exact Complex.ofReal_neg _

/-- Applying the weak-derivative identity to the test function
    `u ↦ (ρ.normed(x-u) : ℂ)`, after substituting its derivative via
    `fderiv_bump_translate_ofReal_apply` and bridging the `Lp` coercions, gives
    `∫ h(u) · ∂ᵢρ.normed(x-u) du = ∫ dh(u) · ρ.normed(x-u) du`. -/
private lemma weak_deriv_against_translated_bump
    (ρ : ContDiffBump (0 : Rn d)) (i : Fin d)
    (h dh : Rn d → ℂ) (hh : MemLp h 2 volume) (hdh : MemLp dh 2 volume)
    (h_wk : HasWeakDerivative (hh.toLp h) i (hdh.toLp dh))
    (x : (Rn d)) :
    ∫ u, h u * ((fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1) : ℂ))
      ∂(volume : Measure (Rn d)) =
    ∫ u, dh u * (((ρ.normed volume) (x - u)) : ℂ) ∂(volume : Measure (Rn d)) := by
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  haveI : IsLocallyFiniteMeasure (volume : Measure (Rn d)) := inferInstance
  have hψ_re_smooth : ContDiff ℝ ∞ (fun u : (Rn d) => (ρ.normed volume) (x - u)) :=
    ρ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hψ_smooth : ContDiff ℝ ∞ (fun u : (Rn d) => ((ρ.normed volume) (x - u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ_re_smooth
  -- Compact support of the real translated bump
  have hρ_tsupp_compact : IsCompact (tsupport (ρ.normed volume)) :=
    ρ.hasCompactSupport_normed
  have hψ_re_supp : HasCompactSupport (fun u : (Rn d) => (ρ.normed volume) (x - u)) := by
    refine HasCompactSupport.intro
      (K := (fun v : (Rn d) => x - v) '' tsupport (ρ.normed volume))
      (hρ_tsupp_compact.image (continuous_const.sub continuous_id)) ?_
    intro u hu
    have hxu : x - u ∉ tsupport (ρ.normed volume) :=
      fun hmem => hu ⟨x - u, hmem, by abel_nf⟩
    exact image_eq_zero_of_notMem_tsupport hxu
  -- Lift compact support to the complex coercion via ofRealCLM ∘ ·
  have hψ_supp : HasCompactSupport (fun u : (Rn d) => ((ρ.normed volume) (x - u) : ℂ)) := by
    rw [show (fun u : (Rn d) => ((ρ.normed volume) (x - u) : ℂ)) =
            Complex.ofRealCLM ∘ (fun u : (Rn d) => (ρ.normed volume) (x - u)) from rfl]
    exact hψ_re_supp.comp_left (map_zero _)
  -- Apply the weak-derivative identity to ψ_ℂ
  have hwk := h_wk (fun u : (Rn d) => ((ρ.normed volume) (x - u) : ℂ)) hψ_smooth hψ_supp
  -- Lp-coercion bridges
  have h_ae : (hh.toLp h : Rn d → ℂ) =ᵐ[volume] h := hh.coeFn_toLp
  have dh_ae : (hdh.toLp dh : Rn d → ℂ) =ᵐ[volume] dh := hdh.coeFn_toLp
  -- Transform LHS of hwk: substitute fderiv via fderiv_bump_translate_ofReal_apply,
  -- bridge Lp, factor out −
  have lhs_transform :
      (∫ u, (hh.toLp h) u *
        fderiv ℝ (fun y : (Rn d) => ((ρ.normed volume) (x - y) : ℂ)) u
          (EuclideanSpace.single i 1)) =
      -(∫ u, h u *
        ((fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1) : ℂ))) := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [h_ae] with u hu
    rw [hu, fderiv_bump_translate_ofReal_apply ρ x u i]
    ring
  -- Transform RHS of hwk: bridge Lp on the inner integral
  have rhs_transform :
      (∫ u, (hdh.toLp dh) u * (((ρ.normed volume) (x - u)) : ℂ)) =
      ∫ u, dh u * (((ρ.normed volume) (x - u)) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [dh_ae] with u hu
    rw [hu]
  rw [lhs_transform, rhs_transform] at hwk
  -- hwk now reads −(∫ h · ∂ᵢρ.normed) = −(∫ dh · ρ.normed); cancel the negation
  exact neg_inj.mp hwk

/-- Derivative of convolution equals convolution of weak derivative:
      ∂ᵢ(ρ ⋆ h)(x) = (ρ ⋆ dh)(x) pointwise. -/
private lemma clm_mul_ofReal (L : ℂ →L[ℝ] ℝ) (z : ℂ) (r : ℝ) :
    L (z * (r : ℂ)) = L z * r := by
  have hz : z * (r : ℂ) = r • z := by rw [Complex.real_smul]; ring
  rw [hz, L.map_smul, smul_eq_mul]
  ring

/-- Real/imaginary-agnostic core of `bumpConvolve_fderiv_eq`: for any `L : ℂ →L[ℝ] ℝ` that
    agrees with `bumpConvolve`'s own componentwise definition (as `Complex.reCLM`/`Complex.imCLM`
    do, via `hL_apply`), the `L`-component of `∂ᵢ(bumpConvolve ρ h) x` equals the `L`-component of
    `bumpConvolve ρ dh x`. `bumpConvolve_fderiv_eq`'s two `Complex.ext` cases are one instantiation
    of this lemma each. -/
private lemma bumpConvolve_fderiv_eq_component (L : ℂ →L[ℝ] ℝ) (i : Fin d)
    (h dh : Rn d → ℂ) (hh : MemLp h 2 volume) (hdh : MemLp dh 2 volume)
    (h_wk : HasWeakDerivative (hh.toLp h) i (hdh.toLp dh))
    (ρ : ContDiffBump (0 : Rn d)) (x : (Rn d))
    (hL_apply : ∀ (f : Rn d → ℂ) (y : (Rn d)), L (bumpConvolve ρ f y) =
      MeasureTheory.convolution (ρ.normed volume) (fun u => L (f u))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume y) :
    L (fderiv ℝ (bumpConvolve ρ h) x (EuclideanSpace.single i 1)) = L (bumpConvolve ρ dh x) := by
  -- Measure instances ---------------------------------------------------------
  haveI : (volume : Measure (Rn d)).IsAddHaarMeasure := inferInstance
  haveI : IsLocallyFiniteMeasure (volume : Measure (Rn d)) := inferInstance
  -- Local integrability of h, dh and the L-component of h ---------------------
  have hh_li : LocallyIntegrable h volume :=
    hh.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hdh_li : LocallyIntegrable dh volume :=
    hdh.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcomponent_li : LocallyIntegrable (fun u => L (h u)) volume :=
    locallyIntegrable_complexCLM L hh_li
  -- Smoothness/continuity/compact-support of fderiv ρ.normed ------------------
  have hρ_smooth : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have hfderiv_smooth : ContDiff ℝ ∞ (fderiv ℝ (ρ.normed volume)) :=
    (contDiff_infty_iff_fderiv.mp hρ_smooth).2
  have hfderiv_cont : Continuous (fderiv ℝ (ρ.normed volume)) := hfderiv_smooth.continuous
  have hfderiv_supp : HasCompactSupport (fderiv ℝ (ρ.normed volume)) :=
    ρ.hasCompactSupport_normed.fderiv ℝ
  -- Cache the CLM-valued bilinear map under a named variable -----------------
  -- `set` primes the instance cache so the next call to `convolutionExists_left` doesn't have
  -- to re-elaborate `precompL (Rn d) lsmul` from scratch (re-elaboration from scratch is slow).
  set Lpre : ((Rn d) →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] ((Rn d) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precompL (Rn d) (ContinuousLinearMap.lsmul ℝ ℝ) with hLpre_def
  -- Integrability of the CLM-valued convolution integrand ---------------------
  -- Needed by `ContinuousLinearMap.integral_apply` later.
  have hint : Integrable
      (fun t => Lpre (fderiv ℝ (ρ.normed volume) t) (L (h (x - t)))) volume :=
    HasCompactSupport.convolutionExists_left Lpre hfderiv_supp hfderiv_cont hcomponent_li x
  -- Apply the complex weak-derivative test-function identity ------------------
  have h_star := weak_deriv_against_translated_bump ρ i h dh hh hdh h_wk x
  -- h_star : ∫ u, h u * (∂ᵢρ.normed(x-u) : ℂ) = ∫ u, dh u * (ρ.normed(x-u) : ℂ)
  -- Step 1: rewrite LHS via fderiv_bumpConvolve_component_apply, unfold convolution, push apply
  rw [fderiv_bumpConvolve_component_apply L (fun u => L (h u)) ρ h hh x i
        hcomponent_li (funext fun y => hL_apply h y),
      MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [hLpre_def, ContinuousLinearMap.precompL_apply,
             ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- LHS = ∫ t, fderiv ρ.normed t eᵢ * L (h (x-t)) ∂volume
  -- Step 2: change of variables u = x - t on LHS
  rw [← MeasureTheory.integral_sub_left_eq_self
      (fun t => fderiv ℝ (ρ.normed volume) t (EuclideanSpace.single i 1)
                  * L (h (x - t))) volume x]
  simp only [show ∀ y, x - (x - y) = y from fun y => by abel]
  -- LHS = ∫ y, fderiv ρ.normed (x-y) eᵢ * L (h y) ∂volume
  -- Step 3: rewrite RHS via hL_apply, unfold convolution
  rw [hL_apply dh x, MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← MeasureTheory.integral_sub_left_eq_self
      (fun t => (ρ.normed volume) t * L (dh (x - t))) volume x]
  simp only [show ∀ y, x - (x - y) = y from fun y => by abel]
  -- RHS = ∫ y, ρ.normed(x-y) * L (dh y) ∂volume
  -- Step 4: continuity + compact support of the translated bump pieces
  have hr_cont : Continuous (fun u : (Rn d) =>
      fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1)) :=
    (hfderiv_cont.comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  have hr_supp : HasCompactSupport (fun u : (Rn d) =>
      fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1)) := by
    apply HasCompactSupport.intro
      (K := (fun v : (Rn d) => x - v) '' tsupport (fderiv ℝ (ρ.normed volume)))
      (hfderiv_supp.image (continuous_const.sub continuous_id))
    intro u hu
    have hxu : x - u ∉ tsupport (fderiv ℝ (ρ.normed volume)) :=
      fun hin => hu ⟨x - u, hin, by abel_nf⟩
    rw [image_eq_zero_of_notMem_tsupport hxu]
    simp only [ContinuousLinearMap.zero_apply]
  have hs_cont : Continuous (fun u : (Rn d) => (ρ.normed volume) (x - u)) :=
    ρ.continuous_normed.comp (continuous_const.sub continuous_id)
  have hs_supp : HasCompactSupport (fun u : (Rn d) => (ρ.normed volume) (x - u)) := by
    apply HasCompactSupport.intro
      (K := (fun v : (Rn d) => x - v) '' tsupport (ρ.normed volume))
      (ρ.hasCompactSupport_normed.image (continuous_const.sub continuous_id))
    intro u hu
    exact image_eq_zero_of_notMem_tsupport (fun hin => hu ⟨x - u, hin, by abel_nf⟩)
  -- Step 5: integrability of the complex-valued h_star integrands
  have h_lhs_int : Integrable
      (fun u => h u *
        ((fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1) : ℂ))) volume := by
    have key := hh_li.integrable_smul_left_of_hasCompactSupport hr_cont hr_supp
    refine key.congr ?_
    filter_upwards with u
    rw [Complex.real_smul]; ring
  have h_rhs_int : Integrable
      (fun u => dh u * (((ρ.normed volume) (x - u)) : ℂ)) volume := by
    have key := hdh_li.integrable_smul_left_of_hasCompactSupport hs_cont hs_supp
    refine key.congr ?_
    filter_upwards with u
    rw [Complex.real_smul]; ring
  -- Step 6: take the L-component of h_star and push it inside both integrals
  have h_lhs_L :
      L (∫ u, h u *
        ((fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1) : ℂ)) ∂volume) =
      ∫ u, L (h u *
        ((fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1) : ℂ))) ∂volume :=
    (L.integral_comp_comm h_lhs_int).symm
  have h_rhs_L :
      L (∫ u, dh u * (((ρ.normed volume) (x - u)) : ℂ) ∂volume) =
      ∫ u, L (dh u * (((ρ.normed volume) (x - u)) : ℂ)) ∂volume :=
    (L.integral_comp_comm h_rhs_int).symm
  have h_star_L :
      L (∫ u, h u *
        ((fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1) : ℂ)) ∂volume) =
      L (∫ u, dh u * (((ρ.normed volume) (x - u)) : ℂ) ∂volume) :=
    congrArg L h_star
  rw [h_lhs_L, h_rhs_L] at h_star_L
  simp only [clm_mul_ofReal] at h_star_L
  -- Step 7: line up multiplication order between goal and h_star_L
  have hLHS_eq :
      ∫ y, fderiv ℝ (ρ.normed volume) (x - y) (EuclideanSpace.single i 1) * L (h y) ∂volume =
      ∫ u, L (h u) * fderiv ℝ (ρ.normed volume) (x - u) (EuclideanSpace.single i 1) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y using mul_comm _ _
  have hRHS_eq :
      ∫ y, (ρ.normed volume) (x - y) * L (dh y) ∂volume =
      ∫ u, L (dh u) * (ρ.normed volume) (x - u) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y using mul_comm _ _
  rw [hLHS_eq, hRHS_eq]
  exact h_star_L

/-- Derivative of convolution equals convolution of weak derivative:
      ∂ᵢ(ρ ⋆ h)(x) = (ρ ⋆ dh)(x)  pointwise. -/
private lemma bumpConvolve_fderiv_eq (i : Fin d)
    (h dh : Rn d → ℂ) (hh : MemLp h 2 volume) (hdh : MemLp dh 2 volume)
    (h_wk : HasWeakDerivative (hh.toLp h) i (hdh.toLp dh))
    (ρ : ContDiffBump (0 : Rn d)) :
    ∀ x, fderiv ℝ (bumpConvolve ρ h) x (EuclideanSpace.single i 1) =
      bumpConvolve ρ dh x := fun x =>
  Complex.ext
    (bumpConvolve_fderiv_eq_component Complex.reCLM i h dh hh hdh h_wk ρ x
      fun f y => bumpConvolve_re_apply ρ f y)
    (bumpConvolve_fderiv_eq_component Complex.imCLM i h dh hh hdh h_wk ρ x
      fun f y => bumpConvolve_im_apply ρ f y)

/-- Convert an eLpNorm bound on bare functions to a norm bound on toLp elements. -/
private lemma norm_toLp_sub_lt {f g : Rn d → ℂ}
    (hf : MemLp f 2 (volume : Measure (Rn d))) (hg : MemLp g 2 (volume : Measure (Rn d)))
    {ε : ℝ} (hε : 0 < ε)
    (h : eLpNorm (f - g) 2 (volume : Measure (Rn d)) < ENNReal.ofReal ε) :
    ‖hf.toLp f - hg.toLp g‖ < ε := by
  rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub _ _),
      eLpNorm_congr_ae (hf.coeFn_toLp.sub hg.coeFn_toLp)]
  have h_ne : eLpNorm (f - g) 2 volume ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h.le
  calc (eLpNorm (f - g) 2 volume).toReal
      < (ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_lt_toReal h_ne ENNReal.ofReal_ne_top).mpr h
    _ = ε := ENNReal.toReal_ofReal hε.le

/-- **Shared mollification construction**, parametrized by an arbitrary nonempty
    `Finite` index `ι` of directions to control simultaneously. A single bump
    convolution `ε`-approximates `h_R` and, for every `j : ι`, its truncated weak
    derivative `dh_R j` in direction `dir j`, all at once. `mollify_compactly_supported`
    (`ι := Unit`) and `mollify_compactly_supported_multi` (`ι := Fin d`, `dir := id`)
    both specialize this lemma; it exists so the bump-radius argument is maintained
    in exactly one place.

    Proof: pick a ContDiffBump ρ with rOut small enough that both
    ρ ⋆ h_R ≈ h_R and, for every j, ρ ⋆ dh_R j ≈ dh_R j in L², then use the derivative
    identity ∂_{dir j}(ρ ⋆ h_R) = ρ ⋆ dh_R j to couple the function bound to each
    derivative bound. -/
lemma mollify_compactly_supported_family {ι : Type*} [Finite ι] [Nonempty ι]
    (dir : ι → Fin d) (h_R : Rn d → ℂ) (dh_R : ι → Rn d → ℂ)
    (hh : MemLp h_R 2 volume) (hdh : ∀ j, MemLp (dh_R j) 2 volume)
    (hh_supp : HasCompactSupport h_R) (hdh_supp : ∀ j, HasCompactSupport (dh_R j))
    (h_wk : ∀ j, HasWeakDerivative (hh.toLp h_R) (dir j) ((hdh j).toLp (dh_R j)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : Rn d → ℂ) (hφ : ContDiff ℝ ∞ φ) (hφ_supp : HasCompactSupport φ),
      ‖hh.toLp h_R - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖ < ε ∧
      ∀ j, ‖(hdh j).toLp (dh_R j) -
        (memLp_partialDeriv φ (dir j) hφ hφ_supp).toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single (dir j) 1))‖ < ε := by
  haveI : Fintype ι := Fintype.ofFinite ι
  -- L² convergence radii: δ₀ for h_R; δ_dg j for each dh_R j.
  obtain ⟨δ₀, hδ₀_pos, happrox₀⟩ := bumpConvolve_L2_tendsto h_R hh ε hε
  choose δ_dg hδ_dg_pos happrox_dg using
    fun j => bumpConvolve_L2_tendsto (dh_R j) (hdh j) ε hε
  -- A single δ small enough to dominate all the convergence facts.
  set δ := min δ₀ (Finset.univ.inf' Finset.univ_nonempty δ_dg) with _hδ_def
  have hδ_dg_inf_pos : 0 < Finset.univ.inf' Finset.univ_nonempty δ_dg :=
    (Finset.lt_inf'_iff _).mpr (fun j _ => hδ_dg_pos j)
  have hδ_pos : 0 < δ := lt_min hδ₀_pos hδ_dg_inf_pos
  have hδ_le_δ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδ_le_dg : ∀ j, δ ≤ δ_dg j := fun j =>
    le_trans (min_le_right _ _) (Finset.inf'_le δ_dg (Finset.mem_univ j))
  let ρ : ContDiffBump (0 : Rn d) := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hρ_le_δ₀ : ρ.rOut ≤ δ₀ := hδ_le_δ₀
  have hρ_le_dg : ∀ j, ρ.rOut ≤ δ_dg j := hδ_le_dg
  -- A single φ approximates all targets simultaneously.
  set φ := bumpConvolve ρ h_R with _hφ_def
  haveI : IsLocallyFiniteMeasure (volume : Measure (Rn d)) := inferInstance
  have hli : LocallyIntegrable h_R volume :=
    hh.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hφ_smooth : ContDiff ℝ ∞ φ := bumpConvolve_smooth ρ h_R hli
  have hφ_supp : HasCompactSupport φ := bumpConvolve_hasCompactSupport ρ h_R hh_supp
  -- Per-j derivative identity: ∂_{dir j} φ = bumpConvolve ρ (dh_R j) pointwise.
  have hderiv_eq : ∀ j,
      (fun x => fderiv ℝ φ x (EuclideanSpace.single (dir j) 1)) =
        bumpConvolve ρ (dh_R j) :=
    fun j => funext (bumpConvolve_fderiv_eq (dir j) h_R (dh_R j)
      hh (hdh j) (h_wk j) ρ)
  -- L² closeness bounds (one for the function, one per direction).
  have h_close₀ : eLpNorm (h_R - φ) 2 volume < ENNReal.ofReal ε :=
    happrox₀ ρ hρ_le_δ₀
  have h_close_dg : ∀ j,
      eLpNorm (dh_R j - bumpConvolve ρ (dh_R j)) 2 volume < ENNReal.ofReal ε :=
    fun j => happrox_dg j ρ (hρ_le_dg j)
  refine ⟨φ, hφ_smooth, hφ_supp, ?_, ?_⟩
  · -- ‖toLp h_R - toLp φ‖ < ε
    exact norm_toLp_sub_lt hh
      (memLp_of_smooth_compactSupport φ hφ_smooth hφ_supp) hε h_close₀
  · -- ∀ j, ‖toLp (dh_R j) - toLp ∂_{dir j}φ‖ < ε
    intro j
    have hdh_li : LocallyIntegrable (dh_R j) volume :=
      (hdh j).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hconv_dh_smooth : ContDiff ℝ ∞ (bumpConvolve ρ (dh_R j)) :=
      bumpConvolve_smooth ρ (dh_R j) hdh_li
    have hconv_dh_supp : HasCompactSupport (bumpConvolve ρ (dh_R j)) :=
      bumpConvolve_hasCompactSupport ρ (dh_R j) (hdh_supp j)
    have h_memLp_deriv := memLp_partialDeriv φ (dir j) hφ_smooth hφ_supp
    have h_memLp_conv :=
      memLp_of_smooth_compactSupport _ hconv_dh_smooth hconv_dh_supp
    -- The two Lp elements agree since the functions match pointwise.
    have h_toLp_eq : h_memLp_deriv.toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single (dir j) 1)) =
        h_memLp_conv.toLp (bumpConvolve ρ (dh_R j)) :=
      Subtype.ext (AEEqFun.ext (h_memLp_deriv.coeFn_toLp.trans
        (by rw [hderiv_eq j]; exact h_memLp_conv.coeFn_toLp.symm)))
    rw [h_toLp_eq]
    exact norm_toLp_sub_lt (hdh j) h_memLp_conv hε (h_close_dg j)

/-- **Mollification of compactly supported L² functions**: simultaneous
    approximation of function and weak derivative by smooth c.s. functions.
    This is the `ι := Unit` specialization of the shared
    `mollify_compactly_supported_family` construction; see
    `mollify_compactly_supported_multi` for the `Fin d` sibling. We unpack the
    trivial `Unit`-indexed output back into the bare, un-indexed shape this
    lemma has always had. -/
lemma mollify_compactly_supported (i : Fin d)
    (h_R : Rn d → ℂ) (dh_R : Rn d → ℂ)
    (hh : MemLp h_R 2 volume) (hdh : MemLp dh_R 2 volume)
    (hh_supp : HasCompactSupport h_R) (hdh_supp : HasCompactSupport dh_R)
    (h_wk : HasWeakDerivative (hh.toLp h_R) i (hdh.toLp dh_R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : Rn d → ℂ) (hφ : ContDiff ℝ ∞ φ) (hφ_supp : HasCompactSupport φ),
      ‖hh.toLp h_R - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖ < ε ∧
      ‖hdh.toLp dh_R -
        (memLp_partialDeriv φ i hφ hφ_supp).toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < ε := by
  obtain ⟨φ, hφ, hφ_supp, hφ_close, hdφ_close⟩ :=
    mollify_compactly_supported_family (ι := Unit) (fun _ => i) h_R (fun _ => dh_R)
      hh (fun _ => hdh) hh_supp (fun _ => hdh_supp) (fun _ => h_wk) ε hε
  exact ⟨φ, hφ, hφ_supp, hφ_close, hdφ_close ()⟩

/-- **Multi-direction mollification step of Meyers-Serrin**: a single bump
    convolution approximates `h_R` and all three `dh_R i` in L² simultaneously.
    This is the `ι := Fin d`, `dir := id` specialization of the shared
    `mollify_compactly_supported_family` construction; see
    `mollify_compactly_supported` for the single-direction sibling. -/
lemma mollify_compactly_supported_multi [NeZero d]
    (h_R : Rn d → ℂ) (dh_R : Fin d → Rn d → ℂ)
    (hh : MemLp h_R 2 volume) (hdh : ∀ i, MemLp (dh_R i) 2 volume)
    (hh_supp : HasCompactSupport h_R)
    (hdh_supp : ∀ i, HasCompactSupport (dh_R i))
    (h_wk : ∀ i, HasWeakDerivative (hh.toLp h_R) i ((hdh i).toLp (dh_R i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : Rn d → ℂ) (hφ : ContDiff ℝ ∞ φ) (hφ_supp : HasCompactSupport φ),
      ‖hh.toLp h_R - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖ < ε ∧
      ∀ i, ‖(hdh i).toLp (dh_R i) -
        (memLp_partialDeriv φ i hφ hφ_supp).toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < ε :=
  mollify_compactly_supported_family (ι := Fin d) id h_R dh_R hh hdh hh_supp hdh_supp h_wk ε hε

end Spectra.Sobolev

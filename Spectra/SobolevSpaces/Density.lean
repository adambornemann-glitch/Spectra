/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/SobolevSpaces/Density.lean
-/
import Spectra.SobolevSpaces.WeakDerivative
import Mathlib.MeasureTheory.Function.ContinuousMapDense
/-!
# Density of Test Functions in L²(ℝ³)

This file proves the density chain `L² ← C_c ← C_c^∞`: continuous compactly supported functions
are dense in `L²(ℝ³)`, and smooth compactly supported functions are in turn dense among those,
so `C_c^∞(ℝ³)` is dense in `L²(ℝ³)`.

## Main statements

* `dense_continuous_compactSupport_L2`: continuous compactly supported functions are dense in `L²`.
* `smooth_approx_continuous_compactSupport`: a continuous compactly supported function is
  approximated, in `L²`, by a smooth compactly supported one.
* `dense_test_functions_L2`: `C_c^∞(ℝ³)` is dense in `L²(ℝ³)` — the capstone density result.

## Implementation notes

The chain factors as `L² ←ε/2— C_c ←ε/2— C_c^∞`: `dense_continuous_compactSupport_L2` supplies
the first ε/2 approximation (via Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), and
`smooth_approx_continuous_compactSupport` supplies the second, via mollification
(`exists_smooth_uniform_approx`, a uniform-continuity + convolution argument) combined with the
elementary `L²`-norm bound `eLpNorm_le_of_compactSupport_bound`.

## References

* [Adams, Fournier, *Sobolev Spaces*][adams2003]
* [Lieb, Loss, *Analysis*][lieb2001], Chapter 2.
-/
open MeasureTheory Complex
open scoped ENNReal Pointwise ContDiff

namespace Spectra.Sobolev

/-- Continuous compactly supported functions are dense in L²(ℝ³). -/
lemma dense_continuous_compactSupport_L2 :
    Dense {g : L2_R3 | ∃ (φ : R3 → ℂ),
      Continuous φ ∧ HasCompactSupport φ ∧
      (g : R3 → ℂ) =ᵐ[volume] φ} := by
  rw [Metric.dense_iff]
  intro g ε hε
  have hg := Lp.memLp g
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hε' : (ENNReal.ofReal (ε / 2)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Nat.ofNat_pos, div_pos_iff_of_pos_right]
    exact RCLike.ofReal_pos.mp hε
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  haveI : (volume : Measure R3).Regular := by
    infer_instance
  haveI : WeaklyLocallyCompactSpace R3 := by infer_instance
  haveI : R1Space R3 := by infer_instance
  obtain ⟨φ, hsupp, hclose, hcont, hmem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hp hε'
  use hmem.toLp φ
  constructor
  · simp only [Metric.mem_ball]
    rw [Lp.dist_def]
    have h1 : eLpNorm ((hmem.toLp φ : R3 → ℂ) - (g : R3 → ℂ)) 2 volume ≤
              ENNReal.ofReal (ε / 2) := by
      have hae : (hmem.toLp φ : R3 → ℂ) - (g : R3 → ℂ) =ᵐ[volume] φ - (g : R3 → ℂ) :=
        hmem.coeFn_toLp.sub (ae_eq_refl _)
      rw [eLpNorm_congr_ae (p := 2) hae, eLpNorm_sub_comm]
      exact hclose
    calc (eLpNorm ((hmem.toLp φ : R3 → ℂ) - (g : R3 → ℂ)) 2 volume).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          ENNReal.toReal_le_toReal
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1)
            ENNReal.ofReal_ne_top |>.mpr h1
      _ < ε := by rw [ENNReal.toReal_ofReal (by linarith)]; linarith
  · exact ⟨φ, hcont, hsupp, hmem.coeFn_toLp⟩

/-- **Core mollification**: a continuous compactly supported function on ℝ³
    can be uniformly approximated by smooth compactly supported functions -/
private lemma exists_smooth_uniform_approx
    (φ : R3 → ℂ) (hcont : Continuous φ) (hsupp : HasCompactSupport φ)
    (δ : ℝ) (hδ : 0 < δ) (radius : ℝ) (hradius : 0 < radius) :
    ∃ (ψ : R3 → ℂ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (tsupport ψ ⊆ tsupport φ + Metric.closedBall (0 : R3) radius) ∧
      (∀ x, ‖ψ x - φ x‖ ≤ δ) := by
  -- Phase 1: Uniform continuity on enlarged compact set
  set K := tsupport φ
  have hK : IsCompact K := hsupp.isCompact
  set K₂ := K + Metric.closedBall (0 : R3) (2 * radius)
  have hK₂ : IsCompact K₂ := hK.add (isCompact_closedBall _ _)
  have huc := hK₂.uniformContinuousOn_of_continuous hcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨ε, hε, huc_spec⟩ := huc (δ / 2) (half_pos hδ)
  -- Phase 2: Choose mollification radius
  set r := min (ε / 2) (radius / 2) with hr_def
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hr_ε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr_rad : r ≤ radius / 2 := min_le_right _ _
  have hr_le_radius : r ≤ radius := le_trans hr_rad (by linarith)
  -- Phase 3: Global oscillation bound
  have hosc : ∀ x y : R3, dist x y < r → ‖φ x - φ y‖ ≤ δ / 2 := by
    intro x y hxy
    by_cases hxK : x ∈ K
    · -- x ∈ K ⊆ K₂, and y ∈ ball(x,r) ⊆ K + ball(0,r) ⊆ K₂
      have hx₂ : x ∈ K₂ := Set.mem_add.mpr
        ⟨x, hxK, 0, Metric.mem_closedBall.mpr (by simp; grind only), by simp⟩
      have hy₂ : y ∈ K₂ := Set.mem_add.mpr
        ⟨x, hxK, y - x, by
          rw [Metric.mem_closedBall]
          calc dist (y - x) 0
              _ = ‖y - x‖ := by simp [dist_zero_right]
              _ = dist y x := (dist_eq_norm y x).symm
              _ = dist x y := dist_comm _ _
              _ ≤ r := le_of_lt hxy
              _ ≤ radius := hr_le_radius
              _ ≤ 2 * radius := by linarith, by abel⟩
      rw [← dist_eq_norm]
      exact le_of_lt (huc_spec x hx₂ y hy₂ (lt_trans hxy hr_ε))
    · -- x ∉ K: φ(x) = 0
      have hφx : φ x = 0 := by
        have : x ∉ Function.support φ := fun h => hxK (subset_tsupport φ h)
        exact Function.notMem_support.mp this
      rw [hφx, zero_sub, norm_neg]
      by_cases hyK : y ∈ K
      · -- y ∈ K, x ∉ K but x ∈ K + ball(0,r) ⊆ K₂
        have hx₂ : x ∈ K₂ := Set.mem_add.mpr
          ⟨y, hyK, x - y, by
            rw [Metric.mem_closedBall]
            calc dist (x - y) 0
              _ = ‖x - y‖ := by simp [dist_zero_right]
              _ = dist x y := (dist_eq_norm x y).symm
              _ ≤ r := le_of_lt hxy
              _ ≤ radius := hr_le_radius
              _ ≤ 2 * radius := by linarith, by abel⟩
        have hy₂ : y ∈ K₂ := Set.mem_add.mpr
          ⟨y, hyK, 0, Metric.mem_closedBall.mpr (by
            simp; exact le_of_lt hradius), by simp⟩
        calc ‖φ y‖ = ‖φ y - φ x‖ := by rw [hφx, sub_zero]
          _ = ‖φ x - φ y‖ := by rw [norm_sub_rev]
          _ ≤ δ / 2 := by
              rw [← dist_eq_norm]; exact le_of_lt (huc_spec x hx₂ y hy₂ (lt_trans hxy hr_ε))
      · -- Both ∉ K: φ(y) = 0
        have hφy : φ y = 0 := by
          have : y ∉ Function.support φ := fun h => hyK (subset_tsupport φ h)
          exact Function.notMem_support.mp this
        rw [hφy, norm_zero]; exact le_of_lt (half_pos hδ)
  -- Phase 4: Construct bump function and convolutions
  let ρ : ContDiffBump (0 : R3) := ⟨r / 2, r, by positivity, by linarith⟩
  set φ_re : R3 → ℝ := fun x => (φ x).re
  set φ_im : R3 → ℝ := fun x => (φ x).im
  have hcont_re : Continuous φ_re := Complex.continuous_re.comp hcont
  have hcont_im : Continuous φ_im := Complex.continuous_im.comp hcont
  have hmeas_re : AEStronglyMeasurable φ_re (volume : Measure R3) :=
    hcont_re.aestronglyMeasurable
  have hmeas_im : AEStronglyMeasurable φ_im (volume : Measure R3) :=
    hcont_im.aestronglyMeasurable
  set ψ_re :=
    MeasureTheory.convolution (ρ.normed volume) φ_re (ContinuousLinearMap.lsmul ℝ ℝ) volume
  set ψ_im :=
    MeasureTheory.convolution (ρ.normed volume) φ_im (ContinuousLinearMap.lsmul ℝ ℝ) volume
  set ψ : R3 → ℂ := fun x => ⟨ψ_re x, ψ_im x⟩
  refine ⟨ψ, ?smooth, ?compact_supp, ?supp_bound, ?unif_bound⟩
  case smooth =>
    haveI : (volume : Measure R3).IsAddHaarMeasure := by
      infer_instance
    have hli_re : LocallyIntegrable φ_re volume := hcont_re.locallyIntegrable
    have hli_im : LocallyIntegrable φ_im volume := hcont_im.locallyIntegrable
    have hsmooth_re : ContDiff ℝ ∞ ψ_re :=
      HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.hasCompactSupport_normed ρ.contDiff_normed hli_re
    have hsmooth_im : ContDiff ℝ ∞ ψ_im :=
      HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.hasCompactSupport_normed ρ.contDiff_normed hli_im
    show ContDiff ℝ ∞ ψ
    have hrw : ψ = fun x => ((ψ_re x : ℂ) + (ψ_im x : ℂ) * Complex.I) := by
      ext x; apply Complex.ext
      · simp [ψ, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im]
      · simp [ψ, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.ofReal_re, Complex.I_re, Complex.I_im]
    rw [hrw]
    exact (Complex.ofRealCLM.contDiff.comp hsmooth_re).add
      ((Complex.ofRealCLM.contDiff.comp hsmooth_im).mul contDiff_const)
  case compact_supp =>
    haveI : (volume : Measure R3).IsAddHaarMeasure := by
      infer_instance
    have hsupp_re : HasCompactSupport φ_re := hsupp.comp_left Complex.zero_re
    have hsupp_im : HasCompactSupport φ_im := hsupp.comp_left Complex.zero_im
    have hcs_re : HasCompactSupport ψ_re :=
      ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hsupp_re
    have hcs_im : HasCompactSupport ψ_im :=
      ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hsupp_im
    have h_sub : tsupport ψ ⊆ tsupport ψ_re ∪ tsupport ψ_im := by
      apply closure_minimal
      · intro x hx
        rw [Function.mem_support] at hx
        by_contra h
        rw [Set.mem_union, not_or] at h
        apply hx
        have hre0 : ψ_re x = 0 := image_eq_zero_of_notMem_tsupport h.1
        have him0 : ψ_im x = 0 := image_eq_zero_of_notMem_tsupport h.2
        show (⟨ψ_re x, ψ_im x⟩ : ℂ) = 0
        rw [hre0, him0]; rfl
      · exact (isClosed_tsupport _).union (isClosed_tsupport _)
    exact (hcs_re.isCompact.union hcs_im.isCompact).of_isClosed_subset
      (isClosed_tsupport _) h_sub
  case supp_bound =>
    haveI : (volume : Measure R3).IsAddHaarMeasure := by
      infer_instance
    have h_closed : IsClosed (tsupport φ + Metric.closedBall (0 : R3) radius) :=
      (hsupp.isCompact.add (isCompact_closedBall _ _)).isClosed
    apply closure_minimal _ h_closed
    have hρ_zero : ∀ t, t ∉ Metric.closedBall (0 : R3) r → ρ.normed volume t = 0 := by
      intro t ht
      have h_not_ball : t ∉ Metric.ball (0 : R3) r :=
        fun h => ht (Metric.ball_subset_closedBall h)
      have h_zero : (ρ : R3 → ℝ) t = 0 := by
        by_contra h
        have : t ∈ Function.support (ρ : R3 → ℝ) := Function.mem_support.mpr h
        rw [ρ.support_eq] at this
        exact h_not_ball this
      simp [ρ.normed_def, h_zero]
    have hφ_zero : ∀ x, x ∉ tsupport φ + Metric.closedBall (0 : R3) radius →
        ∀ t ∈ Metric.closedBall (0 : R3) r, φ (x - t) = 0 := by
      intro x hx t ht
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hx (Set.mem_add.mpr ⟨x - t, hmem, t,
        Metric.closedBall_subset_closedBall hr_le_radius ht, by abel⟩)
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hx_out
    apply hx; clear hx
    have h_re : ψ_re x = 0 := by
      change (MeasureTheory.convolution (ρ.normed volume) φ_re
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0
      simp only [MeasureTheory.convolution_def]
      refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      by_cases ht : t ∈ Metric.closedBall (0 : R3) r
      · rw [show φ_re (x - t) = (φ (x - t)).re from rfl, hφ_zero x hx_out t ht,
            Complex.zero_re, mul_zero]
        exact Real.ext_cauchy rfl
      · rw [hρ_zero t ht, zero_mul]
        exact Real.ext_cauchy rfl
    have h_im : ψ_im x = 0 := by
      change (MeasureTheory.convolution (ρ.normed volume) φ_im
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0
      simp only [MeasureTheory.convolution_def]
      refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      by_cases ht : t ∈ Metric.closedBall (0 : R3) r
      · rw [show φ_im (x - t) = (φ (x - t)).im from rfl, hφ_zero x hx_out t ht,
            Complex.zero_im, mul_zero]
        exact Real.ext_cauchy rfl
      · rw [hρ_zero t ht, zero_mul]
        exact Real.ext_cauchy rfl
    show (⟨ψ_re x, ψ_im x⟩ : ℂ) = 0
    rw [h_re, h_im]; rfl
  case unif_bound =>
    intro x₀
    -- Component-wise oscillation bounds (from hosc)
    have hosc_re : ∀ y ∈ Metric.ball x₀ ρ.rOut,
        dist (φ_re y) (φ_re x₀) ≤ δ / 2 := by
      intro y hy
      rw [Real.dist_eq]
      rw [show ρ.rOut = r from rfl] at hy
      have hd : dist x₀ y < r := Metric.mem_ball'.mp hy
      calc |φ_re y - φ_re x₀|
          = |(φ y - φ x₀).re| := by simp [φ_re, Complex.sub_re]
        _ ≤ ‖φ y - φ x₀‖ := abs_re_le_norm (φ y - φ x₀)
        _ = ‖φ x₀ - φ y‖ := norm_sub_rev _ _
        _ ≤ δ / 2 := hosc x₀ y (by rwa [dist_comm])
    have hosc_im : ∀ y ∈ Metric.ball x₀ ρ.rOut,
        dist (φ_im y) (φ_im x₀) ≤ δ / 2 := by
      intro y hy
      rw [Real.dist_eq]
      rw [show ρ.rOut = r from rfl] at hy
      have hd : dist x₀ y < r := Metric.mem_ball'.mp hy
      calc |φ_im y - φ_im x₀|
          = |(φ y - φ x₀).im| := by simp [φ_im, Complex.sub_im]
        _ ≤ ‖φ y - φ x₀‖ := abs_im_le_norm (φ y - φ x₀)
        _ = ‖φ x₀ - φ y‖ := norm_sub_rev _ _
        _ ≤ δ / 2 := hosc x₀ y (by rwa [dist_comm])
    -- Apply the Mathlib convolution bound to each component
    haveI : (volume : Measure R3).IsAddHaarMeasure := by
      infer_instance
    have hre : dist (ψ_re x₀) (φ_re x₀) ≤ δ / 2 :=
      ρ.dist_normed_convolution_le hmeas_re hosc_re
    have him : dist (ψ_im x₀) (φ_im x₀) ≤ δ / 2 :=
      ρ.dist_normed_convolution_le hmeas_im hosc_im
    -- Recombine: ‖ψ(x₀) - φ(x₀)‖ ≤ |re difference| + |im difference|
    have hdiff_re : (ψ x₀ - φ x₀).re = ψ_re x₀ - φ_re x₀ := by
      simp [ψ, φ_re, Complex.sub_re]
    have hdiff_im : (ψ x₀ - φ x₀).im = ψ_im x₀ - φ_im x₀ := by
      simp [ψ, φ_im, Complex.sub_im]
    calc ‖ψ x₀ - φ x₀‖
        ≤ |(ψ x₀ - φ x₀).re| + |(ψ x₀ - φ x₀).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |ψ_re x₀ - φ_re x₀| + |ψ_im x₀ - φ_im x₀| := by
          rw [hdiff_re, hdiff_im]
      _ ≤ δ / 2 + δ / 2 := by
          gcongr
          · exact RCLike.ofReal_le_ofReal.mp hre
          · exact RCLike.ofReal_le_ofReal.mp him
      _ = δ := add_halves δ

/-- The eLpNorm of a compactly supported bounded function is controlled by
    the sup-norm times a power of the support measure  -/
lemma eLpNorm_le_of_compactSupport_bound
    (f : R3 → ℂ) (hf_supp : HasCompactSupport f)
    (C : ℝ) (hfC : ∀ x, ‖f x‖ ≤ C) :
    eLpNorm f 2 (volume : Measure R3) ≤
      ENNReal.ofReal C *
        ((volume : Measure R3) (tsupport f)) ^ ((1 : ℝ) / 2) := by
  set K := tsupport f
  have hK : IsCompact K := hf_supp.isCompact
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have h_eq : f = K.indicator f := by
    ext x; by_cases hx : x ∈ K
    · exact (Set.indicator_of_mem hx f).symm
    · rw [Set.indicator_of_notMem hx f]
      exact image_eq_zero_of_notMem_tsupport hx
  conv_lhs => rw [h_eq, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  haveI : IsFiniteMeasure ((volume : Measure R3).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have h_ae_bound : ∀ᵐ x ∂(volume : Measure R3).restrict K, ‖f x‖ ≤ C :=
    ae_of_all _ hfC
  calc eLpNorm f 2 ((volume : Measure R3).restrict K)
      ≤ ((volume : Measure R3).restrict K Set.univ) ^ (ENNReal.toReal 2)⁻¹ *
          ENNReal.ofReal C := eLpNorm_le_of_ae_bound h_ae_bound
    _ = ENNReal.ofReal C *
          ((volume : Measure R3) K) ^ ((1 : ℝ) / 2) := by
        rw [mul_comm, Measure.restrict_apply_univ]
        congr 1
        simp [ENNReal.toReal_ofNat]

/-- Smooth compactly supported functions approximate continuous compactly
    supported functions in L² -/
lemma smooth_approx_continuous_compactSupport
    (φ : R3 → ℂ) (hcont : Continuous φ) (hsupp : HasCompactSupport φ)
    (hφ : MemLp φ 2 (volume : Measure R3))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ψ : R3 → ℂ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∃ hψ : MemLp ψ 2 (volume : Measure R3), ‖hφ.toLp φ - hψ.toLp ψ‖ < ε := by
  haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
    infer_instance
  set K₀ := tsupport φ + Metric.closedBall (0 : R3) 1
  have hK₀ : IsCompact K₀ := by
    exact hsupp.isCompact.add (isCompact_closedBall 0 1)
  have hK₀_meas_lt : (volume : Measure R3) K₀ < ⊤ := hK₀.measure_lt_top
  set M := ((volume : Measure R3) K₀).toReal
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  set δ := min 1 (ε / (Real.sqrt M + 2)) with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def, lt_min_iff]
    exact ⟨one_pos, div_pos hε (by linarith [Real.sqrt_nonneg M])⟩
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδM_lt_ε : δ * Real.sqrt M < ε := by
    have hdenom : 0 < Real.sqrt M + 2 := by linarith [Real.sqrt_nonneg M]
    calc δ * Real.sqrt M
        ≤ ε / (Real.sqrt M + 2) * Real.sqrt M := by
          gcongr; exact min_le_right _ _
      _ < ε := by
          have hsM := Real.sqrt_nonneg M
          simp [div_mul_eq_mul_div]
          rw [propext (div_lt_iff₀ hdenom)]
          nlinarith
  have h_approx := exists_smooth_uniform_approx φ hcont hsupp δ hδ_pos (1 : ℝ) (by norm_num)
  obtain ⟨ψ, hψ_smooth, hψ_supp, hψ_tsupport, hψ_close⟩ := h_approx
  have hψ_Lp : MemLp ψ 2 (volume : Measure R3) :=
    memLp_of_smooth_compactSupport ψ hψ_smooth hψ_supp
  refine ⟨ψ, hψ_smooth, hψ_supp, hψ_Lp, ?_⟩
  have hsupp_diff : HasCompactSupport (ψ - φ) := hψ_supp.sub hsupp
  have hsupp_sub_K₀ : tsupport (ψ - φ) ⊆ K₀ := by
    have h_support : Function.support (ψ - φ) ⊆ tsupport ψ ∪ tsupport φ := by
      intro x hx
      simp only [Function.mem_support, Pi.sub_apply, ne_eq, sub_ne_zero] at hx
      by_contra h
      simp only [Set.mem_union, not_or] at h
      have h1 : x ∉ Function.support ψ := mt (subset_tsupport ψ ·) h.1
      have h2 : x ∉ Function.support φ := mt (subset_tsupport φ ·) h.2
      simp only [Function.mem_support, not_not] at h1 h2
      exact hx (by rw [h1, h2])
    have h_closed : IsClosed (tsupport ψ ∪ tsupport φ) :=
        IsClosed.union (isClosed_tsupport ψ) (isClosed_tsupport φ)
    have h_tsupport : tsupport (ψ - φ) ⊆ tsupport ψ ∪ tsupport φ :=
      closure_minimal h_support h_closed
    exact h_tsupport.trans (Set.union_subset hψ_tsupport (fun x hx =>
      show x ∈ tsupport φ + Metric.closedBall (0 : R3) 1 by
        rw [show x = x + 0 from (add_zero x).symm]
        exact Set.add_mem_add hx (Metric.mem_closedBall_self one_pos.le)))
  have h_eLpNorm := eLpNorm_le_of_compactSupport_bound (ψ - φ) hsupp_diff
    δ (fun x => by rw [Pi.sub_apply]; exact hψ_close x)
  have h_meas_le : (volume : Measure R3) (tsupport (ψ - φ)) ≤ (volume : Measure R3) K₀ :=
    measure_mono hsupp_sub_K₀
  have h_chain : eLpNorm (ψ - φ) 2 volume ≤
      ENNReal.ofReal δ * ((volume : Measure R3) K₀) ^ ((1 : ℝ) / 2) :=
    h_eLpNorm.trans (by gcongr)
  rw [Lp.norm_def (hφ.toLp φ - hψ_Lp.toLp ψ),
      eLpNorm_congr_ae (Lp.coeFn_sub (hφ.toLp φ) (hψ_Lp.toLp ψ))]
  have hae : ((hφ.toLp φ : R3 → ℂ) - (hψ_Lp.toLp ψ : R3 → ℂ)) =ᵐ[volume] (φ - ψ) :=
    hφ.coeFn_toLp.sub hψ_Lp.coeFn_toLp
  rw [eLpNorm_congr_ae hae, show φ - ψ = -(ψ - φ) from by abel, eLpNorm_neg]
  have h_ne_top : eLpNorm (ψ - φ) 2 volume ≠ ⊤ :=
    (hψ_Lp.sub hφ).eLpNorm_ne_top
  calc (eLpNorm (ψ - φ) 2 volume).toReal
    _ ≤ (ENNReal.ofReal δ * ((volume : Measure R3) K₀) ^ ((1 : ℝ) / 2)).toReal := by
        apply ENNReal.toReal_mono _ h_chain
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK₀_meas_lt.ne)
    _ = δ * ((volume : Measure R3) K₀).toReal ^ ((1 : ℝ) / 2) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ_pos.le,
            ENNReal.toReal_rpow]
    _ = δ * Real.sqrt M := by
        congr 1
        exact (Real.sqrt_eq_rpow M).symm
    _ < ε := hδM_lt_ε

/-- **Density**: C_c^∞(ℝ³) is dense in L²(ℝ³).
    Chain: L² ←ε/2— C_c ←ε/2— C_c^∞. -/
lemma dense_test_functions_L2 :
    Dense {g : L2_R3 | ∃ (φ : R3 → ℂ),
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (g : R3 → ℂ) =ᵐ[volume] φ} := by
  rw [Metric.dense_iff]
  intro g ε hε
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  -- Step 1: approximate g by continuous compactly supported (within ε/2)
  obtain ⟨g₁, hg₁_dist, φ₁, hcont₁, hsupp₁, hae₁⟩ :=
    Metric.dense_iff.mp dense_continuous_compactSupport_L2 g (ε / 2) hε2
  -- Step 2: φ₁ ∈ L² (continuous + compact support on a locally finite measure)
  have hφ₁_Lp : MemLp φ₁ 2 (volume : Measure R3) := by
    haveI : IsFiniteMeasureOnCompacts (volume : Measure R3) := by
      infer_instance
    obtain ⟨C, hC⟩ := hcont₁.bounded_above_of_compact_support hsupp₁
    exact hsupp₁.memLp_of_bound hcont₁.aestronglyMeasurable C (ae_of_all _ hC)
  -- Step 3: g₁ = toLp φ₁ (both represent φ₁ a.e., hence equal as Lp elements)
  have hg₁_eq : g₁ = hφ₁_Lp.toLp φ₁ :=
    Subtype.ext (AEEqFun.ext (hae₁.trans hφ₁_Lp.coeFn_toLp.symm))
  -- Step 4: smooth approximation of φ₁ (within ε/2); ψ ∈ L² comes bundled with the bound.
  obtain ⟨ψ, hψ_smooth, hψ_supp, hψ_Lp, hψ_close⟩ :=
    smooth_approx_continuous_compactSupport φ₁ hcont₁ hsupp₁ hφ₁_Lp hε2
  -- Step 5: toLp ψ is in the target set and ε-close to g
  exact ⟨hψ_Lp.toLp ψ,
    calc dist (hψ_Lp.toLp ψ) g
        ≤ dist (hψ_Lp.toLp ψ) g₁ + dist g₁ g := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 :=
          add_lt_add
            (by rw [hg₁_eq, dist_comm, dist_eq_norm]; exact hψ_close)
            hg₁_dist
      _ = ε := add_halves ε,
    ⟨ψ, hψ_smooth, hψ_supp, hψ_Lp.coeFn_toLp⟩⟩

end Spectra.Sobolev

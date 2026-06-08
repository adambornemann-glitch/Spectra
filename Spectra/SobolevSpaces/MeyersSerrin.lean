/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/SoboleveSpaces/MeyersSerrin.lean
-/
import Spectra.SobolevSpaces.Mollification

open MeasureTheory
open scoped Pointwise ContDiff

namespace Spectra.Sobolev

/-- Smooth cutoff functions on R3.
    Discharge: ContDiffBump composed with the norm, or
    exists_contDiff_one_nhds_zero applied to closedBall. -/
private lemma exists_smooth_cutoff (R : ℝ) (hR : 0 < R) :
    ∃ (χ : R3 → ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x ∈ Metric.closedBall (0 : R3) R, χ x = 1) ∧
      (∀ x, χ x ∈ Set.Icc 0 1) ∧
      (tsupport χ ⊆ Metric.closedBall (0 : R3) (2 * R)) := by
  let ρ : ContDiffBump (0 : R3) := ⟨R, 2 * R, hR, by linarith⟩
  exact ⟨ρ, ρ.contDiff, ρ.hasCompactSupport,
    fun x hx => ρ.one_of_mem_closedBall hx,
    fun x => ⟨ρ.nonneg, ρ.le_one⟩,
    ρ.tsupport_eq.le⟩

/-- L² mass on the complement of large balls vanishes.
    Proof avoids dominated convergence by using density of C_c in L². -/
private lemma L2_tail_small (f : L2_R3) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (χ : R3 → ℝ),
      (∀ x ∈ Metric.closedBall (0 : R3) R, χ x = 1) →
      (∀ x, χ x ∈ Set.Icc 0 1) → Measurable χ →
      eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : R3 → ℂ) x) 2 volume
        < ENNReal.ofReal ε := by
  -- Approximate f by continuous compactly supported φ within ε
  obtain ⟨g₁, hg₁_dist, φ, hcont, hsupp, hae⟩ :=
    Metric.dense_iff.mp dense_continuous_compactSupport_L2 f ε hε
  -- φ has compact support ⊆ some ball
  obtain ⟨R₀, hball⟩ := hsupp.isCompact.isBounded.subset_closedBall (0 : R3)
  refine ⟨max R₀ 1, lt_max_of_lt_right one_pos, fun χ hχ_one hχ_bound _ => ?_⟩
  have hball' : tsupport φ ⊆ Metric.closedBall (0 : R3) (max R₀ 1) :=
    hball.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  -- Key: (1-χ)φ = 0 everywhere (χ=1 in ball, φ=0 outside support)
  have hzero : ∀ x, (1 - (χ x : ℂ)) * φ x = 0 := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : R3) (max R₀ 1)
    · rw [hχ_one x hx, Complex.ofReal_one, sub_self, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hball' h)), mul_zero]
  -- (1-χ)f =ᵐ (1-χ)(f - g₁) since (1-χ)g₁ =ᵐ (1-χ)φ = 0
  have hae_eq : (fun x => (1 - (χ x : ℂ)) * (f : R3 → ℂ) x) =ᵐ[volume]
      fun x => (1 - (χ x : ℂ)) * ((f : R3 → ℂ) x - (g₁ : R3 → ℂ) x) := by
    filter_upwards [hae] with x hx
    rw [mul_sub, show (1 - (χ x : ℂ)) * (g₁ : R3 → ℂ) x = 0 from by rw [hx]; exact hzero x,
        sub_zero]
  -- Pointwise: ‖(1-χ)(f-g₁)‖ ≤ ‖f-g₁‖ since ‖1-χ‖ ≤ 1
  have hbound : ∀ᵐ x ∂volume,
      ‖(fun x => (1 - (χ x : ℂ)) * ((f : R3 → ℂ) x - (g₁ : R3 → ℂ) x)) x‖ ≤
      ‖(f : R3 → ℂ) x - (g₁ : R3 → ℂ) x‖ :=
    ae_of_all _ fun x => by
      simp only; rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        rw [show (1 : ℂ) - (χ x : ℂ) = ((1 - χ x : ℝ) : ℂ) from by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg (by grind only [= Set.mem_Icc])]
        grind only [= Set.mem_Icc])
  -- Chain: eLpNorm((1-χ)f) = eLpNorm((1-χ)(f-g₁)) ≤ eLpNorm(f-g₁) < ε
  have h_ne_top : eLpNorm ((f - g₁ : L2_R3) : R3 → ℂ) 2 volume ≠ ⊤ :=
    (Lp.memLp (f - g₁)).eLpNorm_ne_top
  calc eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : R3 → ℂ) x) 2 volume
      = eLpNorm (fun x => (1 - (χ x : ℂ)) * ((f : R3 → ℂ) x - (g₁ : R3 → ℂ) x))
          2 volume := eLpNorm_congr_ae hae_eq
    _ ≤ eLpNorm (fun x => (f : R3 → ℂ) x - (g₁ : R3 → ℂ) x) 2 volume :=
        eLpNorm_mono_ae hbound
    _ = eLpNorm ((f - g₁ : L2_R3) : R3 → ℂ) 2 volume :=
        eLpNorm_congr_ae (Lp.coeFn_sub f g₁).symm
    _ < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_toReal h_ne_top]
        exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by
          rw [← Lp.norm_def, ← dist_eq_norm]
          exact Metric.mem_ball'.mp hg₁_dist)

/-- Weak derivative product rule with smooth multiplier.
    If g has weak derivative dg and χ is smooth, then χ·g has weak
    derivative χ·dg + g·∂ᵢχ. Discharge: expand the test function
    integral, use Leibniz rule on χ·φ. -/
private lemma hasWeakDerivative_smul_smooth
    (g : L2_R3) (i : Fin 3) (dg : L2_R3)
    (h_dg : HasWeakDerivative g i dg)
    (χ : R3 → ℝ) (hχ_smooth : ContDiff ℝ ∞ χ) (hχ_supp : HasCompactSupport χ)
    (_hχ_bound : ∀ x, χ x ∈ Set.Icc 0 1)
    (g_trunc dg_trunc : L2_R3)
    (hg_ae : (g_trunc : R3 → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) * (g : R3 → ℂ) x)
    (hdg_ae : (dg_trunc : R3 → ℂ) =ᵐ[volume] fun x =>
      (χ x : ℂ) * (dg : R3 → ℂ) x +
      (g : R3 → ℂ) x * fderiv ℝ (fun y => (χ y : ℂ)) x (EuclideanSpace.single i 1)) :
    HasWeakDerivative g_trunc i dg_trunc := by
  intro φ hφ hsupp_φ
  set eᵢ := EuclideanSpace.single i (1 : ℝ)
  set χC : R3 → ℂ := fun y => (χ y : ℂ) with hχC_def
  have hχC : ContDiff ℝ ∞ χC := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hχC_supp : HasCompactSupport χC := hχ_supp.comp_left Complex.ofReal_zero
  -- χ · φ is smooth compactly supported — a valid test function
  have hχφ_s : ContDiff ℝ ∞ (fun x => χC x * φ x) := hχC.mul hφ
  have hχφ_c : HasCompactSupport (fun x => χC x * φ x) := hχC_supp.mul_right
  -- Leibniz rule: ∂ᵢ(χ·φ) = (∂ᵢχ)·φ + χ·(∂ᵢφ)
  have leibniz : ∀ x, fderiv ℝ (fun y => χC y * φ y) x eᵢ =
      fderiv ℝ χC x eᵢ * φ x + χC x * fderiv ℝ φ x eᵢ := by
    intro x
    have h1 : DifferentiableAt ℝ χC x := (hχC.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
    have h2 : DifferentiableAt ℝ φ x := (hφ.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
    simp only [show (fun y => χC y * φ y) = χC * φ from funext fun _ => rfl]
    erw [fderiv_mul h1 h2, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]; ring_nf
  -- Apply the weak derivative of g to the test function χ · φ
  have h_test := h_dg (fun x => χC x * φ x) hχφ_s hχφ_c
  -- Integrability of all four integral terms (Hölder: L² × L² → L¹)
  have hint_lhs : Integrable (fun x => (g_trunc : R3 → ℂ) x *
      fderiv ℝ φ x eᵢ) volume :=
    (Lp.memLp g_trunc).integrable_mul (memLp_partialDeriv φ i hφ hsupp_φ)
  have hint_rhs : Integrable (fun x => (dg_trunc : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp dg_trunc).integrable_mul (memLp_of_smooth_compactSupport φ hφ hsupp_φ)
  have hint_l : Integrable (fun x => (g : R3 → ℂ) x *
      fderiv ℝ (fun y => χC y * φ y) x eᵢ) volume :=
    (Lp.memLp g).integrable_mul (memLp_of_smooth_compactSupport _
      (contDiff_partialDeriv _ i hχφ_s) (hasCompactSupport_partialDeriv _ i hχφ_c))
  have hint_r : Integrable (fun x => (dg : R3 → ℂ) x * (χC x * φ x)) volume :=
    (Lp.memLp dg).integrable_mul (memLp_of_smooth_compactSupport _ hχφ_s hχφ_c)
  -- Reduce goal (A = -B) to (A + B = 0)
  apply eq_neg_of_add_eq_zero_left
  -- Strategy: merge into one integral, ae-rewrite integrands via
  -- hg_ae + hdg_ae + Leibniz (ring closes the pointwise identity),
  -- then split back and close with h_test.
  trans ∫ x, ((g : R3 → ℂ) x * fderiv ℝ (fun y => χC y * φ y) x eᵢ +
              (dg : R3 → ℂ) x * (χC x * φ x))
  · -- ∫(g_trunc·∂ᵢφ + dg_trunc·φ) =ᵃᵉ ∫(g·∂ᵢ(χφ) + dg·(χφ))
    rw [← integral_add hint_lhs hint_rhs]
    exact integral_congr_ae (by
      filter_upwards [hg_ae, hdg_ae] with x hx1 hx2
      rw [hx1, hx2, leibniz]; ring)
  · -- ∫ g·∂ᵢ(χφ) + ∫ dg·(χφ) = 0  by h_test
    rw [integral_add hint_l hint_r]
    linear_combination h_test

/-- A scaled smooth cutoff with explicit derivative bound `M/R`,
where `M ≥ 0` is a constant independent of `R`. Used in the truncation step
of Meyers-Serrin to control the Leibniz cross-term `g · ∂ᵢχ` uniformly as
`R → ∞`. The bound is achieved by taking `χ_R(x) := ρ(R⁻¹ • x)` for a fixed
unit-scale bump `ρ`; the chain rule then gives `‖fderiv χ_R‖ ≤ ‖fderiv ρ‖_∞ / R`. -/
private lemma exists_smooth_cutoff_scaled :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ), 0 < R →
      ∃ (χ : R3 → ℝ),
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ x ∈ Metric.closedBall (0 : R3) R, χ x = 1) ∧
        (∀ x, χ x ∈ Set.Icc 0 1) ∧
        tsupport χ ⊆ Metric.closedBall (0 : R3) (2 * R) ∧
        ∀ x, ‖fderiv ℝ χ x‖ ≤ M / R := by
  -- Fixed unit-scale bump: rIn = 1, rOut = 2 at the origin.
  let ρ : ContDiffBump (0 : R3) := ⟨1, 2, one_pos, by norm_num⟩
  have hρ_smooth : ContDiff ℝ ∞ (ρ : R3 → ℝ) := ρ.contDiff
  have hρ_supp : HasCompactSupport (ρ : R3 → ℝ) := ρ.hasCompactSupport
  have hρ_tsupp_eq : tsupport (ρ : R3 → ℝ) = Metric.closedBall (0 : R3) 2 :=
    ρ.tsupport_eq
  -- Unit bump's derivative is c.s. and continuous, hence bounded.
  have hρ_d_smooth : ContDiff ℝ ∞ (fderiv ℝ (ρ : R3 → ℝ)) :=
    (contDiff_infty_iff_fderiv.mp hρ_smooth).2
  have hρ_d_cont : Continuous (fderiv ℝ (ρ : R3 → ℝ)) := hρ_d_smooth.continuous
  have hρ_d_supp : HasCompactSupport (fderiv ℝ (ρ : R3 → ℝ)) := hρ_supp.fderiv ℝ
  obtain ⟨M₀, hM₀⟩ := hρ_d_cont.bounded_above_of_compact_support hρ_d_supp
  -- max M₀ 0 ensures nonnegativity unconditionally.
  refine ⟨max M₀ 0, le_max_right _ _, fun R hR => ?_⟩
  refine ⟨fun x => (ρ : R3 → ℝ) (R⁻¹ • x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. Smooth (composition with scaling CLM).
  · have h_scale_smooth : ContDiff ℝ ∞ (fun y : R3 => R⁻¹ • y) :=
      (R⁻¹ • ContinuousLinearMap.id ℝ R3).contDiff
    exact hρ_smooth.comp h_scale_smooth
  -- 2. Compact support.
  · refine HasCompactSupport.intro
      (K := (fun y : R3 => R • y) '' Metric.closedBall (0 : R3) 2)
      ((isCompact_closedBall _ _).image (continuous_id.const_smul R)) ?_
    intro x hx
    show (ρ : R3 → ℝ) (R⁻¹ • x) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    rw [hρ_tsupp_eq] at hmem
    exact hx ⟨R⁻¹ • x, hmem, by simp [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]⟩
  -- 3. χ ≡ 1 on closedBall 0 R.
  · intro x hx
    show (ρ : R3 → ℝ) (R⁻¹ • x) = 1
    apply ρ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    calc R⁻¹ * ‖x‖
        ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
      _ = 1       := inv_mul_cancel₀ hR.ne'
  -- 4. χ ∈ [0, 1].
  · intro x; exact ⟨ρ.nonneg, ρ.le_one⟩
  -- 5. tsupport χ ⊆ closedBall 0 (2R).
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro y hy
    rw [Function.mem_support] at hy
    have h_in : R⁻¹ • y ∈ tsupport (ρ : R3 → ℝ) := subset_tsupport _ hy
    rw [hρ_tsupp_eq, Metric.mem_closedBall, dist_zero_right, norm_smul] at h_in
    simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hR] at h_in
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖y‖
        = R * (R⁻¹ * ‖y‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
      _ ≤ R * 2 := mul_le_mul_of_nonneg_left h_in hR.le
      _ = 2 * R := by ring
  -- 6. Derivative bound: ‖fderiv χ x‖ ≤ (max M₀ 0) / R.
  · intro x
    -- Chain rule via HasFDerivAt of the scaling CLM.
    have h_scale_hfd : HasFDerivAt (fun y : R3 => R⁻¹ • y)
        (R⁻¹ • ContinuousLinearMap.id ℝ R3) x :=
      (R⁻¹ • ContinuousLinearMap.id ℝ R3).hasFDerivAt
    have hρ_diff_at : DifferentiableAt ℝ (ρ : R3 → ℝ) (R⁻¹ • x) :=
      (hρ_smooth.differentiable
        (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
    have h_χ_hfd : HasFDerivAt (fun y : R3 => (ρ : R3 → ℝ) (R⁻¹ • y))
        ((fderiv ℝ (ρ : R3 → ℝ) (R⁻¹ • x)).comp
          (R⁻¹ • ContinuousLinearMap.id ℝ R3)) x :=
      hρ_diff_at.hasFDerivAt.comp x h_scale_hfd
    rw [h_χ_hfd.fderiv]
    have h_op_bound : ‖(fderiv ℝ (ρ : R3 → ℝ) (R⁻¹ • x)).comp
        (R⁻¹ • ContinuousLinearMap.id ℝ R3)‖ ≤
        ‖fderiv ℝ (ρ : R3 → ℝ) (R⁻¹ • x)‖ *
          ‖R⁻¹ • ContinuousLinearMap.id ℝ R3‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h_σ_norm : ‖R⁻¹ • ContinuousLinearMap.id ℝ R3‖ = R⁻¹ := by
      rw [norm_smul, ContinuousLinearMap.norm_id]
      simp [Real.norm_eq_abs]
      exact le_of_lt hR
    calc ‖(fderiv ℝ (ρ : R3 → ℝ) (R⁻¹ • x)).comp
            (R⁻¹ • ContinuousLinearMap.id ℝ R3)‖
        ≤ ‖fderiv ℝ (ρ : R3 → ℝ) (R⁻¹ • x)‖ *
            ‖R⁻¹ • ContinuousLinearMap.id ℝ R3‖ := h_op_bound
      _ = ‖fderiv ℝ (ρ : R3 → ℝ) (R⁻¹ • x)‖ * R⁻¹ := by rw [h_σ_norm]
      _ ≤ M₀ * R⁻¹ :=
          mul_le_mul_of_nonneg_right (hM₀ _) (inv_nonneg.mpr hR.le)
      _ ≤ max M₀ 0 * R⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hR.le)
      _ = max M₀ 0 / R := by rw [← div_eq_mul_inv]

/-- Truncation step of Meyers-Serrin: multiply by a smooth cutoff to get
    compactly supported approximations preserving weak derivative structure. -/
private lemma truncation_approx (i : Fin 3) (g dg : L2_R3)
    (h_dg : HasWeakDerivative g i dg) (ε : ℝ) (hε : 0 < ε) :
    ∃ (h_R : R3 → ℂ) (dh_R : R3 → ℂ)
      (hh : MemLp h_R 2 volume) (hdh : MemLp dh_R 2 volume),
      HasCompactSupport h_R ∧ HasCompactSupport dh_R ∧
      HasWeakDerivative (hh.toLp h_R) i (hdh.toLp dh_R) ∧
      ‖g - hh.toLp h_R‖ < ε ∧ ‖dg - hdh.toLp dh_R‖ < ε := by
  have hε4 : 0 < ε / 4 := by linarith
  -- Universal derivative bound M from the cutoff helper.
  obtain ⟨M, hM_nn, h_cutoff⟩ := exists_smooth_cutoff_scaled
  -- L²-tail bounds for g and dg.
  obtain ⟨R₁, _hR₁_pos, hR₁_tail_g⟩ := L2_tail_small g (ε / 4) hε4
  obtain ⟨R₂, _hR₂_pos, hR₂_tail_dg⟩ := L2_tail_small dg (ε / 4) hε4
  -- Pick R covering both tails AND making (M/R)·‖g‖ < ε/4.
  set R := max (max R₁ R₂) (4 * M * ‖g‖ / ε + 1) with hR_def
  have hMg_nn : 0 ≤ 4 * M * ‖g‖ / ε :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM_nn) (norm_nonneg _)) hε.le
  have hR_pos : 0 < R := lt_max_of_lt_right (by linarith)
  have hR_ge_R₁ : R₁ ≤ R := le_max_of_le_left (le_max_left _ _)
  have hR_ge_R₂ : R₂ ≤ R := le_max_of_le_left (le_max_right _ _)
  have hR_cross : (M / R) * ‖g‖ < ε / 4 := by
    have h_le : 4 * M * ‖g‖ / ε + 1 ≤ R := le_max_right _ _
    have h_lt : 4 * M * ‖g‖ / ε < R := by linarith
    have h_ε : 4 * M * ‖g‖ < R * ε := by
      have := (div_lt_iff₀ hε).mp h_lt; linarith
    rw [show (M / R) * ‖g‖ = M * ‖g‖ / R from by ring, div_lt_iff₀ hR_pos]
    linarith
  -- The cutoff (real-valued).
  obtain ⟨χ, hχ_smooth, hχ_supp, hχ_one, hχ_bound, _hχ_tsupp, hχ_deriv⟩ :=
    h_cutoff R hR_pos
  -- Complex-valued cutoff and its sup bound.
  let χℂ : R3 → ℂ := fun x => (χ x : ℂ)
  have hχℂ_smooth : ContDiff ℝ ∞ χℂ := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hχℂ_supp : HasCompactSupport χℂ := hχ_supp.comp_left Complex.ofReal_zero
  have hχℂ_le_one : ∀ x, ‖χℂ x‖ ≤ 1 := by
    intro x
    show ‖((χ x : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h := hχ_bound x
    rw [Set.mem_Icc] at h
    exact abs_le.mpr ⟨by linarith, h.2⟩
  -- ∂ᵢχℂ: smooth, c.s., with derivative bound M/R.
  let dχℂ : R3 → ℂ := fun x => fderiv ℝ χℂ x (EuclideanSpace.single i 1)
  have hdχℂ_smooth : ContDiff ℝ ∞ dχℂ := contDiff_partialDeriv χℂ i hχℂ_smooth
  have hdχℂ_supp : HasCompactSupport dχℂ :=
    hasCompactSupport_partialDeriv χℂ i hχℂ_supp
  have hdχℂ_bound : ∀ x, ‖dχℂ x‖ ≤ M / R := by
    intro x
    show ‖fderiv ℝ χℂ x (EuclideanSpace.single i 1)‖ ≤ M / R
    have hχ_diff_at : DifferentiableAt ℝ χ x :=
      (hχ_smooth.differentiable
        (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
    rw [show (χℂ : R3 → ℂ) = Complex.ofRealCLM ∘ χ from rfl,
        fderiv_comp x Complex.ofRealCLM.differentiableAt hχ_diff_at]
    erw [ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    change ‖((fderiv ℝ χ x (EuclideanSpace.single i 1) : ℝ) : ℂ)‖ ≤ M / R
    rw [Complex.norm_real]
    calc ‖fderiv ℝ χ x (EuclideanSpace.single i 1)‖
        ≤ ‖fderiv ℝ χ x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M / R) * 1 := by
          gcongr
          · exact hχ_deriv x
          · simp [PiLp.norm_single]
      _ = M / R := mul_one _
  -- The truncated bare functions.
  let h_R : R3 → ℂ := fun x => χℂ x * (g : R3 → ℂ) x
  let dh_R : R3 → ℂ := fun x => χℂ x * (dg : R3 → ℂ) x + (g : R3 → ℂ) x * dχℂ x
  have h_g_meas : AEStronglyMeasurable (g : R3 → ℂ) volume :=
    (Lp.memLp g).aestronglyMeasurable
  have h_dg_meas : AEStronglyMeasurable (dg : R3 → ℂ) volume :=
    (Lp.memLp dg).aestronglyMeasurable
  -- MemLp h_R via |h_R| ≤ |g|.
  have hh_R_MemLp : MemLp h_R 2 volume := by
    refine ⟨hχℂ_smooth.continuous.aestronglyMeasurable.mul h_g_meas, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_mono_ae ?_) (Lp.memLp g).eLpNorm_lt_top
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχℂ_le_one x)
  -- MemLp for the χ·dg piece.
  have h_χdg_MemLp : MemLp (fun x => χℂ x * (dg : R3 → ℂ) x) 2 volume := by
    refine ⟨hχℂ_smooth.continuous.aestronglyMeasurable.mul h_dg_meas, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_mono_ae ?_) (Lp.memLp dg).eLpNorm_lt_top
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχℂ_le_one x)
  have hMR_nn : 0 ≤ M / R := div_nonneg hM_nn hR_pos.le
  -- Pointwise: ‖g·dχℂ‖ ≤ ‖(M/R)•g‖.
  have h_gdχ_ptw : ∀ x, ‖(g : R3 → ℂ) x * dχℂ x‖ ≤
      ‖(M / R : ℝ) • (g : R3 → ℂ) x‖ := by
    intro x
    rw [Complex.real_smul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hMR_nn,
        mul_comm ‖(g : R3 → ℂ) x‖ ‖dχℂ x‖]
    exact mul_le_mul_of_nonneg_right (hdχℂ_bound x) (norm_nonneg _)
  -- MemLp for the g·dχℂ piece.
  have h_gdχ_MemLp : MemLp (fun x => (g : R3 → ℂ) x * dχℂ x) 2 volume := by
    refine ⟨h_g_meas.mul hdχℂ_smooth.continuous.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt
      (eLpNorm_mono_ae (Filter.Eventually.of_forall h_gdχ_ptw)) ?_
    rw [show (fun x => (M / R : ℝ) • (g : R3 → ℂ) x)
          = (M / R : ℝ) • ((g : R3 → ℂ)) from rfl]
    erw [eLpNorm_const_smul]
    exact ENNReal.mul_lt_top enorm_lt_top (Lp.memLp g).eLpNorm_lt_top
  have hdh_R_MemLp : MemLp dh_R 2 volume := h_χdg_MemLp.add h_gdχ_MemLp
  -- Compact supports.
  have hh_R_supp : HasCompactSupport h_R := hχℂ_supp.mul_right
  have hdh_R_supp : HasCompactSupport dh_R :=
    HasCompactSupport.add hχℂ_supp.mul_right hdχℂ_supp.mul_left
  -- Weak derivative via the existing smooth-product-rule lemma.
  have h_wkd : HasWeakDerivative (hh_R_MemLp.toLp h_R) i
      (hdh_R_MemLp.toLp dh_R) :=
    hasWeakDerivative_smul_smooth g i dg h_dg χ hχ_smooth hχ_supp hχ_bound
      (hh_R_MemLp.toLp h_R) (hdh_R_MemLp.toLp dh_R)
      hh_R_MemLp.coeFn_toLp hdh_R_MemLp.coeFn_toLp
  refine ⟨h_R, dh_R, hh_R_MemLp, hdh_R_MemLp,
    hh_R_supp, hdh_R_supp, h_wkd, ?_, ?_⟩
  -- Norm bound 1: ‖g - h_R_Lp‖ < ε.
  · rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
    have hae : ((g : R3 → ℂ) - (hh_R_MemLp.toLp h_R : R3 → ℂ)) =ᵐ[volume]
        fun x => (1 - (χ x : ℂ)) * (g : R3 → ℂ) x := by
      filter_upwards [hh_R_MemLp.coeFn_toLp] with x hx
      show (g : R3 → ℂ) x - (hh_R_MemLp.toLp h_R : R3 → ℂ) x = _
      rw [hx]
      show (g : R3 → ℂ) x - χℂ x * (g : R3 → ℂ) x =
        (1 - (χ x : ℂ)) * (g : R3 → ℂ) x
      ring
    rw [eLpNorm_congr_ae hae]
    have h_bound :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (g : R3 → ℂ) x) 2 volume
          < ENNReal.ofReal (ε / 4) :=
      hR₁_tail_g χ
        (fun x hx => hχ_one x (Metric.closedBall_subset_closedBall hR_ge_R₁ hx))
        hχ_bound hχ_smooth.continuous.measurable
    have h_ne :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (g : R3 → ℂ) x) 2 volume ≠ ⊤ :=
      ne_top_of_lt h_bound
    calc (eLpNorm (fun x => (1 - (χ x : ℂ)) * (g : R3 → ℂ) x) 2 volume).toReal
        < (ENNReal.ofReal (ε / 4)).toReal :=
          (ENNReal.toReal_lt_toReal h_ne ENNReal.ofReal_ne_top).mpr h_bound
      _ = ε / 4 := ENNReal.toReal_ofReal hε4.le
      _ < ε := by linarith
  -- Norm bound 2: ‖dg - dh_R_Lp‖ < ε.
  · rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
    have hae : ((dg : R3 → ℂ) - (hdh_R_MemLp.toLp dh_R : R3 → ℂ)) =ᵐ[volume]
        fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x -
          (g : R3 → ℂ) x * dχℂ x := by
      filter_upwards [hdh_R_MemLp.coeFn_toLp] with x hx
      show (dg : R3 → ℂ) x - (hdh_R_MemLp.toLp dh_R : R3 → ℂ) x = _
      rw [hx]
      show (dg : R3 → ℂ) x -
            (χℂ x * (dg : R3 → ℂ) x + (g : R3 → ℂ) x * dχℂ x) =
        (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x - (g : R3 → ℂ) x * dχℂ x
      ring
    rw [eLpNorm_congr_ae hae]
    have h_meas1 : AEStronglyMeasurable
        (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x) volume :=
      (continuous_const.sub hχℂ_smooth.continuous).aestronglyMeasurable.mul h_dg_meas
    have h_meas2 : AEStronglyMeasurable
        (fun x => (g : R3 → ℂ) x * dχℂ x) volume :=
      h_g_meas.mul hdχℂ_smooth.continuous.aestronglyMeasurable
    have hp_one_le_two : (1 : ENNReal) ≤ 2 := by norm_num
    have h_triangle : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x -
          (g : R3 → ℂ) x * dχℂ x) 2 volume ≤
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x) 2 volume +
        eLpNorm (fun x => (g : R3 → ℂ) x * dχℂ x) 2 volume :=
      eLpNorm_sub_le h_meas1 h_meas2 hp_one_le_two
    have h_bound1 :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x) 2 volume
          < ENNReal.ofReal (ε / 4) :=
      hR₂_tail_dg χ
        (fun x hx => hχ_one x (Metric.closedBall_subset_closedBall hR_ge_R₂ hx))
        hχ_bound hχ_smooth.continuous.measurable
    have h_eLpNorm_g_eq :
        eLpNorm (g : R3 → ℂ) 2 volume = ENNReal.ofReal ‖g‖ := by
      rw [Lp.norm_def]
      exact (ENNReal.ofReal_toReal (Lp.memLp g).eLpNorm_ne_top).symm
    have h_bound2 :
        eLpNorm (fun x => (g : R3 → ℂ) x * dχℂ x) 2 volume
          ≤ ENNReal.ofReal (ε / 4) := by
      have h_le :
          eLpNorm (fun x => (g : R3 → ℂ) x * dχℂ x) 2 volume ≤
          ENNReal.ofReal ((M / R) * ‖g‖) := by
        calc eLpNorm (fun x => (g : R3 → ℂ) x * dχℂ x) 2 volume
            ≤ eLpNorm (fun x => (M / R : ℝ) • (g : R3 → ℂ) x) 2 volume :=
              eLpNorm_mono_ae (Filter.Eventually.of_forall h_gdχ_ptw)
          _ = ‖(M / R : ℝ)‖ₑ * eLpNorm (g : R3 → ℂ) 2 volume := by
              rw [show (fun x => (M / R : ℝ) • (g : R3 → ℂ) x)
                    = (M / R : ℝ) • ((g : R3 → ℂ)) from rfl]
              erw [eLpNorm_const_smul]
          _ = ENNReal.ofReal (M / R) * ENNReal.ofReal ‖g‖ := by
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hMR_nn,
                  h_eLpNorm_g_eq]
          _ = ENNReal.ofReal ((M / R) * ‖g‖) :=
              (ENNReal.ofReal_mul hMR_nn).symm
      exact le_of_lt
        (lt_of_le_of_lt h_le ((ENNReal.ofReal_lt_ofReal_iff hε4).mpr hR_cross))
    have h_sum_bound : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x -
          (g : R3 → ℂ) x * dχℂ x) 2 volume
          ≤ ENNReal.ofReal (ε / 2) := by
      calc eLpNorm
            (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x -
              (g : R3 → ℂ) x * dχℂ x) 2 volume
          ≤ eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x) 2 volume +
            eLpNorm (fun x => (g : R3 → ℂ) x * dχℂ x) 2 volume := h_triangle
        _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
              add_le_add h_bound1.le h_bound2
        _ = ENNReal.ofReal (ε / 2) := by
              rw [← ENNReal.ofReal_add hε4.le hε4.le]; congr 1; ring
    have h_ne : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x -
          (g : R3 → ℂ) x * dχℂ x) 2 volume ≠ ⊤ :=
      (lt_of_le_of_lt h_sum_bound ENNReal.ofReal_lt_top).ne
    calc (eLpNorm
            (fun x => (1 - (χ x : ℂ)) * (dg : R3 → ℂ) x -
              (g : R3 → ℂ) x * dχℂ x) 2 volume).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          (ENNReal.toReal_le_toReal h_ne ENNReal.ofReal_ne_top).mpr h_sum_bound
      _ = ε / 2 := ENNReal.toReal_ofReal (by linarith)
      _ < ε := by linarith

/-- **Meyers-Serrin approximation**: g with weak derivative dg can be
    simultaneously approximated by smooth c.s. functions in both norms. -/
lemma meyers_serrin_approx (i : Fin 3) (g dg : L2_R3)
    (h_dg : HasWeakDerivative g i dg) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ),
      ‖g - (memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ‖ < ε ∧
      ‖dg - (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  -- Step 1: Truncate g to get compactly supported approximation
  obtain ⟨h_R, dh_R, hh, hdh, hh_supp, hdh_supp, h_wk, hg_close, hdg_close⟩ :=
    truncation_approx i g dg h_dg (ε / 2) hε2
  -- Step 2: Mollify the truncation to get smooth c.s. approximation
  obtain ⟨φ, hφ, hφ_supp, hφ_close, hdφ_close⟩ :=
    mollify_compactly_supported i h_R dh_R hh hdh hh_supp hdh_supp h_wk (ε / 2) hε2
  -- Step 3: Triangle inequality assembles the two ε/2 bounds
  refine ⟨φ, hφ, hφ_supp, ?_, ?_⟩
  · -- ‖g - φ‖ ≤ ‖g - h_R‖ + ‖h_R - φ‖ < ε/2 + ε/2 = ε
    calc ‖g - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖
        ≤ ‖g - hh.toLp h_R‖ +
          ‖hh.toLp h_R - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖ := by
          have : g - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ =
            (g - hh.toLp h_R) +
            (hh.toLp h_R - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ) := by abel
          rw [this]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hg_close hφ_close
      _ = ε := add_halves ε
  · -- ‖dg - ∂ᵢφ‖ ≤ ‖dg - dh_R‖ + ‖dh_R - ∂ᵢφ‖ < ε/2 + ε/2 = ε
    calc ‖dg - (memLp_partialDeriv φ i hφ hφ_supp).toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖
        ≤ ‖dg - hdh.toLp dh_R‖ +
          ‖hdh.toLp dh_R - (memLp_partialDeriv φ i hφ hφ_supp).toLp
            (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ := by
          have : dg - (memLp_partialDeriv φ i hφ hφ_supp).toLp
              (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) =
            (dg - hdh.toLp dh_R) +
            (hdh.toLp dh_R - (memLp_partialDeriv φ i hφ hφ_supp).toLp
              (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) := by abel
          rw [this]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdg_close hdφ_close
      _ = ε := add_halves ε

end Spectra.Sobolev

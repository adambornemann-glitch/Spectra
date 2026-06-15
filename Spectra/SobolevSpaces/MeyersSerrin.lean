/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/SoboleveSpaces/MeyersSerrin.lean
-/
import Spectra.SobolevSpaces.Mollification
import Spectra.SobolevSpaces.MeyersCommon

open MeasureTheory
open scoped Pointwise ContDiff

namespace Spectra.Sobolev

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

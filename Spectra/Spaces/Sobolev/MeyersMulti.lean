/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/Spaces/Sobolev/MeyersMulti.lean
-/
import Spectra.Spaces.Sobolev.Mollification
import Spectra.Spaces.Sobolev.MeyersCommon

open MeasureTheory
open scoped Pointwise ContDiff

namespace Spectra.Sobolev

/-- **Multi-direction truncation step of Meyers-Serrin**: simultaneously truncate
    `f` and all three weak derivatives using a single cutoff `χ`.
    Parallels `truncation_approx`; the function-side h_R is shared across all
    directions, only the derivative-side dh_R i depends on i. -/
private lemma truncation_approx_multi
    (f : L2_R3) (dg : Fin 3 → L2_R3)
    (h_dg : ∀ i, HasWeakDerivative f i (dg i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (h_R : R3 → ℂ) (dh_R : Fin 3 → R3 → ℂ)
      (hh : MemLp h_R 2 volume) (hdh : ∀ i, MemLp (dh_R i) 2 volume),
      HasCompactSupport h_R ∧ (∀ i, HasCompactSupport (dh_R i)) ∧
      (∀ i, HasWeakDerivative (hh.toLp h_R) i ((hdh i).toLp (dh_R i))) ∧
      ‖f - hh.toLp h_R‖ < ε ∧ ∀ i, ‖dg i - (hdh i).toLp (dh_R i)‖ < ε := by
  have hε4 : 0 < ε / 4 := by linarith
  -- Universal derivative bound M for the cutoff.
  obtain ⟨M, hM_nn, h_cutoff⟩ := exists_smooth_cutoff_scaled
  -- L²-tail bounds: one for f, three for the dg i's.
  obtain ⟨R₀, _hR₀_pos, hR₀_tail_f⟩ := L2_tail_small f (ε / 4) hε4
  choose R_dg hR_dg_pos hR_dg_tail using
    fun i => L2_tail_small (dg i) (ε / 4) hε4
  -- R covers all four tails AND makes (M/R)·‖f‖ < ε/4.
  set R := max (max R₀ (max (R_dg 0) (max (R_dg 1) (R_dg 2))))
                (4 * M * ‖f‖ / ε + 1) with hR_def
  have hMf_nn : 0 ≤ 4 * M * ‖f‖ / ε :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM_nn) (norm_nonneg _)) hε.le
  have hR_pos : 0 < R := lt_max_of_lt_right (by linarith)
  have hR_ge_R₀ : R₀ ≤ R := le_max_of_le_left (le_max_left _ _)
  have hR_ge_R_dg : ∀ i, R_dg i ≤ R := by
    intro i
    fin_cases i
    · exact le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
    · exact le_max_of_le_left
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    · exact le_max_of_le_left
        (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  have hR_cross : (M / R) * ‖f‖ < ε / 4 := by
    have h_le : 4 * M * ‖f‖ / ε + 1 ≤ R := le_max_right _ _
    have h_lt : 4 * M * ‖f‖ / ε < R := by linarith
    have h_ε : 4 * M * ‖f‖ < R * ε := by
      have := (div_lt_iff₀ hε).mp h_lt; linarith
    rw [show (M / R) * ‖f‖ = M * ‖f‖ / R from by ring, div_lt_iff₀ hR_pos]
    linarith
  -- The cutoff (real-valued, single χ for all directions).
  obtain ⟨χ, hχ_smooth, hχ_supp, hχ_one, hχ_bound, _hχ_tsupp, hχ_deriv⟩ :=
    h_cutoff R hR_pos
  -- Complex-valued cutoff and sup bound.
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
  -- Per-direction partial of χℂ: smooth, c.s., uniformly bounded by M/R.
  let dχℂ : Fin 3 → R3 → ℂ :=
    fun i x => fderiv ℝ χℂ x (EuclideanSpace.single i 1)
  have hdχℂ_smooth : ∀ i, ContDiff ℝ ∞ (dχℂ i) :=
    fun i => contDiff_partialDeriv χℂ i hχℂ_smooth
  have hdχℂ_supp : ∀ i, HasCompactSupport (dχℂ i) :=
    fun i => hasCompactSupport_partialDeriv χℂ i hχℂ_supp
  have hdχℂ_bound : ∀ i x, ‖dχℂ i x‖ ≤ M / R := by
    intro i x
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
  -- Truncated bare functions: h_R universal, dh_R i per direction.
  let h_R : R3 → ℂ := fun x => χℂ x * (f : R3 → ℂ) x
  let dh_R : Fin 3 → R3 → ℂ :=
    fun i x => χℂ x * (dg i : R3 → ℂ) x + (f : R3 → ℂ) x * dχℂ i x
  have h_f_meas : AEStronglyMeasurable (f : R3 → ℂ) volume :=
    (Lp.memLp f).aestronglyMeasurable
  have h_dg_meas : ∀ i, AEStronglyMeasurable (dg i : R3 → ℂ) volume :=
    fun i => (Lp.memLp (dg i)).aestronglyMeasurable
  -- MemLp h_R via |h_R| ≤ |f|.
  have hh_R_MemLp : MemLp h_R 2 volume := by
    refine ⟨hχℂ_smooth.continuous.aestronglyMeasurable.mul h_f_meas, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_mono_ae ?_) (Lp.memLp f).eLpNorm_lt_top
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχℂ_le_one x)
  -- Per-i MemLp for χ·(dg i).
  have h_χdg_MemLp : ∀ i, MemLp (fun x => χℂ x * (dg i : R3 → ℂ) x) 2 volume := by
    intro i
    refine ⟨hχℂ_smooth.continuous.aestronglyMeasurable.mul (h_dg_meas i), ?_⟩
    refine lt_of_le_of_lt (eLpNorm_mono_ae ?_) (Lp.memLp (dg i)).eLpNorm_lt_top
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχℂ_le_one x)
  have hMR_nn : 0 ≤ M / R := div_nonneg hM_nn hR_pos.le
  -- Pointwise: ‖f · dχℂ i‖ ≤ ‖(M/R) • f‖, uniformly in i.
  have h_fdχ_ptw : ∀ i x, ‖(f : R3 → ℂ) x * dχℂ i x‖ ≤
      ‖(M / R : ℝ) • (f : R3 → ℂ) x‖ := by
    intro i x
    rw [Complex.real_smul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hMR_nn,
        mul_comm ‖(f : R3 → ℂ) x‖ ‖dχℂ i x‖]
    exact mul_le_mul_of_nonneg_right (hdχℂ_bound i x) (norm_nonneg _)
  -- Per-i MemLp for f · dχℂ i.
  have h_fdχ_MemLp : ∀ i, MemLp (fun x => (f : R3 → ℂ) x * dχℂ i x) 2 volume := by
    intro i
    refine ⟨h_f_meas.mul (hdχℂ_smooth i).continuous.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt
      (eLpNorm_mono_ae (Filter.Eventually.of_forall (h_fdχ_ptw i))) ?_
    rw [show (fun x => (M / R : ℝ) • (f : R3 → ℂ) x)
          = (M / R : ℝ) • ((f : R3 → ℂ)) from rfl]
    erw [eLpNorm_const_smul]
    exact ENNReal.mul_lt_top enorm_lt_top (Lp.memLp f).eLpNorm_lt_top
  have hdh_R_MemLp : ∀ i, MemLp (dh_R i) 2 volume :=
    fun i => (h_χdg_MemLp i).add (h_fdχ_MemLp i)
  -- Compact supports.
  have hh_R_supp : HasCompactSupport h_R := hχℂ_supp.mul_right
  have hdh_R_supp : ∀ i, HasCompactSupport (dh_R i) :=
    fun i => HasCompactSupport.add hχℂ_supp.mul_right (hdχℂ_supp i).mul_left
  -- Per-i weak derivative via hasWeakDerivative_smul_smooth.
  have h_wkd : ∀ i, HasWeakDerivative (hh_R_MemLp.toLp h_R) i
      ((hdh_R_MemLp i).toLp (dh_R i)) := fun i =>
    hasWeakDerivative_smul_smooth f i (dg i) (h_dg i)
      χ hχ_smooth hχ_supp hχ_bound
      (hh_R_MemLp.toLp h_R) ((hdh_R_MemLp i).toLp (dh_R i))
      hh_R_MemLp.coeFn_toLp (hdh_R_MemLp i).coeFn_toLp
  refine ⟨h_R, dh_R, hh_R_MemLp, hdh_R_MemLp,
    hh_R_supp, hdh_R_supp, h_wkd, ?_, ?_⟩
  -- Norm bound 1: ‖f - h_R_Lp‖ < ε.
  · rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
    have hae : ((f : R3 → ℂ) - (hh_R_MemLp.toLp h_R : R3 → ℂ)) =ᵐ[volume]
        fun x => (1 - (χ x : ℂ)) * (f : R3 → ℂ) x := by
      filter_upwards [hh_R_MemLp.coeFn_toLp] with x hx
      show (f : R3 → ℂ) x - (hh_R_MemLp.toLp h_R : R3 → ℂ) x = _
      rw [hx]
      show (f : R3 → ℂ) x - χℂ x * (f : R3 → ℂ) x =
        (1 - (χ x : ℂ)) * (f : R3 → ℂ) x
      ring
    rw [eLpNorm_congr_ae hae]
    have h_bound :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : R3 → ℂ) x) 2 volume
          < ENNReal.ofReal (ε / 4) :=
      hR₀_tail_f χ
        (fun x hx => hχ_one x (Metric.closedBall_subset_closedBall hR_ge_R₀ hx))
        hχ_bound hχ_smooth.continuous.measurable
    have h_ne :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : R3 → ℂ) x) 2 volume ≠ ⊤ :=
      ne_top_of_lt h_bound
    calc (eLpNorm (fun x => (1 - (χ x : ℂ)) * (f : R3 → ℂ) x) 2 volume).toReal
        < (ENNReal.ofReal (ε / 4)).toReal :=
          (ENNReal.toReal_lt_toReal h_ne ENNReal.ofReal_ne_top).mpr h_bound
      _ = ε / 4 := ENNReal.toReal_ofReal hε4.le
      _ < ε := by linarith
  -- Norm bound 2: ∀ i, ‖dg i - dh_R_i_Lp‖ < ε.
  · intro i
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
    have hae : ((dg i : R3 → ℂ) - ((hdh_R_MemLp i).toLp (dh_R i) : R3 → ℂ))
        =ᵐ[volume]
        fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x -
          (f : R3 → ℂ) x * dχℂ i x := by
      filter_upwards [(hdh_R_MemLp i).coeFn_toLp] with x hx
      show (dg i : R3 → ℂ) x -
            ((hdh_R_MemLp i).toLp (dh_R i) : R3 → ℂ) x = _
      rw [hx]
      show (dg i : R3 → ℂ) x -
            (χℂ x * (dg i : R3 → ℂ) x + (f : R3 → ℂ) x * dχℂ i x) =
        (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x - (f : R3 → ℂ) x * dχℂ i x
      ring
    rw [eLpNorm_congr_ae hae]
    have h_meas1 : AEStronglyMeasurable
        (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x) volume :=
      (continuous_const.sub hχℂ_smooth.continuous).aestronglyMeasurable.mul
        (h_dg_meas i)
    have h_meas2 : AEStronglyMeasurable
        (fun x => (f : R3 → ℂ) x * dχℂ i x) volume :=
      h_f_meas.mul (hdχℂ_smooth i).continuous.aestronglyMeasurable
    have hp_one_le_two : (1 : ENNReal) ≤ 2 := by norm_num
    have h_triangle : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x -
          (f : R3 → ℂ) x * dχℂ i x) 2 volume ≤
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x) 2 volume +
        eLpNorm (fun x => (f : R3 → ℂ) x * dχℂ i x) 2 volume :=
      eLpNorm_sub_le h_meas1 h_meas2 hp_one_le_two
    have h_bound1 :
        eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x) 2 volume
          < ENNReal.ofReal (ε / 4) :=
      hR_dg_tail i χ
        (fun x hx => hχ_one x
          (Metric.closedBall_subset_closedBall (hR_ge_R_dg i) hx))
        hχ_bound hχ_smooth.continuous.measurable
    have h_eLpNorm_f_eq :
        eLpNorm (f : R3 → ℂ) 2 volume = ENNReal.ofReal ‖f‖ := by
      rw [Lp.norm_def]
      exact (ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top).symm
    have h_bound2 :
        eLpNorm (fun x => (f : R3 → ℂ) x * dχℂ i x) 2 volume
          ≤ ENNReal.ofReal (ε / 4) := by
      have h_le :
          eLpNorm (fun x => (f : R3 → ℂ) x * dχℂ i x) 2 volume ≤
          ENNReal.ofReal ((M / R) * ‖f‖) := by
        calc eLpNorm (fun x => (f : R3 → ℂ) x * dχℂ i x) 2 volume
            ≤ eLpNorm (fun x => (M / R : ℝ) • (f : R3 → ℂ) x) 2 volume :=
              eLpNorm_mono_ae (Filter.Eventually.of_forall (h_fdχ_ptw i))
          _ = ‖(M / R : ℝ)‖ₑ * eLpNorm (f : R3 → ℂ) 2 volume := by
              rw [show (fun x => (M / R : ℝ) • (f : R3 → ℂ) x)
                    = (M / R : ℝ) • ((f : R3 → ℂ)) from rfl]
              erw [eLpNorm_const_smul]
          _ = ENNReal.ofReal (M / R) * ENNReal.ofReal ‖f‖ := by
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hMR_nn,
                  h_eLpNorm_f_eq]
          _ = ENNReal.ofReal ((M / R) * ‖f‖) :=
              (ENNReal.ofReal_mul hMR_nn).symm
      exact le_of_lt
        (lt_of_le_of_lt h_le ((ENNReal.ofReal_lt_ofReal_iff hε4).mpr hR_cross))
    have h_sum_bound : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x -
          (f : R3 → ℂ) x * dχℂ i x) 2 volume
          ≤ ENNReal.ofReal (ε / 2) := by
      calc eLpNorm
            (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x -
              (f : R3 → ℂ) x * dχℂ i x) 2 volume
          ≤ eLpNorm (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x) 2 volume +
            eLpNorm (fun x => (f : R3 → ℂ) x * dχℂ i x) 2 volume := h_triangle
        _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
              add_le_add h_bound1.le h_bound2
        _ = ENNReal.ofReal (ε / 2) := by
              rw [← ENNReal.ofReal_add hε4.le hε4.le]; congr 1; ring
    have h_ne : eLpNorm
        (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x -
          (f : R3 → ℂ) x * dχℂ i x) 2 volume ≠ ⊤ :=
      (lt_of_le_of_lt h_sum_bound ENNReal.ofReal_lt_top).ne
    calc (eLpNorm
            (fun x => (1 - (χ x : ℂ)) * (dg i : R3 → ℂ) x -
              (f : R3 → ℂ) x * dχℂ i x) 2 volume).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          (ENNReal.toReal_le_toReal h_ne ENNReal.ofReal_ne_top).mpr h_sum_bound
      _ = ε / 2 := ENNReal.toReal_ofReal (by linarith)
      _ < ε := by linarith

/-- **Multi-direction Meyers-Serrin**: simultaneous smooth c.s. approximation of
    `f` and all three weak derivatives. -/
lemma meyers_serrin_approx_multi
    (f : L2_R3) (dg : Fin 3 → L2_R3)
    (h_dg : ∀ i, HasWeakDerivative f i (dg i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ),
      ‖f - (memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ‖ < ε ∧
      ∀ i, ‖dg i - (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  -- Step 1: multi-truncation gives compactly supported intermediates.
  obtain ⟨h_R, dh_R, hh, hdh, hh_supp, hdh_supp, h_wk, hf_close, hdg_close⟩ :=
    truncation_approx_multi f dg h_dg (ε / 2) hε2
  -- Step 2: a single bump convolution mollifies them all simultaneously.
  obtain ⟨φ, hφ, hφ_supp, hφ_close, hdφ_close⟩ :=
    mollify_compactly_supported_multi h_R dh_R hh hdh hh_supp hdh_supp h_wk (ε / 2) hε2
  refine ⟨φ, hφ, hφ_supp, ?_, ?_⟩
  · -- ‖f - toLp φ‖ ≤ ‖f - toLp h_R‖ + ‖toLp h_R - toLp φ‖ < ε/2 + ε/2 = ε
    calc ‖f - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖
        ≤ ‖f - hh.toLp h_R‖ +
          ‖hh.toLp h_R -
            (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖ := by
          have h_eq : f - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ =
              (f - hh.toLp h_R) +
              (hh.toLp h_R -
                (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ) := by abel
          rw [h_eq]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hf_close hφ_close
      _ = ε := add_halves ε
  · -- Per direction: ‖dg i - ∂ᵢφ‖ ≤ ‖dg i - toLp (dh_R i)‖ + ‖toLp (dh_R i) - ∂ᵢφ‖
    intro i
    calc ‖dg i - (memLp_partialDeriv φ i hφ hφ_supp).toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖
        ≤ ‖dg i - (hdh i).toLp (dh_R i)‖ +
          ‖(hdh i).toLp (dh_R i) -
            (memLp_partialDeriv φ i hφ hφ_supp).toLp
              (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ := by
          have h_eq : dg i - (memLp_partialDeriv φ i hφ hφ_supp).toLp
              (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) =
              (dg i - (hdh i).toLp (dh_R i)) +
              ((hdh i).toLp (dh_R i) - (memLp_partialDeriv φ i hφ hφ_supp).toLp
                (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) := by abel
          rw [h_eq]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hdg_close i) (hdφ_close i)
      _ = ε := add_halves ε

end Spectra.Sobolev

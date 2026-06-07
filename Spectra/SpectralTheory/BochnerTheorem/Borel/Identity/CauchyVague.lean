/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerTheorem/Borel/Identity/CauchyVague.lean
-/
import Spectra.SpectralTheory.BochnerTheorem.Borel.Identity.CauchyTransform
import Spectra.SpectralTheory.BochnerTheorem.Borel.Identity.BoundedCDF
namespace QuantumMechanics.SpectralTheory

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal ComplexConjugate
open Resolvent Bochner FourierUniqueness HerglotzStieltjes

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- C₀ vague convergence along the Helly subsequence. -/
lemma borel_cauchy_vague
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (borelCauchyApprox U_grp ξ z) atTop
      (𝓝 (∫ lambda, ((lambda : ℂ) - z)⁻¹ ∂(borelMeasure U_grp ξ))) := by
  -- ═══════════════════════════ SETUP ═══════════════════════════
  set g  : ℝ → ℂ           := fun l => ((l : ℂ) - z)⁻¹ with hg_def
  set G  : ℝ → ℝ           := borelLimitCDF U_grp ξ with hG_def
  set μ  : Measure ℝ       := borelMeasure U_grp ξ  with hμ_def
  set ρ  : ℕ → ℝ → ℝ       :=
    fun k => borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) with hρ_def
  set μk : ℕ → Measure ℝ   :=
    fun k => volume.withDensity (fun l => ENNReal.ofReal (ρ k l)) with hμk_def
  set M  : ℝ               := ‖ξ‖ ^ 2 with hM_def
  have hM_nn   : 0 ≤ M := by positivity
  have hzim    : 0 < |z.im| := abs_pos.mpr hz
  have hG_mono : Monotone G := borelLimitCDF_mono U_grp ξ
  have hG_bnd  : ∀ x, G x ∈ Set.Icc (0 : ℝ) M :=
    (borelHelly U_grp ξ).choose_spec.choose_spec.2.2.1
  -- ─────────── g and ρ ───────────
  have hg_cont : Continuous g := by
    refine (Complex.continuous_ofReal.sub continuous_const).inv₀ (fun l h => ?_)
    have : -z.im = 0 := by
      have := congrArg Complex.im h
      simpa [Complex.sub_im, Complex.ofReal_im] using this
    exact hz (neg_eq_zero.mp this)
  --have hg_meas : AEStronglyMeasurable g volume := hg_cont.aestronglyMeasurable
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
  -- ─────────── μk univ = ofReal M, hence finite ───────────
  have hμk_univ : ∀ k, μk k Set.univ = ENNReal.ofReal M := fun k => by
    show (volume.withDensity (fun l => ENNReal.ofReal (ρ k l))) Set.univ = _
    rw [withDensity_apply _ MeasurableSet.univ, MeasureTheory.setLIntegral_univ,
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hρint k)
              (Filter.Eventually.of_forall (hρnn k)),
        hmass]
  haveI μk_fin : ∀ k, IsFiniteMeasure (μk k) := fun k =>
    ⟨by rw [hμk_univ k]; exact ENNReal.ofReal_lt_top⟩
  have hμk_real : ∀ k, (μk k Set.univ).toReal = M := fun k => by
    rw [hμk_univ k, ENNReal.toReal_ofReal hM_nn]
  -- ─────────── μ identification: rfl ───────────
  have μ_st : μ = (borelLimitCDF_mono U_grp ξ).stieltjesFunction.measure := rfl
  -- ─────────── μ ≤ ENNReal.ofReal M (and toReal version) ───────────
  -- Replicates the bound used inside `borelMeasure_isFiniteMeasure`.
  have hμ_le : μ Set.univ ≤ ENNReal.ofReal M := by
    show borelMeasure U_grp ξ Set.univ ≤ _
    have h_tend : ∀ x, Tendsto G (𝓝[>] x) (𝓝 (Function.rightLim G x)) :=
      fun x => hG_mono.tendsto_rightLim x
    have h_sf_le : ∀ x, hG_mono.stieltjesFunction x ≤ M := fun x =>
      le_of_tendsto (h_tend x) (Filter.Eventually.of_forall fun y => (hG_bnd y).2)
    have h_sf_nn : ∀ x, 0 ≤ hG_mono.stieltjesFunction x := fun x =>
      ge_of_tendsto (h_tend x) (Filter.Eventually.of_forall fun y => (hG_bnd y).1)
    have h_cover : ⋃ n : ℕ, Set.Ioc (-(n : ℝ)) (n : ℝ) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      rw [abs_lt] at hn
      exact Set.mem_iUnion.mpr ⟨n, hn.1, hn.2.le⟩
    have h_mono_sets : Monotone fun n : ℕ => Set.Ioc (-(n : ℝ)) (n : ℝ) := fun m n hmn =>
      Set.Ioc_subset_Ioc (neg_le_neg (by exact_mod_cast hmn)) (by exact_mod_cast hmn)
    have h_bnd_Ioc : ∀ n : ℕ, μ (Set.Ioc (-(n : ℝ)) (n : ℝ)) ≤ ENNReal.ofReal M := by
      intro n
      show hellyLimitMeasure G hG_mono _ ≤ _
      rw [HerglotzStieltjes.hellyLimitMeasure_Ioc]
      exact ENNReal.ofReal_le_ofReal (by linarith [h_sf_le (n : ℝ), h_sf_nn (-(n : ℝ))])
    calc borelMeasure U_grp ξ Set.univ
        = borelMeasure U_grp ξ (⋃ n : ℕ, Set.Ioc (-(n : ℝ)) (n : ℝ)) := by rw [h_cover]
      _ = ⨆ n : ℕ, borelMeasure U_grp ξ (Set.Ioc (-(n : ℝ)) (n : ℝ)) := h_mono_sets.measure_iUnion
      _ ≤ ENNReal.ofReal M := iSup_le h_bnd_Ioc
  have hμM : (μ Set.univ).toReal ≤ M := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ_le
    rwa [ENNReal.toReal_ofReal hM_nn] at h
  -- ─────────── g integrable wrt both μk k and μ ───────────
  haveI : IsFiniteMeasure μ := inferInstance
  have hg_int_μ : Integrable g μ :=
    Integrable.of_bound hg_cont.aestronglyMeasurable (1 / |z.im|)
      (Filter.Eventually.of_forall hg_bdd)
  have hg_int_μk : ∀ k, Integrable g (μk k) := fun k => by
    haveI := μk_fin k
    exact Integrable.of_bound hg_cont.aestronglyMeasurable (1 / |z.im|)
      (Filter.Eventually.of_forall hg_bdd)
  -- ─────────── Cauchy approximant as ∫ g ∂(μk k) ───────────
  have cauchy_eq : ∀ k, borelCauchyApprox U_grp ξ z k = ∫ l, g l ∂(μk k) := fun k => by
    show ∫ lambda : ℝ, ((lambda : ℂ) - z)⁻¹ * (ρ k lambda : ℂ) = ∫ l, g l ∂(μk k)
    rw [show μk k = volume.withDensity (fun l => ENNReal.ofReal (ρ k l)) from rfl,
        integral_withDensity_eq_integral_toReal_smul (hρenn k)
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards with l
    rw [ENNReal.toReal_ofReal (hρnn k l), Complex.real_smul,
        show (ρ k l : ℂ) * g l = g l * (ρ k l : ℂ) from mul_comm _ _]
  -- ─────────── μk identification (the meaty one) ───────────
  -- Use `ext_of_Iic`: both finite, agree on `Iic a` for every `a`.
  have μk_st : ∀ k, μk k =
      (borelApproxCDF_mono U_grp ξ (borelSubseq U_grp ξ k)).stieltjesFunction.measure := by
    intro k
    set F : ℝ → ℝ := borelApproxCDF U_grp ξ (borelSubseq U_grp ξ k) with hF_def
    have hF_mono : Monotone F := borelApproxCDF_mono U_grp ξ (borelSubseq U_grp ξ k)
    have hF_cont : Continuous F := borelCDF_continuous _ _ _
    -- sf agrees with F pointwise (continuity)
    have hSF_eq : ∀ x, hF_mono.stieltjesFunction x = F x := fun x => by
      exact HerglotzStieltjes.stieltjes_eq_at_continuousAt _ hF_mono x hF_cont.continuousAt
    -- limit of F at -∞ is 0
    have hF_atBot : Tendsto F atBot (𝓝 0) :=
      borelCDF_tendsto_atBot _ _ _
    -- hence limit of sf at -∞ is 0
    have hSF_atBot : Tendsto hF_mono.stieltjesFunction atBot (𝓝 0) := by
      apply hF_atBot.congr'
      filter_upwards with x; exact (hSF_eq x).symm
    -- finiteness of sf-measure (will be needed for ext)
    -- We only need IsFiniteMeasure on μk for ext_of_Iic.
    apply Measure.ext_of_Iic
    intro a
    -- LHS: (μk k)(Iic a)
    have hLHS : μk k (Set.Iic a) = ENNReal.ofReal (F a) := by
      show (volume.withDensity (fun l => ENNReal.ofReal (ρ k l))) (Set.Iic a) = _
      rw [withDensity_apply _ measurableSet_Iic]
      have h_intOn : IntegrableOn (ρ k) (Set.Iic a) volume :=
        (hρint k).integrableOn
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_intOn
              (Filter.Eventually.of_forall (hρnn k))]
      show ENNReal.ofReal (∫ l in Set.Iic a, ρ k l ∂volume) = ENNReal.ofReal (F a)
      rfl -- borelCDF a := ∫ lambda in Set.Iic a, borelDensity ...
    -- RHS: sf.measure (Iic a) = ofReal (sf a - 0) = ofReal (F a)
    have hRHS : hF_mono.stieltjesFunction.measure (Set.Iic a) = ENNReal.ofReal (F a) := by
      rw [StieltjesFunction.measure_Iic _ hSF_atBot, hSF_eq, sub_zero]
    rw [hLHS, hRHS]
  -- ─────────── tail bound for μk and μ on the complement of [-R,R] ───────────
  -- (factored as a `tail` lemma later, parametric in ν)
  -- ─────────── ε-δ unwrap and R-selection ───────────
  rw [Metric.tendsto_atTop]; intro ε hε
  -- choose R: continuity points of G with R, -R ∉ disc(G), and 2M/(R-|z.re|) < ε/2.
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
    have hRgap : 4 * M / ε + 1 < R - |z.re| := by linarith
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
  have hRgap : 0 < R - |z.re| := by linarith
  -- ─────────── tail bound (parametric ν) ───────────
  have tail : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], (ν Set.univ).toReal ≤ M →
      ‖∫ l in (Set.Ioc (-R) R)ᶜ, g l ∂ν‖ ≤ M / (R - |z.re|) := by
    intro ν _ hνM
    -- on (Ioc -R R)ᶜ, |l| ≥ R, so |l - z.re| ≥ R - |z.re|, so |l - z| ≥ R - |z.re|.
    have hbd : ∀ l ∈ (Set.Ioc (-R) R)ᶜ, ‖g l‖ ≤ 1 / (R - |z.re|) := by
      intro l hl
      have hl_outside : l ≤ -R ∨ R < l := by
        simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hl
        exact hl
      have h_absL : R ≤ |l| := by
        rcases hl_outside with hL | hR'
        · have : R ≤ -l := by linarith
          calc R ≤ -l := this
            _ ≤ |l| := neg_le_abs l
        · linarith [le_abs_self l]
      -- |l - z.re| ≥ |l| - |z.re| ≥ R - |z.re|
      have h_lzre : R - |z.re| ≤ |l - z.re| := by
        calc R - |z.re| ≤ |l| - |z.re| := by linarith
          _ ≤ |l - z.re|              := abs_sub_abs_le_abs_sub _ _
      -- |l - z| ≥ |(l - z).re| = |l - z.re|
      have h_lz : R - |z.re| ≤ ‖(l : ℂ) - z‖ := by
        calc R - |z.re| ≤ |l - z.re|         := h_lzre
          _ = |((l : ℂ) - z).re|             := by simp [Complex.sub_re, Complex.ofReal_re]
          _ ≤ ‖(l : ℂ) - z‖                  := Complex.abs_re_le_norm _
      have h_lz_pos : 0 < ‖(l : ℂ) - z‖ := lt_of_lt_of_le hRgap h_lz
      have h_lz_ne : ((l : ℂ) - z) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at h_lz_pos; exact h_lz_pos.false
      show ‖((l : ℂ) - z)⁻¹‖ ≤ 1 / (R - |z.re|)
      rw [norm_inv]
      calc (‖(l : ℂ) - z‖)⁻¹
          = 1 / ‖(l : ℂ) - z‖   := by rw [one_div]
        _ ≤ 1 / (R - |z.re|)    := div_le_div_of_nonneg_left (by norm_num) hRgap h_lz
    calc ‖∫ l in (Set.Ioc (-R) R)ᶜ, g l ∂ν‖
        ≤ (1 / (R - |z.re|)) * ν.real (Set.Ioc (-R) R)ᶜ :=
          norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hbd
      _ ≤ (1 / (R - |z.re|)) * M := by
          have : ν.real (Set.Ioc (-R) R)ᶜ ≤ M :=
            (ENNReal.toReal_mono (measure_ne_top _ _)
              (measure_mono (Set.subset_univ _))).trans hνM
          gcongr
      _ = M / (R - |z.re|) := by ring
  -- ─────────── middle convergence on [-R, R] ───────────
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
  -- ─────────── assemble ───────────
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

end QuantumMechanics.SpectralTheory

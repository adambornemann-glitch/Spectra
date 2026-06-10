/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/Dynamics/FaaDiBruno/Helper.lean
-/
import Spectra.InformationGeometry.Stone.Family
import Spectra.InformationGeometry.Dynamics.CubicTensor

import Mathlib.Tactic.Explode
open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)

/-- **Off-diagonal cross-score derivative, with components.**

The cross-score integral `θ' ↦ −∫ p(θ,ω)·sⱼ(θ',ω) dμ` is Fréchet
differentiable at every `θ₀ ∈ paramDomain` — not only at `θ₀ = θ`,
which is `cross_score_hasFDerivAt` — and the `i`-th component of its
derivative is `−∫ p(θ,ω)·(∂ᵢsⱼ)(θ₀,ω) dμ`.

This is `cross_score_differentiableAt`'s Leibniz interchange, upgraded
to keep the derivative and evaluate its components.  (That lemma is the
`.differentiableAt` shadow of this one and could be re-derived from it
in one line; this lemma morally belongs next to its siblings in
`Hessian.lean`.) -/
lemma cross_score_hasFDerivAt'
    {θ θ₀ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (hθ₀ : θ₀ ∈ M.paramDomain) (j : Fin n) :
    ∃ g₁ : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => -∫ ω, M.density θ ω *
          M.toRegularStatisticalModel.score θ' j ω ∂M.refMeasure)
        g₁ θ₀ ∧
      ∀ i : Fin n,
        g₁ (EuclideanSpace.single i 1) =
          -∫ ω, M.density θ ω * M.scorePartial θ₀ i j ω ∂M.refMeasure := by
  obtain ⟨ε₁, hε₁, bound₁, hbound₁_int, h_ae₁⟩ :=
    M.score_fderiv_bound θ hθ θ₀ hθ₀ j
  obtain ⟨ε₂, hε₂, hball₂⟩ :=
    Metric.isOpen_iff.mp M.isOpen_paramDomain θ₀ hθ₀
  set ε := min ε₁ ε₂ with hε_def
  have hε_pos : 0 < ε := lt_min hε₁ hε₂
  -- Base-point integrability via the crossEntropy_fderiv_bound trick
  -- (verbatim from `cross_score_differentiableAt`, with `mono'`).
  have h_base_int : Integrable
      (fun ω => M.density θ ω *
        M.toRegularStatisticalModel.score θ₀ j ω) M.refMeasure := by
    obtain ⟨ε₃, hε₃, bound₃, hbound₃_int, h_ae₃⟩ :=
      M.crossEntropy_fderiv_bound θ hθ θ₀ hθ₀
    apply Integrable.mono' hbound₃_int
    · exact (M.toStatisticalModel.density_measurable θ hθ).aestronglyMeasurable.mul
        (M.toRegularStatisticalModel.score_aestronglyMeasurable hθ₀ j)
    · filter_upwards [h_ae₃, M.density_pos_ae θ₀ hθ₀] with ω hω₃ hω_pos
      have h_ne : M.density θ₀ ω ≠ 0 := ne_of_gt hω_pos
      have h_diff := M.toStatisticalModel.density_differentiableAt hθ₀ ω
      have h_score_eq : M.toRegularStatisticalModel.score θ₀ j ω =
          fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀
            (EuclideanSpace.single j 1) := by
        rw [(h_diff.hasFDerivAt.log h_ne).fderiv,
            ContinuousLinearMap.smul_apply, smul_eq_mul]
        unfold RegularStatisticalModel.score RegularStatisticalModel.partialDensity
        field_simp
      calc ‖M.density θ ω * M.toRegularStatisticalModel.score θ₀ j ω‖
          = ‖(M.density θ ω •
              fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀)
              (EuclideanSpace.single j 1)‖ := by
            simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, h_score_eq]
        _ ≤ ‖M.density θ ω •
              fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀‖ *
            ‖(EuclideanSpace.single j (1 : ℝ) : ParamSpace n)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖M.density θ ω •
              fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀‖ := by
            rw [PiLp.norm_single, norm_one, mul_one]
        _ ≤ bound₃ ω := (hω₃ θ₀ (Metric.mem_ball_self hε₃)).2
  -- Measurability of the dominated derivative integrand at θ₀
  -- (verbatim density-ratio trick from `cross_score_differentiableAt`).
  have h_F'_meas : AEStronglyMeasurable
      (fun ω => M.density θ ω •
        fderiv ℝ (fun θ' =>
          M.toRegularStatisticalModel.score θ' j ω) θ₀)
      M.refMeasure := by
    have h_base := M.score_deriv_aestronglyMeasurable hθ₀ j
    have h_ratio : AEStronglyMeasurable
        (fun ω => M.density θ ω * (M.density θ₀ ω)⁻¹)
        M.refMeasure :=
      ((M.toStatisticalModel.density_measurable θ hθ).mul
        (M.toStatisticalModel.density_measurable θ₀ hθ₀).inv).aestronglyMeasurable
    have h_eq : ∀ᵐ ω ∂M.refMeasure,
        M.density θ ω •
          fderiv ℝ (fun θ' =>
            M.toRegularStatisticalModel.score θ' j ω) θ₀ =
        (M.density θ ω * (M.density θ₀ ω)⁻¹) •
          (M.density θ₀ ω •
            fderiv ℝ (fun θ' =>
              M.toRegularStatisticalModel.score θ' j ω) θ₀) := by
      filter_upwards [M.density_pos_ae θ₀ hθ₀] with ω hω
      ext v
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp
    exact (h_ratio.smul h_base).congr
      (h_eq.mono fun ω hω => hω.symm)
  -- Leibniz interchange at θ₀ (verbatim from `cross_score_differentiableAt`).
  have hLeibniz : HasFDerivAt
      (fun θ' => ∫ ω, M.density θ ω *
        M.toRegularStatisticalModel.score θ' j ω ∂M.refMeasure)
      (∫ ω, M.density θ ω •
        fderiv ℝ (fun θ' =>
          M.toRegularStatisticalModel.score θ' j ω) θ₀
        ∂M.refMeasure) θ₀ := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Metric.ball θ₀ ε)
      (F' := fun θ' ω => M.density θ ω •
        fderiv ℝ (fun θ'' =>
          M.toRegularStatisticalModel.score θ'' j ω) θ')
      (bound := bound₁)
      (Metric.ball_mem_nhds θ₀ hε_pos)
    · filter_upwards [Metric.ball_mem_nhds θ₀ hε_pos] with θ' hθ'
      exact (M.toStatisticalModel.density_measurable θ hθ).aestronglyMeasurable.mul
        (M.toRegularStatisticalModel.score_aestronglyMeasurable
          (hball₂ (Metric.ball_subset_ball (min_le_right ε₁ ε₂) hθ'))
          j)
    · exact h_base_int
    · exact h_F'_meas
    · filter_upwards [h_ae₁] with ω hω θ' hθ'
      exact (hω θ'
        (Metric.ball_subset_ball (min_le_left ε₁ ε₂) hθ')).2
    · exact hbound₁_int
    · filter_upwards [h_ae₁] with ω hω θ' hθ'
      exact (hω θ'
        (Metric.ball_subset_ball (min_le_left ε₁ ε₂) hθ')).1
  -- The derivative integrand is integrable, so components of the
  -- integral CLM are integrals of the pointwise components.
  have hL_int : Integrable
      (fun ω => M.density θ ω •
        fderiv ℝ (fun θ' =>
          M.toRegularStatisticalModel.score θ' j ω) θ₀)
      M.refMeasure := by
    apply Integrable.mono' hbound₁_int h_F'_meas
    filter_upwards [h_ae₁] with ω hω
    exact (hω θ₀ (Metric.mem_ball_self hε₁)).2
  refine ⟨-(∫ ω, M.density θ ω •
      fderiv ℝ (fun θ' =>
        M.toRegularStatisticalModel.score θ' j ω) θ₀ ∂M.refMeasure),
    hLeibniz.neg, fun i => ?_⟩
  -- (−L)(eᵢ) = −∫ p(θ,ω)·∂ᵢsⱼ(θ₀,ω) dμ
  simp only [ContinuousLinearMap.neg_apply, neg_inj]
  rw [ContinuousLinearMap.integral_apply hL_int]
  -- (p(θ,ω) • fderiv(sⱼ(·,ω))(θ₀))(eᵢ) = p(θ,ω) · ∂ᵢsⱼ(θ₀,ω) is `rfl`
  -- after unfolding `scorePartial`; `congr 1` closes up to defeq.
  congr 1

namespace ThriceDifferentiableModel
variable (M : ThriceDifferentiableModel n Ω)
namespace DivergencePreservingFamily
variable {M : ThriceDifferentiableModel n Ω}
variable (F : M.toTwiceDifferentiableModel.DivergencePreservingFamily)
open TwiceDifferentiableModel

/-- **Derivative of the moving first variation against a moving vector.**

With `α := φ_t θ`, for any vector field `V` differentiable at `θ`, the
scalar map `θ₁ ↦ (d D(α‖·))(φ_t θ₁) (V θ₁)` is differentiable at `θ`
and its `a`-th partial there is `g_α(dφ_t(θ)(eₐ), V θ)`.

This is the frozen-vector computation extracted from `preserves_fisher`'s
`h_LHS` (where `V θ₂ = dφ_t(θ₂)(e_b)`), generalized over `V`: since
`fderiv (klDiv α)` vanishes at `α`, the motion of `V` contributes only
`o(θ₁ - θ)` — the operator factor is `o(1)` and the vector increment is
`O(θ₁ - θ)` — so only the frozen vector `V θ` survives, paired against
the Hessian, which is the Fisher metric.  Applications: `h_Q_val` in
`kl_faa_di_bruno` takes `V θ₁ = d²φ(θ₁)(e_b, e_c)` (a live second
derivative), recovering the `g(α)(dφ_a, d²φ_bc)` correction term. -/
lemma fderiv_klDiv_phi_apply_live
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ) (a : Fin n)
    {V : ParamSpace n → ParamSpace n} (hV : DifferentiableAt ℝ V θ) :
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (M.klDiv (F.φ t θ)) (F.φ t θ₁) (V θ₁)) θ
      (EuclideanSpace.single a 1) =
    M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) (V θ) := by
  set α := F.φ t θ with hα_def
  have hα : α ∈ M.paramDomain := F.maps_domain t θ hθ
  have hφ_smooth : ContDiff ℝ ⊤ (F.φ t) :=
    F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hφ_diff_at : ∀ θ₂, DifferentiableAt ℝ (F.φ t) θ₂ :=
    fun θ₂ => (hφ_smooth.differentiable WithTop.top_ne_zero).differentiableAt
  have hKL_zero : fderiv ℝ (M.klDiv α) α = 0 :=
    (M.klDiv_fderiv_eq_zero hα).fderiv
  -- Abbreviations
  set u := fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1) with hu_def
  set v₀ := V θ with hv₀_def
  -- ── The "live" function G and "frozen" function R ──
  set G : ParamSpace n → ℝ := fun θ₂ =>
    fderiv ℝ (M.klDiv α) (F.φ t θ₂) (V θ₂) with hG_def
  set R : ParamSpace n → ℝ := fun θ₂ =>
    fderiv ℝ (M.klDiv α) (F.φ t θ₂) v₀ with hR_def
  -- ── Both vanish at θ ──
  have hφtθ_eq_α : F.φ t θ = α := hα_def.symm
  have hG_zero : G θ = 0 := by
    simp only [hG_def, hφtθ_eq_α, hKL_zero, ContinuousLinearMap.zero_apply]
  have hR_zero : R θ = 0 := by
    simp only [hR_def, hφtθ_eq_α, hKL_zero, ContinuousLinearMap.zero_apply]
  -- Part I: HasFDerivAt for each Sⱼ(θ₂) := fderiv(klDiv α)(φ_t θ₂)(eⱼ)
  have hSj : ∀ j : Fin n, ∃ g'ⱼ : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt (fun θ' => fderiv ℝ (M.klDiv α) θ'
        (EuclideanSpace.single j 1)) g'ⱼ α ∧
      (∀ i : Fin n, g'ⱼ (EuclideanSpace.single i 1) =
        M.toRegularStatisticalModel.fisherMatrix α i j) := by
    intro j
    obtain ⟨g'ⱼ, hg'ⱼ, hg'ⱼ_eval⟩ := M.cross_score_hasFDerivAt hα j
    refine ⟨g'ⱼ, ?_, hg'ⱼ_eval⟩
    exact hg'ⱼ.congr_of_eventuallyEq (by
      filter_upwards [M.isOpen_paramDomain.mem_nhds hα] with θ' hθ'
      exact (M.klDiv_partial_j hα hθ' j))
  have hSj_comp : ∀ j : Fin n, ∃ g'ⱼ : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)
        (EuclideanSpace.single j 1))
        g'ⱼ θ ∧
      (∀ i : Fin n, g'ⱼ (EuclideanSpace.single i 1) =
        ∑ k : Fin n, (fderiv ℝ (F.φ t) θ (EuclideanSpace.single i 1)).ofLp k *
          M.toRegularStatisticalModel.fisherMatrix α k j) := by
    intro j
    obtain ⟨g'ⱼ, hg'ⱼ_α, hg'ⱼ_eval⟩ := hSj j
    refine ⟨g'ⱼ.comp (fderiv ℝ (F.φ t) θ), ?_, ?_⟩
    · -- HasFDerivAt via chain rule
      convert hg'ⱼ_α.comp θ (hφ_diff_at θ).hasFDerivAt using 1
    · -- Component evaluation
      intro i
      rw [ContinuousLinearMap.comp_apply]
      set w := fderiv ℝ (F.φ t) θ (EuclideanSpace.single i 1)
      conv_lhs => rw [show w = ∑ k : Fin n, w.ofLp k •
          EuclideanSpace.single k 1 from by ext p; simp [Pi.single,
            Function.update_apply, Finset.mem_univ]]
      rw [map_sum]; simp_rw [map_smul, smul_eq_mul, hg'ⱼ_eval]
  -- Part II: HasFDerivAt for R(θ₂) = Σⱼ v₀ⱼ · Sⱼ(φ_t θ₂)
  have hR_eq : ∀ θ₂, R θ₂ = ∑ j : Fin n, v₀.ofLp j *
      fderiv ℝ (M.klDiv α) (F.φ t θ₂) (EuclideanSpace.single j 1) := by
    intro θ₂
    simp only [hR_def]
    conv_lhs => rw [show v₀ = ∑ j : Fin n, v₀.ofLp j •
        EuclideanSpace.single j 1 from by ext p; simp [Pi.single,
          Function.update_apply, Finset.mem_univ]]
    rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
  set fR : ParamSpace n →L[ℝ] ℝ :=
    ∑ j : Fin n, v₀.ofLp j • (hSj_comp j).choose with hfR_def
  have hR_fderiv : HasFDerivAt R fR θ := by
    have hR_sum : R =ᶠ[𝓝 θ] (fun θ₂ => ∑ j : Fin n, v₀.ofLp j *
        fderiv ℝ (M.klDiv α) (F.φ t θ₂) (EuclideanSpace.single j 1)) := by
      filter_upwards with θ₂; exact hR_eq θ₂
    apply HasFDerivAt.congr_of_eventuallyEq _ hR_sum
    apply HasFDerivAt.fun_sum
    intro j _
    exact ((hSj_comp j).choose_spec.1).const_mul (v₀.ofLp j)
  -- Part III: G - R = o(‖·-θ‖)
  have hGR_eq : ∀ θ₂, G θ₂ - R θ₂ =
      fderiv ℝ (M.klDiv α) (F.φ t θ₂) (V θ₂ - v₀) := by
    intro θ₂; simp only [hG_def, hR_def, ← map_sub]
  have h_factor1 : Tendsto
      (fun θ₂ => ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂)‖) (𝓝 θ) (𝓝 0) := by
    -- Step 1: Each component tends to 0
    have h_comp : ∀ j : Fin n, Tendsto
        (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)
          (EuclideanSpace.single j 1)) (𝓝 θ) (𝓝 0) := by
      intro j
      have h_ev : (fun θ' => fderiv ℝ (M.klDiv α) θ'
          (EuclideanSpace.single j 1)) =ᶠ[𝓝 α]
          (fun θ' => -∫ ω, M.density α ω *
            M.toRegularStatisticalModel.score θ' j ω ∂M.refMeasure) := by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hα] with θ' hθ'
        exact M.klDiv_partial_j hα hθ' j
      obtain ⟨_, hg_j, _⟩ := M.cross_score_hasFDerivAt hα j
      -- HasFDerivAt ⟹ ContinuousAt, transferred via eventuallyEq
      have h_cont : ContinuousAt (fun θ' => fderiv ℝ (M.klDiv α) θ'
          (EuclideanSpace.single j 1)) α :=
        hg_j.continuousAt.congr h_ev.symm
      have h_val : fderiv ℝ (M.klDiv α) α (EuclideanSpace.single j 1) = 0 := by
        rw [hKL_zero]; exact ContinuousLinearMap.zero_apply _
      rw [← h_val]
      exact h_cont.tendsto.comp
        (hφtθ_eq_α ▸ hφ_smooth.continuous.continuousAt.tendsto)
    -- Step 2: ‖L‖ ≤ ∑ⱼ ‖L(eⱼ)‖ via opNorm_le_bound
    have h_bound : ∀ θ₂, ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂)‖ ≤
        ∑ j : Fin n, ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂)
          (EuclideanSpace.single j 1)‖ := by
      intro θ₂
      apply ContinuousLinearMap.opNorm_le_bound _
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      intro v
      conv_lhs => rw [show v = ∑ j : Fin n, v j • EuclideanSpace.single j 1 from by
        ext i; simp [Pi.single, Function.update_apply, Finset.mem_univ]]
      rw [map_sum]; simp_rw [map_smul]
      calc ‖∑ j, v j • fderiv ℝ (M.klDiv α) (F.φ t θ₂)
              (EuclideanSpace.single j 1)‖
          ≤ ∑ j, ‖v j • fderiv ℝ (M.klDiv α) (F.φ t θ₂)
              (EuclideanSpace.single j 1)‖ := norm_sum_le _ _
        _ = ∑ j, |v j| * ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂)
              (EuclideanSpace.single j 1)‖ := by
            simp_rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ j, ‖v‖ * ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂)
              (EuclideanSpace.single j 1)‖ := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            -- |v j| ≤ ‖v‖ in EuclideanSpace
            have h_sq : (v j) ^ 2 ≤ ‖v‖ ^ 2 := by
              rw [EuclideanSpace.norm_eq,
                  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
              calc (v j) ^ 2 = ‖v j‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
                _ ≤ ∑ i, ‖v.ofLp i‖ ^ 2 :=
                    Finset.single_le_sum (f := fun i => ‖v.ofLp i‖ ^ 2)
                      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
            calc |v j| = √((v j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
              _ ≤ √(‖v‖ ^ 2) := Real.sqrt_le_sqrt h_sq
              _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)
        _ = (∑ j, ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂)
              (EuclideanSpace.single j 1)‖) * ‖v‖ := by
            rw [Finset.sum_mul]; ring_nf
    -- Step 3: Squeeze — sum of components → 0
    apply squeeze_zero (fun _ => norm_nonneg _) h_bound
    have := tendsto_finsetSum Finset.univ
        (fun j _ => (h_comp j).norm)
    simp only [norm_zero, Finset.sum_const_zero] at this
    exact this
  have h_factor2 : ∃ C > 0, ∀ᶠ θ₂ in 𝓝 θ,
      ‖V θ₂ - v₀‖ ≤ C * ‖θ₂ - θ‖ := by
    set L := fderiv ℝ V θ
    have hfd := hV.hasFDerivAt
    refine ⟨‖L‖ + 1, by positivity, ?_⟩
    rw [Metric.eventually_nhds_iff]
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
      (Asymptotics.isLittleO_iff.mp hfd.isLittleO one_pos)
    refine ⟨δ, hδ, fun θ₂ hθ₂ => ?_⟩
    have hest := hball (Metric.mem_ball.mp hθ₂)
    calc ‖V θ₂ - v₀‖
        = ‖(V θ₂ - v₀ - L (θ₂ - θ)) + L (θ₂ - θ)‖ := by abel_nf
      _ ≤ ‖V θ₂ - v₀ - L (θ₂ - θ)‖ + ‖L (θ₂ - θ)‖ := norm_add_le _ _
      _ ≤ 1 * ‖θ₂ - θ‖ + ‖L‖ * ‖θ₂ - θ‖ := by
          apply add_le_add
          · have hest := hball hθ₂
            exact hest
          · exact ContinuousLinearMap.le_opNorm L _
      _ = (‖L‖ + 1) * ‖θ₂ - θ‖ := by ring
  have hGR_littleo : (fun θ₂ => G θ₂ - R θ₂) =o[𝓝 θ] (fun θ₂ => θ₂ - θ) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨C, hC, hC_bound⟩ := h_factor2
    have h_small := Metric.tendsto_nhds.mp h_factor1 (ε / C) (div_pos hε hC)
    filter_upwards [h_small, hC_bound] with θ₂ h1 h2
    rw [hGR_eq]
    calc ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂) (V θ₂ - v₀)‖
        ≤ ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂)‖ * ‖V θ₂ - v₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε / C) * (C * ‖θ₂ - θ‖) := by
          apply mul_le_mul
          · rw [dist_eq_norm, sub_zero, norm_norm] at h1
            exact le_of_lt h1
          · exact h2
          · exact norm_nonneg (V θ₂ - v₀)
          · exact div_nonneg hε.le hC.le
      _ = ε * ‖θ₂ - θ‖ := by field_simp
  -- Part IV: HasFDerivAt G fR θ (from Parts II + III)
  have hG_fderiv : HasFDerivAt G fR θ := by
    have h1 := hR_fderiv.isLittleO.add hGR_littleo
    have h2 : (fun θ₂ => (R θ₂ - R θ - fR (θ₂ - θ)) + (G θ₂ - R θ₂)) =
        (fun θ₂ => G θ₂ - G θ - fR (θ₂ - θ)) := by
      ext θ₂; rw [hR_zero, hG_zero]; ring
    rw [h2] at h1
    exact hasFDerivAt_iff_isLittleO.mpr h1
  -- Part V: Evaluate fR(e_a) = fisherBilin α u v₀
  rw [show fderiv ℝ G θ = fR from hG_fderiv.fderiv]
  simp only [hfR_def, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  conv_lhs =>
    arg 2; ext j
    rw [(hSj_comp j).choose_spec.2 a]
  rw [M.toRegularStatisticalModel.fisherBilin_eq_sum_fisherMatrix hα
    (M.scoreSqIntegrable α hα)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext j; ring

end DivergencePreservingFamily
end ThriceDifferentiableModel
end TwiceDifferentiableModel

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Regularity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
/-!
# The Hessian Theorem: ∂²D = g

This file proves the foundational theorem of information geometry: the
Fisher information matrix is the second derivative of the KL divergence
at the diagonal.

  D(θ ‖ θ) = 0                                         (minimum)
  ∂D(θ ‖ θ')/∂θ'ʲ |_{θ'=θ} = 0                        (critical point)
  ∂²D(θ ‖ θ')/∂θ'ⁱ∂θ'ʲ |_{θ'=θ} = g_{ij}(θ)          (Fisher metric)

Consequence: the Fisher metric is the **infinitesimal divergence** —
the second-order Taylor expansion of D at the diagonal. Any map
preserving D automatically preserves g.

The KL divergence `klDiv` itself is defined once at the model level in `StatisticalModel.lean`;
this file develops its calculus.

## Main statements

* `klDiv_self`, `klDiv_nonneg` — diagonal vanishing, Gibbs inequality
* `klDiv_fderiv_eq_zero` — vanishing first derivative at the diagonal
* `klDiv_hessian_eq_fisher` — **the Hessian theorem**
* `klDiv_taylor_second_order` — quadratic Taylor expansion of D
-/
open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)

/-- The standard-coordinate expansion in `ParamSpace n`. -/
private lemma paramSpace_eq_sum_single (u : ParamSpace n) :
    u = ∑ i : Fin n, u.ofLp i • EuclideanSpace.single i 1 := by
  ext p
  simp [Pi.single, Function.update_apply, Finset.mem_univ]

/-- A scalar continuous linear functional is determined by its values on
the standard basis, expanded through the corresponding inner-product
coordinate functionals. -/
private lemma continuousLinearMap_eq_sum_innerSL (L : ParamSpace n →L[ℝ] ℝ) :
    L = ∑ i : Fin n, L (EuclideanSpace.single i 1) •
      (innerSL ℝ (EuclideanSpace.single i (1 : ℝ)) : ParamSpace n →L[ℝ] ℝ) := by
  ext w
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, innerSL_apply_apply]
  conv_lhs => rw [paramSpace_eq_sum_single w]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  erw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]
  ring

/-- Small inverse steps along a coordinate line eventually stay in the
open parameter domain. -/
private lemma eventually_single_inv_smul_mem_paramDomain
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (k : Fin n) :
    ∀ᶠ m : ℕ in atTop,
      θ + ((m + 1 : ℝ)⁻¹ • EuclideanSpace.single k (1 : ℝ)) ∈
        M.paramDomain := by
  rw [Filter.eventually_atTop]
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.isOpen_iff.mp M.isOpen_paramDomain θ hθ
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  refine ⟨N, fun m hm => hδ_ball (Metric.mem_ball.mpr ?_)⟩
  simp only [dist_eq_norm, add_sub_cancel_left]
  calc ‖((m + 1 : ℝ)⁻¹ • EuclideanSpace.single k (1 : ℝ) : ParamSpace n)‖
      ≤ (m + 1 : ℝ)⁻¹ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
        calc (m + 1 : ℝ)⁻¹ * ‖(EuclideanSpace.single k (1 : ℝ) : ParamSpace n)‖
            ≤ (m + 1 : ℝ)⁻¹ * 1 := by
              apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
              simp only [PiLp.norm_single, one_mem, CStarRing.norm_of_mem_unitary, le_refl]
          _ = (m + 1 : ℝ)⁻¹ := mul_one _
    _ < δ := by
        have hm_pos : (0 : ℝ) < m + 1 := by positivity
        rw [inv_lt_comm₀ hm_pos hδ_pos]
        calc δ⁻¹ < N := hN
          _ ≤ m := by exact_mod_cast hm
          _ < m + 1 := by linarith

/-! ### Calculus of the KL divergence

`klDiv` is defined at the model level in `StatisticalModel.lean`; here we establish its
diagonal behaviour, the Gibbs inequality, and the Hessian theorem. -/

/-- D(θ ‖ θ) = 0: the divergence vanishes on the diagonal. -/
lemma klDiv_self {θ : ParamSpace n} (_hθ : θ ∈ M.paramDomain) :
    M.klDiv θ θ = 0 := by
  unfold StatisticalModel.klDiv
  have : (fun ω => M.density θ ω * Real.log (M.density θ ω / M.density θ ω)) = 0 := by
    ext ω
    by_cases h : M.density θ ω = 0
    · simp [h]
    · rw [div_self h, Real.log_one, mul_zero]; rfl
  rw [this]
  exact integral_zero' Ω ℝ

/-- Gibbs' inequality, pointwise: for p, q > 0, p - q ≤ p log(p/q). -/
private lemma gibbs_pointwise {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  have hqp_pos : 0 < q / p := div_pos hq hp
  have log_le : Real.log (q / p) ≤ q / p - 1 := by
    have h := Real.add_one_le_exp (Real.log (q / p))
    rw [Real.exp_log hqp_pos] at h
    exact Real.log_le_sub_one_of_pos hqp_pos
  have h1 : p * Real.log (q / p) ≤ q - p := by
    have h := mul_le_mul_of_nonneg_left log_le hp.le
    have : p * (q / p - 1) = q - p := by
      field_simp
    linarith
  have h2 : Real.log (p / q) = -Real.log (q / p) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),
        Real.log_div (ne_of_gt hq) (ne_of_gt hp), neg_sub]
  have h3 : p * Real.log (p / q) = -(p * Real.log (q / p)) := by
    rw [h2]; ring
  linarith

/-- D(θ₁ ‖ θ₂) ≥ 0: Gibbs' inequality / positivity of KL divergence. -/
lemma klDiv_nonneg {θ₁ θ₂ : ParamSpace n}
    (hθ₁ : θ₁ ∈ M.paramDomain) (hθ₂ : θ₂ ∈ M.paramDomain) :
    0 ≤ M.klDiv θ₁ θ₂ := by
  unfold StatisticalModel.klDiv
  by_cases hInt : Integrable (fun ω => M.density θ₁ ω *
      Real.log (M.density θ₁ ω / M.density θ₂ ω)) M.refMeasure
  · have h_int_p := M.toStatisticalModel.integrable hθ₁
    have h_int_q := M.toStatisticalModel.integrable hθ₂
    have h_zero : ∫ ω, (M.density θ₁ ω - M.density θ₂ ω) ∂M.refMeasure = 0 := by
      rw [integral_sub h_int_p h_int_q,
          M.density_integral_one θ₁ hθ₁, M.density_integral_one θ₂ hθ₂, sub_self]
    rw [← h_zero]
    apply integral_mono_ae (h_int_p.sub h_int_q) hInt
    filter_upwards [M.density_pos_ae θ₁ hθ₁, M.density_pos_ae θ₂ hθ₂] with ω hp hq
    exact gibbs_pointwise hp hq
  · simp [integral_undef hInt]

/-- The cross-entropy derivative integrand is a.e. strongly measurable. -/
private lemma crossEntropy_deriv_aestronglyMeasurable
    {θ θ₀ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (hθ₀ : θ₀ ∈ M.paramDomain) :
    AEStronglyMeasurable
      (fun ω => M.density θ ω • fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀)
      M.refMeasure := by
  have h_eq : ∀ᵐ ω ∂M.refMeasure,
      M.density θ ω • fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀ =
      (M.density θ ω * (M.density θ₀ ω)⁻¹) •
        fderiv ℝ (fun θ' => M.density θ' ω) θ₀ := by
    filter_upwards [M.density_pos_ae θ₀ hθ₀] with ω hω
    have h_diff := M.toStatisticalModel.density_differentiableAt hθ₀ ω
    rw [(h_diff.hasFDerivAt.log (ne_of_gt hω)).fderiv]
    ext v; simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    exact Eq.symm (mul_assoc (M.density θ ω) (M.density θ₀ ω)⁻¹
      ((fderiv ℝ (fun θ' => M.density θ' ω) θ₀) v))
  exact AEStronglyMeasurable.congr
    (((M.toStatisticalModel.density_measurable θ hθ).mul
        (M.toStatisticalModel.density_measurable θ₀ hθ₀).inv).aestronglyMeasurable.smul
      (M.toRegularStatisticalModel.fderiv_aestronglyMeasurable hθ₀))
    (h_eq.mono fun ω hω => hω.symm)

/-- Non-existential form: the derivative of the cross-entropy is the
integral of the pointwise derivative. -/
private lemma crossEntropy_hasFDerivAt {θ θ₀ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (hθ₀ : θ₀ ∈ M.paramDomain) :
    HasFDerivAt
      (fun θ' => ∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure)
      (∫ ω, M.density θ ω •
        fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀ ∂M.refMeasure)
      θ₀ := by
  obtain ⟨ε₁, hε₁, bound, hbound_int, h_ae⟩ :=
    M.crossEntropy_fderiv_bound θ hθ θ₀ hθ₀
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.isOpen_iff.mp M.isOpen_paramDomain θ₀ hθ₀
  set ε := min ε₁ ε₂ with _hε_def
  have hε_pos : 0 < ε := lt_min hε₁ hε₂
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball θ₀ ε)
    (F' := fun θ' ω => M.density θ ω •
      fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ')
    (bound := bound)
    (Metric.ball_mem_nhds θ₀ hε_pos)
  · filter_upwards [Metric.ball_mem_nhds θ₀ hε_pos] with θ' hθ'
    have hθ'_mem : θ' ∈ M.paramDomain :=
      hball (Metric.ball_subset_ball (min_le_right ε₁ ε₂) hθ')
    exact (M.crossEntropy_integrable θ hθ θ' hθ'_mem).aestronglyMeasurable
  · exact M.crossEntropy_integrable θ hθ θ₀ hθ₀
  · exact M.crossEntropy_deriv_aestronglyMeasurable hθ hθ₀
  · filter_upwards [h_ae] with ω hω θ' hθ'
    exact (hω θ' (Metric.ball_subset_ball (min_le_left ε₁ ε₂) hθ')).2
  · exact hbound_int
  · filter_upwards [h_ae] with ω hω θ' hθ'
    exact (hω θ' (Metric.ball_subset_ball (min_le_left ε₁ ε₂) hθ')).1

/-- The cross-entropy θ' ↦ -∫ p(ω;θ₀) log p(ω;θ') dμ is differentiable at θ₀. -/
lemma negCrossEntropy_hasFDerivAt {θ θ₀ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (hθ₀ : θ₀ ∈ M.paramDomain) :
    ∃ f' : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => -∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure)
        f' θ₀ :=
  ⟨_, (crossEntropy_hasFDerivAt M hθ hθ₀).neg⟩

/-- The KL divergence θ' ↦ D(θ ‖ θ') is Fréchet differentiable at
any point of the parameter domain. -/
lemma klDiv_hasFDerivAt_self {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) :
    ∃ f' : ParamSpace n →L[ℝ] ℝ, HasFDerivAt (M.klDiv θ) f' θ := by
  have hdecomp : ∀ θ' ∈ M.paramDomain,
    M.klDiv θ θ' =
      ∫ ω, M.density θ ω * Real.log (M.density θ ω) ∂M.refMeasure +
      (-∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure) := by
    intro θ' hθ'
    unfold StatisticalModel.klDiv
    have h_eq : ∀ᵐ ω ∂M.refMeasure,
        M.density θ ω * Real.log (M.density θ ω / M.density θ' ω) =
        M.density θ ω * Real.log (M.density θ ω) -
        M.density θ ω * Real.log (M.density θ' ω) := by
      filter_upwards [M.density_pos_ae θ hθ, M.density_pos_ae θ' hθ'] with ω hp hq
      rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)]; ring
    rw [integral_congr_ae h_eq,
        integral_sub (M.entropy_integrable θ hθ) (M.crossEntropy_integrable θ hθ θ' hθ'),
        sub_eq_add_neg]
  obtain ⟨g, hg⟩ := negCrossEntropy_hasFDerivAt (M := M) hθ hθ
  have h1 : HasFDerivAt
      (fun θ' => ∫ ω, M.density θ ω * Real.log (M.density θ ω) ∂M.refMeasure +
        (-∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure))
      g θ := hg.const_add _
  have hev : (fun θ' => M.klDiv θ θ') =ᶠ[𝓝 θ]
      (fun θ' => ∫ ω, M.density θ ω * Real.log (M.density θ ω) ∂M.refMeasure +
        (-∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure)) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    exact hdecomp θ' hθ'
  exact ⟨g, hev.hasFDerivAt_iff.mpr h1⟩

/-- The first derivative of D(θ ‖ ·) vanishes at the diagonal. -/
lemma klDiv_fderiv_eq_zero {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) :
    HasFDerivAt (M.klDiv θ) (0 : ParamSpace n →L[ℝ] ℝ) θ := by
  have hDiff : ∃ f' : ParamSpace n →L[ℝ] ℝ, HasFDerivAt (M.klDiv θ) f' θ :=
    M.klDiv_hasFDerivAt_self hθ
  obtain ⟨f', hf'⟩ := hDiff
  have hMin : IsLocalMin (M.klDiv θ) θ := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    rw [M.klDiv_self hθ]
    exact M.klDiv_nonneg hθ hθ'
  have h0 : f' = 0 := by
    have hfderiv := IsLocalMin.fderiv_eq_zero hMin
    rwa [hf'.fderiv] at hfderiv
  rwa [h0] at hf'

/-- D(θ ‖ θ') = H(θ) + H×(θ, θ') where H is entropy and H× is neg cross-entropy. -/
lemma klDiv_decomp {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    {θ' : ParamSpace n} (hθ' : θ' ∈ M.paramDomain) :
    M.klDiv θ θ' =
      ∫ ω, M.density θ ω * Real.log (M.density θ ω) ∂M.refMeasure +
      (-∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure) := by
  unfold StatisticalModel.klDiv
  rw [← sub_eq_add_neg,
      ← integral_sub (M.entropy_integrable θ hθ) (M.crossEntropy_integrable θ hθ θ' hθ')]
  apply integral_congr_ae
  filter_upwards [M.density_pos_ae θ hθ, M.density_pos_ae θ' hθ'] with ω hp hq
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq)]; ring

/-- First partial derivative of D(θ ‖ θ') in the second argument. -/
lemma klDiv_partial_j
    {θ θ₀ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (hθ₀ : θ₀ ∈ M.paramDomain)
    (j : Fin n) :
    fderiv ℝ (M.klDiv θ) θ₀ (EuclideanSpace.single j 1) =
      -∫ ω, M.density θ ω *
        M.toRegularStatisticalModel.score θ₀ j ω ∂M.refMeasure := by
  have hCE := crossEntropy_hasFDerivAt (M := M) hθ hθ₀
  have hdecomp : (fun θ' => M.klDiv θ θ') =ᶠ[𝓝 θ₀]
      (fun θ' => ∫ ω, M.density θ ω * Real.log (M.density θ ω) ∂M.refMeasure +
        (-∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure)) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₀] with θ' hθ'
    exact M.klDiv_decomp hθ hθ'
  have hKL : HasFDerivAt (M.klDiv θ)
      (-(∫ ω, M.density θ ω •
        fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀ ∂M.refMeasure))
      θ₀ := by
    have h1 : HasFDerivAt
        (fun θ' => ∫ ω, M.density θ ω * Real.log (M.density θ ω) ∂M.refMeasure +
          (-∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure))
        (-(∫ ω, M.density θ ω •
          fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀ ∂M.refMeasure))
        θ₀ := hCE.neg.const_add _
    exact hdecomp.hasFDerivAt_iff.mpr h1
  rw [hKL.fderiv]
  simp only [ContinuousLinearMap.neg_apply, neg_inj]
  rw [ContinuousLinearMap.integral_apply]
  · apply integral_congr_ae
    filter_upwards [M.density_pos_ae θ₀ hθ₀] with ω hω
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h_ne : M.density θ₀ ω ≠ 0 := ne_of_gt hω
    have h_diff := M.toStatisticalModel.density_differentiableAt hθ₀ ω
    rw [(h_diff.hasFDerivAt.log h_ne).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
    unfold RegularStatisticalModel.score RegularStatisticalModel.partialDensity
    ring
  · obtain ⟨ε₁, hε₁, bound, hbound_int, h_ae⟩ :=
      M.crossEntropy_fderiv_bound θ hθ θ₀ hθ₀
    apply Integrable.mono hbound_int.norm
    · exact M.crossEntropy_deriv_aestronglyMeasurable hθ hθ₀
    · filter_upwards [h_ae] with ω hω
      calc ‖M.density θ ω • fderiv ℝ (fun θ'' => Real.log (M.density θ'' ω)) θ₀‖
          _ ≤ bound ω := (hω θ₀ (Metric.mem_ball_self hε₁)).2
          _ ≤ ‖bound ω‖ := le_abs_self _
      exact Real.le_norm_self ‖bound ω‖

/-- The density-weighted score derivative
ω ↦ p(θ,ω) • ∂ᵢsⱼ(θ,ω) is a.e. strongly measurable. -/
lemma score_deriv_aestronglyMeasurable
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (j : Fin n) :
    AEStronglyMeasurable
      (fun ω => M.density θ ω •
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ)
      M.refMeasure := by
  obtain ⟨ε₁, hε₁_pos, _, _, h_ae⟩ := M.score_fderiv_bound θ hθ θ hθ j
  have h_comp : ∀ k : Fin n,
      AEStronglyMeasurable
        (fun ω => (M.density θ ω •
          fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ)
          (EuclideanSpace.single k 1))
        M.refMeasure := by
    intro k
    have h_eventually : ∀ᶠ m : ℕ in atTop,
        θ + ((m + 1 : ℝ)⁻¹ • EuclideanSpace.single k (1 : ℝ)) ∈ M.paramDomain := by
      exact M.eventually_single_inv_smul_mem_paramDomain hθ k
    obtain ⟨N₀, hN₀⟩ := h_eventually.exists_forall_of_atTop
    set dq : ℕ → Ω → ℝ := fun m ω =>
      (↑(m + 1 + N₀) : ℝ) *
        (M.density θ ω * M.toRegularStatisticalModel.score
          (θ + ((↑(m + 1 + N₀) : ℝ)⁻¹ • EuclideanSpace.single k 1)) j ω -
         M.density θ ω * M.toRegularStatisticalModel.score θ j ω)
    have h_dq_meas : ∀ m, AEStronglyMeasurable (dq m) M.refMeasure := by
      intro m
      have hθ_shift := hN₀ (m + N₀) (by omega)
      have h_dens := (M.toStatisticalModel.density_measurable θ hθ).aestronglyMeasurable
        (μ := M.refMeasure)
      have h_s1 := M.toRegularStatisticalModel.score_aestronglyMeasurable hθ_shift j
      have h_s2 := M.toRegularStatisticalModel.score_aestronglyMeasurable hθ j
      have h_meas := ((h_dens.mul h_s1).sub (h_dens.mul h_s2)).const_mul
        (↑(m + N₀) + 1 : ℝ)
      exact h_meas.congr (by
        filter_upwards with ω
        simp only [dq, Pi.sub_apply, Pi.mul_apply]
        push_cast; ring_nf)
    have h_dq_tendsto : ∀ᵐ ω ∂M.refMeasure,
        Tendsto (fun m => dq m ω) atTop
          (𝓝 ((M.density θ ω •
            fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ)
            (EuclideanSpace.single k 1))) := by
      filter_upwards [h_ae] with ω hω
      set g : ℝ → ℝ := fun t => M.density θ ω *
        M.toRegularStatisticalModel.score
          (θ + t • EuclideanSpace.single k 1) j ω
      set L := (M.density θ ω •
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ)
        (EuclideanSpace.single k 1)
      have h_deriv : HasDerivAt g L 0 := by
        have h_affine : HasDerivAt
            (fun t : ℝ => θ + t • EuclideanSpace.single k (1 : ℝ))
            (EuclideanSpace.single k (1 : ℝ)) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).smul_const
            (EuclideanSpace.single k (1 : ℝ)) |>.const_add θ
        have hfd := (hω θ (Metric.mem_ball_self hε₁_pos)).1
        have h_base : θ + (0 : ℝ) • EuclideanSpace.single k (1 : ℝ) = θ := by simp
        rw [← h_base] at hfd
        convert hfd.comp_hasDerivAt (0 : ℝ) h_affine using 1
        · simp only [zero_smul, add_zero]
          rfl
        · simp only [zero_smul, add_zero, ContinuousLinearMap.coe_smul',
                                            Pi.smul_apply, smul_eq_mul];
          rfl
      suffices h : Tendsto (fun m : ℕ =>
          ((m + 1 + N₀ : ℝ)) * (g ((m + 1 + N₀ : ℝ)⁻¹) - g 0)) atTop (𝓝 L) by
        refine h.congr (fun m => ?_)
        simp only [dq, g, mul_comm]
        push_cast; ring_nf; simp only [zero_smul, add_zero]
      have h_seq_pos : ∀ m : ℕ, (0 : ℝ) < (m + 1 + N₀ : ℝ) := by
        intro m; positivity
      have _h_seq_ne : ∀ m : ℕ, (m + 1 + N₀ : ℝ)⁻¹ ≠ 0 := by
        intro m; exact inv_ne_zero (ne_of_gt (h_seq_pos m))
      have _h_seq_tendsto : Tendsto (fun m : ℕ => (m + 1 + N₀ : ℝ)⁻¹) atTop (𝓝 0) := by
        exact tendsto_inv_atTop_zero.comp
          (Filter.tendsto_atTop_add_const_right _ _ (
            Filter.tendsto_atTop_add_const_right _ _
              tendsto_natCast_atTop_atTop))
      have h_slope_tendsto : Tendsto (fun h : ℝ => (g h - g 0) / h) (𝓝[≠] 0) (𝓝 L) := by
        have := hasDerivAt_iff_tendsto_slope.mp h_deriv
        exact this.congr (fun h => by
          simp only [slope, sub_zero]
          exact inv_mul_eq_div h (g h - g 0))
      suffices h_seq : Tendsto (fun m : ℕ =>
          (g ((m + 1 + N₀ : ℝ)⁻¹) - g 0) / (m + 1 + N₀ : ℝ)⁻¹) atTop (𝓝 L) by
        refine h_seq.congr (fun m => ?_)
        simp only [g]
        rw [div_eq_mul_inv, inv_inv]
        ring
      apply h_slope_tendsto.comp
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h1 : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun m : ℕ => (m : ℝ) + 1 + ↑N₀) atTop atTop := by
          refine (Filter.tendsto_atTop_add_const_right _ ((1 : ℝ) + ↑N₀) h1).congr ?_
          intro m; ring
        have h3 : Tendsto (fun m : ℕ => ((m : ℝ) + 1 + ↑N₀)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp h2
        exact h3
      · filter_upwards with m
        exact inv_ne_zero (by positivity : (m + 1 + N₀ : ℝ) ≠ 0)
    exact aestronglyMeasurable_of_tendsto_ae atTop h_dq_meas h_dq_tendsto
  set v : Ω → EuclideanSpace ℝ (Fin n) := fun ω =>
    (EuclideanSpace.equiv (Fin n) ℝ).symm (fun k =>
      (M.density θ ω •
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ)
        (EuclideanSpace.single k 1))
  have hv : AEStronglyMeasurable v M.refMeasure := by
    have h_eq : ∀ᵐ ω ∂M.refMeasure, v ω = ∑ k : Fin n,
        ((M.density θ ω •
          fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ)
          (EuclideanSpace.single k 1)) •
        EuclideanSpace.single k (1 : ℝ) := by
      filter_upwards with ω
      simp only [v]
      ext i
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
        PiLp.continuousLinearEquiv_symm_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
        PiLp.ofLp_single, sum_apply]
      simp only [Pi.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb;
        simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff, mul_eq_zero]
        grind only
      · intro h; exact absurd (Finset.mem_univ i) h
    exact AEStronglyMeasurable.congr
      (Finset.aestronglyMeasurable_sum Finset.univ fun k _ =>
        (h_comp k).smul_const (EuclideanSpace.single k (1 : ℝ)))
      (h_eq.mono fun ω hω => by
        simp only [Finset.sum_apply] at hω ⊢
        exact hω.symm)
  have h_eq : ∀ᵐ ω ∂M.refMeasure, (M.density θ ω •
      fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ) =
      innerSL ℝ (v ω) := by
    filter_upwards with ω
    apply ContinuousLinearMap.ext
    intro w
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]
    conv_lhs => rw [paramSpace_eq_sum_single w]
    rw [map_sum, Finset.mul_sum]
    simp only [map_smul, smul_eq_mul, ← mul_assoc]
    simp only [PiLp.inner_apply, v,
      PiLp.continuousLinearEquiv_symm_apply]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    congr 1; ext k
    simp only [mul_comm]
    rw [NonUnitalRing.mul_assoc]
    rfl
  exact (innerSL ℝ |>.continuous.comp_aestronglyMeasurable hv).congr
    (h_eq.mono fun ω hω => hω.symm)

/-- Off-diagonal density-weighted score derivative measurability, obtained
from the diagonal version by rescaling with the density ratio
`p(θ,ω) / p(θ₀,ω)`. -/
private lemma weighted_score_deriv_aestronglyMeasurable
    {θ θ₀ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (hθ₀ : θ₀ ∈ M.paramDomain)
    (j : Fin n) :
    AEStronglyMeasurable
      (fun ω => M.density θ ω •
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ₀)
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

/-- The second mixed partial ω ↦ fderiv(θ' ↦ ∂ⱼp(θ',ω))(θ) is a.e. strongly measurable. -/
private lemma fderiv_partialDensity_aestronglyMeasurable
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (j : Fin n) :
    AEStronglyMeasurable
      (fun ω => fderiv ℝ
        (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single j 1)) θ)
      M.refMeasure := by
  have hf_diff : ∀ ω, DifferentiableAt ℝ
      (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
        (EuclideanSpace.single j 1)) θ := by
    intro ω
    have hcda : ContDiffAt ℝ 2 (fun θ' => M.density θ' ω) θ :=
      (M.density_twice_diff ω).contDiffAt (M.isOpen_paramDomain.mem_nhds hθ)
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fun θ' => M.density θ' ω)) θ :=
      hcda.fderiv_right le_rfl
    exact h1.differentiableAt one_ne_zero |>.clm_apply (differentiableAt_const _)
  have h_comp : ∀ k : Fin n,
      AEStronglyMeasurable
        (fun ω => (fderiv ℝ
          (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
            (EuclideanSpace.single j 1)) θ)
          (EuclideanSpace.single k 1))
        M.refMeasure := by
    intro k
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ m ≥ N₀,
        θ + ((m + 1 : ℝ)⁻¹ • EuclideanSpace.single k (1 : ℝ)) ∈
        M.paramDomain := by
      exact (M.eventually_single_inv_smul_mem_paramDomain hθ k).exists_forall_of_atTop
    apply aestronglyMeasurable_of_tendsto_ae (ι := ℕ) atTop
      (f := fun m ω => (↑(m + 1 + N₀) : ℝ) *
        (fderiv ℝ (fun θ'' => M.density θ'' ω)
          (θ + (↑(m + 1 + N₀) : ℝ)⁻¹ • EuclideanSpace.single k 1)
          (EuclideanSpace.single j 1) -
         fderiv ℝ (fun θ'' => M.density θ'' ω) θ
          (EuclideanSpace.single j 1)))
    · intro m
      have hθ' := hN₀ (m + N₀) (by omega)
      have hf_meas : ∀ θ' ∈ M.paramDomain,
          AEStronglyMeasurable
            (fun ω => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
              (EuclideanSpace.single j 1))
            M.refMeasure := by
        intro θ' hθ'
        exact (M.toRegularStatisticalModel.partialDensity_aestronglyMeasurable
          hθ' j).congr (by filter_upwards with ω; rfl)
      exact (((hf_meas _ hθ').sub (hf_meas _ hθ)).const_mul
        (↑(m + 1 + N₀) : ℝ)).congr (by
          filter_upwards with ω; simp only [Pi.sub_apply]; push_cast; ring_nf)
    · filter_upwards with ω
      set g : ℝ → ℝ := fun t =>
        fderiv ℝ (fun θ'' => M.density θ'' ω)
          (θ + t • EuclideanSpace.single k (1 : ℝ))
          (EuclideanSpace.single j 1)
      have hg : HasDerivAt g
          ((fderiv ℝ
            (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
              (EuclideanSpace.single j 1)) θ)
            (EuclideanSpace.single k 1)) 0 := by
        have hfd := (hf_diff ω).hasFDerivAt
        have hline : HasDerivAt (fun t : ℝ => θ + t • EuclideanSpace.single k (1 : ℝ))
            (EuclideanSpace.single k (1 : ℝ)) 0 :=
          by simpa using (hasDerivAt_id (0 : ℝ)).smul_const
              (EuclideanSpace.single k (1 : ℝ)) |>.const_add θ
        have hfd' : HasFDerivAt
            (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
              (EuclideanSpace.single j 1))
            (fderiv ℝ
              (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
                (EuclideanSpace.single j 1)) θ)
            (θ + (0 : ℝ) • EuclideanSpace.single k (1 : ℝ)) := by
          rw [zero_smul, add_zero]; exact hfd
        exact hfd'.comp_hasDerivAt 0 hline
      have h_seq : Tendsto (fun m : ℕ => (↑(m + 1 + N₀) : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          ((Filter.tendsto_atTop_add_const_right _ (1 + ↑N₀ : ℝ)
            tendsto_natCast_atTop_atTop).congr (fun m => by push_cast; ring))
      have h_slope := (hasDerivAt_iff_tendsto_slope.mp hg).comp
        (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          h_seq (by filter_upwards with m; exact inv_ne_zero (by positivity)))
      refine h_slope.congr (fun m => ?_)
      simp only [Function.comp, slope, vsub_eq_sub, sub_zero, g, smul_eq_mul,
                inv_inv, Nat.cast_add, Nat.cast_one, zero_smul, add_zero]
  suffices h_sum : ∀ ω, fderiv ℝ
      (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
        (EuclideanSpace.single j 1)) θ =
      ∑ k : Fin n,
        ((fderiv ℝ
          (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
            (EuclideanSpace.single j 1)) θ)
          (EuclideanSpace.single k 1)) •
        (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)) :
          ParamSpace n →L[ℝ] ℝ) by
    exact (Finset.aestronglyMeasurable_sum Finset.univ (fun k _ =>
      (h_comp k).smul_const _)).congr
      (by filter_upwards with ω; simp only [Finset.sum_apply]; exact (h_sum ω).symm)
  intro ω
  exact continuousLinearMap_eq_sum_innerSL _

/-- The second mixed partial of ∫ p dμ vanishes:
∫ ∂ᵢ∂ⱼp(θ,ω) dμ = 0, since ∂ᵢ∂ⱼ(∫ p dμ) = ∂ᵢ∂ⱼ(1) = 0. -/
lemma integral_second_partial_eq_zero
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (i j : Fin n) :
    ∫ ω, fderiv ℝ (fun θ' =>
      fderiv ℝ (fun θ'' => M.density θ'' ω) θ' (EuclideanSpace.single j 1)) θ
        (EuclideanSpace.single i 1) ∂M.refMeasure = 0 := by
  set f : ParamSpace n → Ω → ℝ := fun θ' ω =>
    fderiv ℝ (fun θ'' => M.density θ'' ω) θ' (EuclideanSpace.single j 1) with _hf_def
  have hG_ev : (fun θ' => ∫ ω, f θ' ω ∂M.refMeasure) =ᶠ[𝓝 θ] 0 := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    have h := M.toRegularStatisticalModel.integral_partialDensity_eq_zero hθ' j
    unfold RegularStatisticalModel.partialDensity at h; exact h
  have hZero : HasFDerivAt (fun θ' => ∫ ω, f θ' ω ∂M.refMeasure)
      (0 : ParamSpace n →L[ℝ] ℝ) θ :=
    (hasFDerivAt_const (0 : ℝ) θ).congr_of_eventuallyEq hG_ev
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp M.isOpen_paramDomain θ hθ
  have hLeibniz : HasFDerivAt (fun θ' => ∫ ω, f θ' ω ∂M.refMeasure)
      (∫ ω, fderiv ℝ (f · ω) θ ∂M.refMeasure) θ := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds θ hε)
    · filter_upwards [Metric.ball_mem_nhds θ hε] with θ' hθ'
      exact (M.toRegularStatisticalModel.partialDensity_aestronglyMeasurable
        (hball hθ') j).congr (by filter_upwards with ω; rfl)
    · exact (M.toRegularStatisticalModel.partialDensity_integrable hθ j).congr
        (by filter_upwards with ω; rfl)
    · exact M.fderiv_partialDensity_aestronglyMeasurable hθ j
    · filter_upwards with ω θ' hθ'
      have hθ'_mem := hball hθ'
      apply ContinuousLinearMap.opNorm_le_bound _ (M.secondDerivBound_nonneg ω)
      intro v
      have hcda : ContDiffAt ℝ 2 (fun θ'' => M.density θ'' ω) θ' :=
        (M.density_twice_diff ω).contDiffAt (M.isOpen_paramDomain.mem_nhds hθ'_mem)
      have h_fderiv_diff : DifferentiableAt ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ' :=
        (hcda.fderiv_right le_rfl).differentiableAt one_ne_zero
      have h_chain : fderiv ℝ (f · ω) θ' v =
          (fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ' v)
            (EuclideanSpace.single j 1) := by
        have := (h_fderiv_diff.hasFDerivAt.clm_apply
          (hasFDerivAt_const (EuclideanSpace.single j 1) θ')).fderiv
        simp only [ContinuousLinearMap.comp_zero, zero_add] at this
        change fderiv ℝ (fun x => (fderiv ℝ (fun θ'' => M.density θ'' ω) x)
          (EuclideanSpace.single j 1)) θ' v = _
        rw [this]; rfl
      rw [h_chain]
      calc ‖(fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ' v)
              (EuclideanSpace.single j 1)‖
          ≤ ‖fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ' v‖ *
            ‖(EuclideanSpace.single j (1 : ℝ) : ParamSpace n)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ' v‖ := by
            rw [PiLp.norm_single];
            simp only [one_mem, CStarRing.norm_of_mem_unitary, mul_one, le_refl]
        _ ≤ ‖fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ'‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖iteratedFDeriv ℝ 2 (fun θ'' => M.density θ'' ω) θ'‖ * ‖v‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]
            simp only [norm_iteratedFDeriv_one, le_refl]
        _ ≤ M.secondDerivBound ω * ‖v‖ :=
            mul_le_mul_of_nonneg_right
              (M.density_fderiv2_norm_le θ' hθ'_mem ω) (norm_nonneg _)
    · exact M.secondDerivBound_integrable
    · filter_upwards with ω θ' hθ'
      have hθ'_mem := hball hθ'
      have hcda : ContDiffAt ℝ 2 (fun θ'' => M.density θ'' ω) θ' :=
        (M.density_twice_diff ω).contDiffAt
          (M.isOpen_paramDomain.mem_nhds hθ'_mem)
      exact (hcda.fderiv_right le_rfl |>.differentiableAt one_ne_zero |>.clm_apply
        (differentiableAt_const _)).hasFDerivAt
  have hEq : (∫ ω, fderiv ℝ (f · ω) θ ∂M.refMeasure) = 0 :=
    hLeibniz.unique hZero
  have hF'_int : Integrable (fun ω => fderiv ℝ (f · ω) θ) M.refMeasure := by
    apply Integrable.mono M.secondDerivBound_integrable.norm
    · exact M.fderiv_partialDensity_aestronglyMeasurable hθ j
    · filter_upwards with ω
      have hcda : ContDiffAt ℝ 2 (fun θ' => M.density θ' ω) θ :=
        (M.density_twice_diff ω).contDiffAt (M.isOpen_paramDomain.mem_nhds hθ)
      have h_fderiv_diff : DifferentiableAt ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ :=
        (hcda.fderiv_right le_rfl).differentiableAt one_ne_zero
      calc ‖fderiv ℝ (f · ω) θ‖
          ≤ M.secondDerivBound ω := by
            apply ContinuousLinearMap.opNorm_le_bound _ (M.secondDerivBound_nonneg ω)
            intro v
            have h_chain : fderiv ℝ (f · ω) θ v =
                (fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ v)
                  (EuclideanSpace.single j 1) := by
              have := (h_fderiv_diff.hasFDerivAt.clm_apply
                (hasFDerivAt_const (EuclideanSpace.single j 1) θ)).fderiv
              simp only [ContinuousLinearMap.comp_zero, zero_add] at this
              change fderiv ℝ (fun x => (fderiv ℝ (fun θ'' => M.density θ'' ω) x)
                (EuclideanSpace.single j 1)) θ v = _
              rw [this]; simp only [ContinuousLinearMap.flip_apply]
            rw [h_chain]
            calc ‖(fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ v)
                    (EuclideanSpace.single j 1)‖
                ≤ ‖fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ v‖ := by
                  calc _ ≤ ‖fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ v‖ *
                        ‖(EuclideanSpace.single j (1 : ℝ) : ParamSpace n)‖ :=
                        ContinuousLinearMap.le_opNorm _ _
                    _ = _ := by rw [PiLp.norm_single]; simp only [one_mem,
                      CStarRing.norm_of_mem_unitary, mul_one]
              _ ≤ ‖fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ‖ * ‖v‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖iteratedFDeriv ℝ 2 (fun θ'' => M.density θ'' ω) θ‖ * ‖v‖ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                  rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]
                  simp only [norm_iteratedFDeriv_one, le_refl]
              _ ≤ M.secondDerivBound ω * ‖v‖ :=
                  mul_le_mul_of_nonneg_right (M.density_fderiv2_norm_le θ hθ ω) (norm_nonneg _)
        _ ≤ ‖M.secondDerivBound ω‖ := Real.le_norm_self (M.secondDerivBound ω)
      exact Real.le_norm_self ‖M.secondDerivBound ω‖
  calc ∫ ω, fderiv ℝ (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
            (EuclideanSpace.single j 1)) θ
          (EuclideanSpace.single i 1) ∂M.refMeasure
      = (∫ ω, fderiv ℝ (f · ω) θ ∂M.refMeasure) (EuclideanSpace.single i 1) := by
          rw [ContinuousLinearMap.integral_apply hF'_int]
    _ = (0 : ParamSpace n →L[ℝ] ℝ) (EuclideanSpace.single i 1) := by rw [hEq]
    _ = 0 := ContinuousLinearMap.zero_apply _

/-- The derivative of the cross-score integral at the diagonal
has eᵢ-component equal to the Fisher information. -/
lemma cross_score_hasFDerivAt
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (j : Fin n) :
    ∃ g₁ : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => -∫ ω, M.density θ ω *
          M.toRegularStatisticalModel.score θ' j ω ∂M.refMeasure)
        g₁ θ ∧
      ∀ i : Fin n,
        g₁ (EuclideanSpace.single i 1) =
          M.toRegularStatisticalModel.fisherMatrix θ i j := by
  set F' : Ω → ParamSpace n →L[ℝ] ℝ :=
    fun ω => M.density θ ω •
      fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ
  have hLeibniz : Integrable F' M.refMeasure ∧
      HasFDerivAt
        (fun θ' => ∫ ω, M.density θ ω *
          M.toRegularStatisticalModel.score θ' j ω ∂M.refMeasure)
        (∫ ω, F' ω ∂M.refMeasure) θ := by
    obtain ⟨ε₁, hε₁, bound, hbound_int, h_ae⟩ := M.score_fderiv_bound θ hθ θ hθ j
    obtain ⟨ε₂, hε₂, hball⟩ := Metric.isOpen_iff.mp M.isOpen_paramDomain θ hθ
    set ε := min ε₁ ε₂
    have hε_pos : 0 < ε := lt_min hε₁ hε₂
    have hF'_meas : AEStronglyMeasurable F' M.refMeasure :=
      M.weighted_score_deriv_aestronglyMeasurable hθ hθ j
    constructor
    · apply Integrable.mono hbound_int.norm
      · exact hF'_meas
      · filter_upwards [h_ae] with ω hω
        calc ‖F' ω‖ = ‖M.density θ ω •
              fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ‖ := rfl
          _ ≤ bound ω := (hω θ (Metric.mem_ball_self hε₁)).2
          _ ≤ ‖bound ω‖ := le_abs_self _
        exact Real.le_norm_self ‖bound ω‖
    · apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (s := Metric.ball θ ε)
        (F' := fun θ' ω => M.density θ ω •
          fderiv ℝ (fun θ'' => M.toRegularStatisticalModel.score θ'' j ω) θ')
        (bound := bound)
        (Metric.ball_mem_nhds θ hε_pos)
      · filter_upwards [Metric.ball_mem_nhds θ hε_pos] with θ' hθ'
        have hθ'_mem := hball (Metric.ball_subset_ball (min_le_right ε₁ ε₂) hθ')
        exact (M.toStatisticalModel.density_measurable θ hθ).aestronglyMeasurable.mul
          (M.toRegularStatisticalModel.score_aestronglyMeasurable hθ'_mem j)
      · refine Integrable.congr
          (M.toRegularStatisticalModel.score_integrable_wrt_density hθ j) ?_
        filter_upwards with ω
        exact mul_comm _ _
      · exact hF'_meas
      · filter_upwards [h_ae] with ω hω θ' hθ'
        exact (hω θ' (Metric.ball_subset_ball (min_le_left ε₁ ε₂) hθ')).2
      · exact hbound_int
      · filter_upwards [h_ae] with ω hω θ' hθ'
        exact (hω θ' (Metric.ball_subset_ball (min_le_left ε₁ ε₂) hθ')).1
  refine ⟨-(∫ ω, F' ω ∂M.refMeasure), hLeibniz.2.neg, ?_⟩
  intro i
  simp only [ContinuousLinearMap.neg_apply]
  rw [ContinuousLinearMap.integral_apply hLeibniz.1]
  rw [neg_eq_iff_eq_neg]
  have h_integrand : ∀ᵐ ω ∂M.refMeasure,
      (F' ω) (EuclideanSpace.single i 1) =
        fderiv ℝ (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single j 1)) θ (EuclideanSpace.single i 1) -
        M.toRegularStatisticalModel.score θ i ω *
        M.toRegularStatisticalModel.score θ j ω *
        M.density θ ω := by
    filter_upwards [M.density_pos_ae θ hθ] with ω hω
    simp only [F', ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h_pos : 0 < M.density θ ω := hω
    have h_ne : M.density θ ω ≠ 0 := ne_of_gt h_pos
    have h_den_diff : DifferentiableAt ℝ (fun θ' => M.density θ' ω) θ :=
      M.toStatisticalModel.density_differentiableAt hθ ω
    have hcda : ContDiffAt ℝ 2 (fun θ' => M.density θ' ω) θ :=
      (M.density_twice_diff ω).contDiffAt (M.isOpen_paramDomain.mem_nhds hθ)
    have h_pd_diff : DifferentiableAt ℝ
        (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single j 1)) θ :=
      (hcda.fderiv_right le_rfl).differentiableAt one_ne_zero |>.clm_apply
        (differentiableAt_const _)
    have h_score_diff : DifferentiableAt ℝ
        (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ := by
      have h_eq : ∀ θ', M.toRegularStatisticalModel.score θ' j ω =
          fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
            (EuclideanSpace.single j 1) * (M.density θ' ω)⁻¹ := by
        intro θ'; rfl
      simp_rw [h_eq]
      exact h_pd_diff.mul (h_den_diff.inv h_ne)
    have h_eq_near : (fun θ' => M.toRegularStatisticalModel.score θ' j ω *
        M.density θ' ω) =ᶠ[𝓝 θ]
        (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single j 1)) := by
      filter_upwards [h_den_diff.continuousAt.eventually
          (isOpen_Ioi.mem_nhds h_pos)] with θ' hθ'
      unfold RegularStatisticalModel.score RegularStatisticalModel.partialDensity
      field_simp
    have h_prod : HasFDerivAt
        (fun θ' => M.toRegularStatisticalModel.score θ' j ω * M.density θ' ω)
        (M.toRegularStatisticalModel.score θ j ω •
          fderiv ℝ (fun θ' => M.density θ' ω) θ +
         M.density θ ω •
          fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ)
        θ :=
      h_score_diff.hasFDerivAt.mul h_den_diff.hasFDerivAt
    have h_key :
        M.toRegularStatisticalModel.score θ j ω •
          fderiv ℝ (fun θ' => M.density θ' ω) θ +
        M.density θ ω •
          fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ =
        fderiv ℝ (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single j 1)) θ := by
      rw [← h_prod.fderiv, h_eq_near.fderiv_eq]
    have h_eval : M.toRegularStatisticalModel.score θ j ω *
        (fderiv ℝ (fun θ' => M.density θ' ω) θ (EuclideanSpace.single i 1)) +
      M.density θ ω *
        (fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' j ω) θ
          (EuclideanSpace.single i 1)) =
      (fderiv ℝ (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single j 1)) θ)
        (EuclideanSpace.single i 1) := by
      have := DFunLike.congr_fun h_key (EuclideanSpace.single i 1)
      simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul] using this
    have h_pd_i : fderiv ℝ (fun θ' => M.density θ' ω) θ
        (EuclideanSpace.single i 1) =
        M.toRegularStatisticalModel.score θ i ω * M.density θ ω := by
      unfold RegularStatisticalModel.score RegularStatisticalModel.partialDensity
      field_simp
    rw [h_pd_i] at h_eval
    have _h_comm : M.toRegularStatisticalModel.score θ j ω *
        (M.toRegularStatisticalModel.score θ i ω * M.density θ ω) =
      M.toRegularStatisticalModel.score θ i ω *
        M.toRegularStatisticalModel.score θ j ω * M.density θ ω := by ring
    linarith
  have h_int_F'_eval : Integrable
      (fun ω => (F' ω) (EuclideanSpace.single i 1)) M.refMeasure :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).integrable_comp
      hLeibniz.1
  have h_int_second : Integrable (fun ω =>
      fderiv ℝ (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
        (EuclideanSpace.single j 1)) θ (EuclideanSpace.single i 1))
      M.refMeasure := by
    apply Integrable.mono M.secondDerivBound_integrable.norm
    · exact (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single i 1)).continuous.comp_aestronglyMeasurable
        (M.fderiv_partialDensity_aestronglyMeasurable hθ j)
    · filter_upwards with ω
      have hcda : ContDiffAt ℝ 2 (fun θ' => M.density θ' ω) θ :=
        (M.density_twice_diff ω).contDiffAt (M.isOpen_paramDomain.mem_nhds hθ)
      have h_fderiv_diff : DifferentiableAt ℝ
          (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ :=
        (hcda.fderiv_right le_rfl).differentiableAt one_ne_zero
      have h_chain : fderiv ℝ (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single j 1)) θ (EuclideanSpace.single i 1) =
          (fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ
            (EuclideanSpace.single i 1))
            (EuclideanSpace.single j 1) := by
        have := (h_fderiv_diff.hasFDerivAt.clm_apply
          (hasFDerivAt_const (EuclideanSpace.single j 1) θ)).fderiv
        simp only [ContinuousLinearMap.comp_zero, zero_add] at this
        change fderiv ℝ (fun x => (fderiv ℝ (fun θ'' => M.density θ'' ω) x)
          (EuclideanSpace.single j 1)) θ (EuclideanSpace.single i 1) = _
        rw [this]; rfl
      rw [h_chain]
      calc ‖(fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ
              (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)‖
          ≤ ‖fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ
              (EuclideanSpace.single i 1)‖ := by
            calc _ ≤ _ * ‖(EuclideanSpace.single j (1 : ℝ) : ParamSpace n)‖ :=
                    ContinuousLinearMap.le_opNorm _ _
              _ = _ := by rw [PiLp.norm_single, norm_one, mul_one]
        _ ≤ ‖fderiv ℝ (fderiv ℝ (fun θ'' => M.density θ'' ω)) θ‖ := by
            calc _ ≤ _ * ‖(EuclideanSpace.single i (1 : ℝ) : ParamSpace n)‖ :=
                    ContinuousLinearMap.le_opNorm _ _
              _ = _ := by rw [PiLp.norm_single, norm_one, mul_one]
        _ ≤ ‖iteratedFDeriv ℝ 2 (fun θ'' => M.density θ'' ω) θ‖ := by
            rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]
            simp only [norm_iteratedFDeriv_one, le_refl]
        _ ≤ M.secondDerivBound ω := M.density_fderiv2_norm_le θ hθ ω
        _ ≤ ‖M.secondDerivBound ω‖ := Real.le_norm_self _
      exact Real.le_norm_self ‖M.secondDerivBound ω‖
  have h_int_score_prod : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ i ω *
      M.toRegularStatisticalModel.score θ j ω *
      M.density θ ω) M.refMeasure :=
    (h_int_second.sub h_int_F'_eval).congr
      (h_integrand.mono fun ω hω => by
        simp_all only [ContinuousLinearMap.coe_smul', Pi.smul_apply,
                      smul_eq_mul, Pi.sub_apply, sub_sub_cancel, F'])
  rw [integral_congr_ae h_integrand]
  rw [integral_sub h_int_second h_int_score_prod]
  rw [M.integral_second_partial_eq_zero hθ i j, zero_sub]
  rfl

/-- Two-point version of cross_score differentiability: density at θ,
derivative at θ₀. Only DifferentiableAt is claimed (component identification
with fisherMatrix only holds at the diagonal). -/
lemma cross_score_differentiableAt
    {θ θ₀ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (hθ₀ : θ₀ ∈ M.paramDomain) (j : Fin n) :
    DifferentiableAt ℝ
      (fun θ' => -∫ ω, M.density θ ω *
        M.toRegularStatisticalModel.score θ' j ω ∂M.refMeasure)
      θ₀ := by
  obtain ⟨ε₁, hε₁, bound₁, hbound₁_int, h_ae₁⟩ :=
    M.score_fderiv_bound θ hθ θ₀ hθ₀ j
  obtain ⟨ε₂, hε₂, hball₂⟩ :=
    Metric.isOpen_iff.mp M.isOpen_paramDomain θ₀ hθ₀
  set ε := min ε₁ ε₂ with _hε_def
  have hε_pos : 0 < ε := lt_min hε₁ hε₂
  have h_base_int : Integrable
      (fun ω => M.density θ ω *
        M.toRegularStatisticalModel.score θ₀ j ω) M.refMeasure := by
    obtain ⟨ε₃, hε₃, bound₃, hbound₃_int, h_ae₃⟩ :=
      M.crossEntropy_fderiv_bound θ hθ θ₀ hθ₀
    apply Integrable.mono hbound₃_int.norm
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
        _ ≤ ‖bound₃ ω‖ := le_abs_self _
      exact Real.le_norm_self ‖bound₃ ω‖
  have h_F'_meas : AEStronglyMeasurable
      (fun ω => M.density θ ω •
        fderiv ℝ (fun θ' =>
          M.toRegularStatisticalModel.score θ' j ω) θ₀)
      M.refMeasure := by
    exact M.weighted_score_deriv_aestronglyMeasurable hθ hθ₀ j
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
  exact hLeibniz.neg.differentiableAt

/-- **The Hessian Theorem.** The second partial derivative of D(θ ‖ θ')
with respect to θ' at the diagonal equals the Fisher information:

  ∂²D(θ ‖ θ')/∂θ'ⁱ∂θ'ʲ |_{θ'=θ} = g_{ij}(θ) -/
lemma klDiv_hessian_eq_fisher {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (i j : Fin n) :
    (∀ f₁ : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt (fun θ' =>
        fderiv ℝ (M.klDiv θ) θ' (EuclideanSpace.single j 1))
        f₁ θ →
      f₁ (EuclideanSpace.single i 1) =
        M.toRegularStatisticalModel.fisherMatrix θ i j) := by
  intro f₁ hf₁
  have heq : (fun θ' =>
      fderiv ℝ (M.klDiv θ) θ' (EuclideanSpace.single j 1)) =ᶠ[𝓝 θ]
      (fun θ' => -∫ ω, M.density θ ω *
        M.toRegularStatisticalModel.score θ' j ω ∂M.refMeasure) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    exact klDiv_partial_j M hθ hθ' j
  obtain ⟨g₁, hg₁, heval⟩ := cross_score_hasFDerivAt M hθ j
  have hg₁' : HasFDerivAt (fun θ' =>
      fderiv ℝ (M.klDiv θ) θ' (EuclideanSpace.single j 1)) g₁ θ :=
    hg₁.congr_of_eventuallyEq heq
  rw [HasFDerivAt.unique hf₁ hg₁']
  exact heval i

/-- **Corollary: Second-order Taylor expansion of KL divergence.**

  D(θ ‖ θ + δ) = ½ ∑ᵢⱼ gᵢⱼ(θ) δⁱδʲ + O(‖δ‖³) -/
lemma klDiv_taylor_second_order {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) :
    ∀ ε > 0, ∃ δ₀ > 0, ∀ δ : ParamSpace n, ‖δ‖ < δ₀ →
      θ + δ ∈ M.paramDomain →
      |M.klDiv θ (θ + δ) -
        (1/2) * ∑ i : Fin n, ∑ j : Fin n,
          δ i * δ j * M.toRegularStatisticalModel.fisherMatrix θ i j| ≤
        ε * ‖δ‖ ^ 2 := by
  intro ε hε
  have hHess : ∀ j : Fin n, ∃ g_j : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => fderiv ℝ (M.klDiv θ) θ' (EuclideanSpace.single j 1))
        g_j θ ∧
      (∀ i : Fin n, g_j (EuclideanSpace.single i 1) =
        M.toRegularStatisticalModel.fisherMatrix θ i j) ∧
      (fderiv ℝ (M.klDiv θ) θ (EuclideanSpace.single j 1) = 0) := by
    intro j
    obtain ⟨g₁, hg₁, heval⟩ := cross_score_hasFDerivAt M hθ j
    refine ⟨g₁, ?_, heval, ?_⟩
    · exact hg₁.congr_of_eventuallyEq (by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
        exact klDiv_partial_j M hθ hθ' j)
    · rw [(klDiv_fderiv_eq_zero M hθ).fderiv]
      exact ContinuousLinearMap.zero_apply _
  set gH : Fin n → ParamSpace n →L[ℝ] ℝ := fun j => (hHess j).choose
  have hgH_fderiv : ∀ j, HasFDerivAt
      (fun θ' => fderiv ℝ (M.klDiv θ) θ' (EuclideanSpace.single j 1))
      (gH j) θ := fun j => (hHess j).choose_spec.1
  have hgH_eval : ∀ j i,
      (gH j) (EuclideanSpace.single i 1) =
        M.toRegularStatisticalModel.fisherMatrix θ i j :=
    fun j i => (hHess j).choose_spec.2.1 i
  have hgH_zero : ∀ j,
      fderiv ℝ (M.klDiv θ) θ (EuclideanSpace.single j 1) = 0 :=
    fun j => (hHess j).choose_spec.2.2
  set η := ε / ((n : ℝ) + 1) with hη_def
  have hη_pos : 0 < η := div_pos hε (by positivity)
  have hj_littleo : ∀ j : Fin n, ∃ ρ > 0, ∀ h : ParamSpace n,
      ‖h‖ < ρ →
      |fderiv ℝ (M.klDiv θ) (θ + h) (EuclideanSpace.single j 1) -
       (gH j) h| ≤ η * ‖h‖ := by
    intro j
    have ho := (hgH_fderiv j).isLittleO
    rw [Asymptotics.isLittleO_iff] at ho
    have hev := ho hη_pos
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ρ, hρ_pos, hball⟩ := hev
    refine ⟨ρ, hρ_pos, fun h hh => ?_⟩
    have := @hball (θ + h) (by rwa [dist_eq_norm, add_sub_cancel_left])
    simp only [add_sub_cancel_left, hgH_zero j, sub_zero] at this
    rwa [Real.norm_eq_abs] at this
  obtain ⟨r_dom, hr_dom_pos, hr_dom⟩ :=
    Metric.isOpen_iff.mp M.isOpen_paramDomain θ hθ
  have hρ_all : ∀ j : Fin n, ∃ ρ > 0, ∀ h : ParamSpace n,
      ‖h‖ < ρ →
      |fderiv ℝ (M.klDiv θ) (θ + h) (EuclideanSpace.single j 1) -
       (gH j) h| ≤ η * ‖h‖ := hj_littleo
  set ρ_min := if h : n = 0 then r_dom else
    Finset.inf' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩)
      (fun j => (hρ_all j).choose)
  set ρ_j : Fin n → ℝ := fun j => (hj_littleo j).choose
  have hρ_j_pos : ∀ j, 0 < ρ_j j := fun j => (hj_littleo j).choose_spec.1
  have hρ_j_spec : ∀ j h, ‖h‖ < ρ_j j →
      |fderiv ℝ (M.klDiv θ) (θ + h) (EuclideanSpace.single j 1) -
       (gH j) h| ≤ η * ‖h‖ :=
    fun j => (hj_littleo j).choose_spec.2
  have h_exists_δ₀ : ∃ δ₀ > 0,
      δ₀ ≤ r_dom ∧ ∀ j : Fin n, δ₀ ≤ ρ_j j := by
    by_cases hn : n = 0
    · exact ⟨r_dom, hr_dom_pos, le_refl _, fun j => (Fin.elim0 (hn ▸ j))⟩
    · have hne : Finset.Nonempty (Finset.univ : Finset (Fin n)) :=
        Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
      set m := Finset.inf' Finset.univ hne ρ_j
      have hm_pos : 0 < m := by
        exact (lt_inf'_iff hne).mpr fun i _a => hρ_j_pos i
      have hm_le : ∀ j : Fin n, m ≤ ρ_j j :=
        fun j => Finset.inf'_le _ (Finset.mem_univ j)
      refine ⟨min m r_dom, lt_min hm_pos hr_dom_pos,
        min_le_right _ _, fun j => le_trans (min_le_left _ _) (hm_le j)⟩
  obtain ⟨δ₀, hδ₀_pos, hδ₀_dom, hδ₀_ρ⟩ := h_exists_δ₀
  refine ⟨δ₀, hδ₀_pos, fun δ hδ _hδ_mem => ?_⟩
  by_cases hδ_zero : δ = 0
  · simp [hδ_zero, klDiv_self M hθ]
  have hn_η : ↑n * η ≤ ε := by
    rw [hη_def, mul_div_assoc']
    rw [div_le_iff₀ (show (0:ℝ) < ↑n + 1 by positivity)]
    grind only
  have h_comp_le : ∀ j : Fin n, |δ j| ≤ ‖δ‖ := by
    intro j
    have h_sq : (δ j) ^ 2 ≤ ‖δ‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq,
          Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      calc (δ j) ^ 2 = ‖δ j‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        _ ≤ ∑ i, ‖δ i‖ ^ 2 :=
            Finset.single_le_sum (f := fun i => ‖δ.ofLp i‖ ^ 2)
              (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    calc |δ j| = √((δ j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √(‖δ‖ ^ 2) := Real.sqrt_le_sqrt h_sq
      _ = ‖δ‖ := Real.sqrt_sq (norm_nonneg _)
  have h_seg_ball : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → θ + t • δ ∈ Metric.ball θ δ₀ := by
    intro t ht0 ht1
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc |t| * ‖δ‖ ≤ 1 * ‖δ‖ :=
          mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, ht1⟩) (norm_nonneg _)
      _ = ‖δ‖ := one_mul _
      _ < δ₀ := hδ
  have h_seg_dom : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → θ + t • δ ∈ M.paramDomain :=
    fun t ht0 ht1 => hr_dom (Metric.ball_subset_ball hδ₀_dom (h_seg_ball t ht0 ht1))
  have hKL_diff : ∀ θ₀ ∈ M.paramDomain, DifferentiableAt ℝ (M.klDiv θ) θ₀ := by
    intro θ₀ hθ₀
    obtain ⟨g, hg⟩ := negCrossEntropy_hasFDerivAt (M := M) hθ hθ₀
    have h1 : HasFDerivAt
        (fun θ' => ∫ ω, M.density θ ω * Real.log (M.density θ ω) ∂M.refMeasure +
          (-∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure))
        g θ₀ := hg.const_add _
    have hev : (M.klDiv θ) =ᶠ[𝓝 θ₀]
        (fun θ' => ∫ ω, M.density θ ω * Real.log (M.density θ ω) ∂M.refMeasure +
          (-∫ ω, M.density θ ω * Real.log (M.density θ' ω) ∂M.refMeasure)) := by
      filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₀] with θ' hθ'
      exact M.klDiv_decomp hθ hθ'
    exact (hev.hasFDerivAt_iff.mpr h1).differentiableAt
  have hKL_fderiv : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      HasFDerivAt (M.klDiv θ) (fderiv ℝ (M.klDiv θ) (θ + t • δ)) (θ + t • δ) :=
    fun t ht0 ht1 => (hKL_diff _ (h_seg_dom t ht0 ht1)).hasFDerivAt
  have hline : ∀ t : ℝ, HasDerivAt (fun s => θ + s • δ) δ t :=
    fun t => by simpa [one_smul] using (hasDerivAt_id t).smul_const δ |>.const_add θ
  have hφ : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      HasDerivAt (fun s => M.klDiv θ (θ + s • δ))
        (fderiv ℝ (M.klDiv θ) (θ + t • δ) δ) t := by
    intro t ht0 ht1
    change HasDerivAt ((M.klDiv θ) ∘ (fun s => θ + s • δ)) _ t
    exact (hKL_fderiv t ht0 ht1).comp_hasDerivAt t (hline t)
  set G := ∑ i : Fin n, ∑ j : Fin n,
    δ i * δ j * M.toRegularStatisticalModel.fisherMatrix θ i j
  have hψ : ∀ t : ℝ, HasDerivAt (fun s => (s ^ 2 / 2) * G) (t * G) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      have := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
      simp only [Nat.cast_ofNat] at this; convert this using 1; ring
    exact h1.mul_const G
  set r : ℝ → ℝ := fun t => M.klDiv θ (θ + t • δ) - (t ^ 2 / 2) * G
  have hr_deriv : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      HasDerivAt r (fderiv ℝ (M.klDiv θ) (θ + t • δ) δ - t * G) t :=
    fun t ht0 ht1 => (hφ t ht0 ht1).sub (hψ t)
  have hr_zero : r 0 = 0 := by simp [r, klDiv_self M hθ]
  have hr_one : r 1 = M.klDiv θ (θ + δ) -
      (1/2) * ∑ i : Fin n, ∑ j : Fin n,
        δ i * δ j * M.toRegularStatisticalModel.fisherMatrix θ i j := by
    simp only [r, G, one_smul]; ring
  have h_dir : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      |fderiv ℝ (M.klDiv θ) (θ + t • δ) δ - t * G| ≤ ↑n * η * ‖δ‖ ^ 2 := by
    intro t ht0 ht1
    have hδ_basis : δ = ∑ k : Fin n, δ k • EuclideanSpace.single k 1 := by
      ext i
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp [Pi.single, Function.update_apply, Finset.mem_univ]
    have h_lin : fderiv ℝ (M.klDiv θ) (θ + t • δ) δ =
        ∑ j, δ j * fderiv ℝ (M.klDiv θ) (θ + t • δ) (EuclideanSpace.single j 1) := by
      calc fderiv ℝ (M.klDiv θ) (θ + t • δ) δ
          = fderiv ℝ (M.klDiv θ) (θ + t • δ)
              (∑ k : Fin n, δ k • EuclideanSpace.single k 1) := by rw [← hδ_basis]
        _ = ∑ j, δ j * fderiv ℝ (M.klDiv θ) (θ + t • δ)
              (EuclideanSpace.single j 1) := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    have h_tG : t * G = ∑ j : Fin n, δ j *
        ∑ i, (t • δ) i * M.toRegularStatisticalModel.fisherMatrix θ i j := by
      simp only [G, Finset.mul_sum, PiLp.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      congr 1; ext j
      congr 1; ext i; ring
    rw [h_lin, h_tG, ← Finset.sum_sub_distrib]
    simp_rw [show ∀ j, δ j * fderiv ℝ (M.klDiv θ) (θ + t • δ) (EuclideanSpace.single j 1) -
        δ j * ∑ i, (t • δ) i * M.toRegularStatisticalModel.fisherMatrix θ i j =
        δ j * (fderiv ℝ (M.klDiv θ) (θ + t • δ) (EuclideanSpace.single j 1) -
          ∑ i, (t • δ) i * M.toRegularStatisticalModel.fisherMatrix θ i j) from
      fun j => by ring]
    have h_tδ_bound : ‖t • δ‖ < δ₀ := by
      rw [norm_smul]
      calc |t| * ‖δ‖ ≤ 1 * ‖δ‖ :=
            mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, ht1⟩) (norm_nonneg _)
        _ = ‖δ‖ := one_mul _
        _ < δ₀ := hδ
    have h_res_bound : ∀ j : Fin n,
        |fderiv ℝ (M.klDiv θ) (θ + t • δ) (EuclideanSpace.single j 1) -
          ∑ i, (t • δ).ofLp i * M.toRegularStatisticalModel.fisherMatrix θ i j| ≤
        η * ‖δ‖ := by
      intro j
      have hgH_sum : (gH j) (t • δ) =
          ∑ i, (t • δ).ofLp i * M.toRegularStatisticalModel.fisherMatrix θ i j := by
        rw [map_smul, smul_eq_mul]
        have hgH_δ : (gH j) δ =
            ∑ i, δ.ofLp i * M.toRegularStatisticalModel.fisherMatrix θ i j := by
          conv_lhs => rw [hδ_basis, map_sum]
          congr 1; ext i; rw [map_smul, smul_eq_mul, hgH_eval j i]
        rw [hgH_δ, Finset.mul_sum]
        congr 1; ext i
        have : (t • δ).ofLp i = t * δ.ofLp i := rfl
        rw [this]; ring
      rw [← hgH_sum]
      calc |fderiv ℝ (M.klDiv θ) (θ + t • δ) (EuclideanSpace.single j 1) -
             (gH j) (t • δ)|
          ≤ η * ‖t • δ‖ :=
            hρ_j_spec j (t • δ) (lt_of_lt_of_le h_tδ_bound (hδ₀_ρ j))
        _ ≤ η * ‖δ‖ := by
            apply mul_le_mul_of_nonneg_left _ hη_pos.le
            rw [norm_smul]
            calc |t| * ‖δ‖ ≤ 1 * ‖δ‖ :=
                  mul_le_mul_of_nonneg_right
                    (abs_le.mpr ⟨by linarith, ht1⟩) (norm_nonneg _)
              _ = ‖δ‖ := one_mul _
    calc |∑ j, δ j * (fderiv ℝ (M.klDiv θ) (θ + t • δ) (EuclideanSpace.single j 1) -
           ∑ i, (t • δ) i * M.toRegularStatisticalModel.fisherMatrix θ i j)|
        ≤ ∑ j, |δ j| * |fderiv ℝ (M.klDiv θ) (θ + t • δ) (EuclideanSpace.single j 1) -
           ∑ i, (t • δ) i * M.toRegularStatisticalModel.fisherMatrix θ i j| := by
          calc _ ≤ ∑ j, |δ j * _| := Finset.abs_sum_le_sum_abs _ _
            _ = _ := by congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ _j : Fin n, ‖δ‖ * (η * ‖δ‖) := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul (h_comp_le j) (h_res_bound j) (abs_nonneg _) (norm_nonneg _)
      _ = ↑n * η * ‖δ‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hmvt : ‖r 1 - r 0‖ ≤ ↑n * η * ‖δ‖ ^ 2 * ‖(1:ℝ) - 0‖ := by
    apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (s := Set.Icc 0 1)
      (f' := fun t => (1 : ℝ →L[ℝ] ℝ).smulRight
        (fderiv ℝ (M.klDiv θ) (θ + t • δ) δ - t * G))
    · intro t ht
      exact (hr_deriv t ht.1 ht.2).hasDerivWithinAt.hasFDerivWithinAt
    · intro t ht
      simp only [ContinuousLinearMap.norm_smulRight_apply,
                  Real.norm_eq_abs]
      simp only [norm_one, one_mul]
      exact h_dir t ht.1 ht.2
    · exact convex_Icc 0 1
    · exact Set.left_mem_Icc.mpr zero_le_one
    · exact Set.right_mem_Icc.mpr zero_le_one
  simp only [hr_zero, sub_zero, sub_zero, norm_one, mul_one, Real.norm_eq_abs] at hmvt
  rw [← hr_one]
  calc |r 1| ≤ ↑n * η * ‖δ‖ ^ 2 := hmvt
    _ ≤ ε * ‖δ‖ ^ 2 := mul_le_mul_of_nonneg_right hn_η (sq_nonneg _)

/-- **Vector form of the Hessian theorem.** At a diagonal point `θ` of the
domain, the second Fréchet derivative of `θ' ↦ D(θ‖θ')` — the canonical
`fderiv` of the operator-valued first-derivative map — evaluates on any
pair of vectors to the Fisher bilinear form:

  `(d² D(θ‖·))(θ)[x, y] = g_θ(x, y)`.

Componentwise this is `klDiv_hessian_eq_fisher`; the vector form follows
by reconstructing the operator-valued differentiability from components
(the `h_fKL` template), identifying each scalar partial's derivative via
`cross_score_hasFDerivAt`, and expanding both slots in the basis. -/
lemma klDiv_hessian_vec {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (x y : ParamSpace n) :
    fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv θ) θ'') θ x y =
    M.toRegularStatisticalModel.fisherBilin θ x y := by
  -- ── The operator-valued first-derivative map is differentiable at θ. ──
  have hG : DifferentiableAt ℝ (fun θ'' => fderiv ℝ (M.klDiv θ) θ'') θ := by
    have h_comp : ∀ j : Fin n, DifferentiableAt ℝ
        (fun θ₀ => fderiv ℝ (M.klDiv θ) θ₀
          (EuclideanSpace.single j 1)) θ := by
      intro j
      have h_cs := M.cross_score_differentiableAt hθ hθ j
      exact h_cs.congr_of_eventuallyEq (by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ₀ hθ₀
        exact (M.klDiv_partial_j hθ hθ₀ j))
    have h_eq : (fun θ₀ => fderiv ℝ (M.klDiv θ) θ₀) =
        (fun θ₀ => ∑ j : Fin n,
          fderiv ℝ (M.klDiv θ) θ₀ (EuclideanSpace.single j 1) •
          (innerSL ℝ (EuclideanSpace.single j (1 : ℝ)) :
            ParamSpace n →L[ℝ] ℝ)) := by
      funext θ₀
      exact continuousLinearMap_eq_sum_innerSL _
    change DifferentiableAt ℝ (fun θ₀ => fderiv ℝ (M.klDiv θ) θ₀) θ
    rw [h_eq]
    refine DifferentiableAt.fun_sum fun j _ => ?_
    haveI : IsScalarTower ℝ ℝ (ParamSpace n →L[ℝ] ℝ) :=
      ⟨fun r s f => by ext x; simp only [ContinuousLinearMap.smul_apply,
        smul_eq_mul, mul_assoc]⟩
    exact (h_comp j).smul_const _
  -- ── Per-component derivative of the scalar partials, at the diagonal. ──
  have hSj : ∀ j : Fin n, ∃ g'ⱼ : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt (fun θ' => fderiv ℝ (M.klDiv θ) θ'
        (EuclideanSpace.single j 1)) g'ⱼ θ ∧
      (∀ i : Fin n, g'ⱼ (EuclideanSpace.single i 1) =
        M.toRegularStatisticalModel.fisherMatrix θ i j) := by
    intro j
    obtain ⟨g'ⱼ, hg'ⱼ, hg'ⱼ_eval⟩ := M.cross_score_hasFDerivAt hθ j
    refine ⟨g'ⱼ, ?_, hg'ⱼ_eval⟩
    exact hg'ⱼ.congr_of_eventuallyEq (by
      filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
      exact (M.klDiv_partial_j hθ hθ' j))
  -- ── Exchange: the operator derivative's components are the gⱼ's. ──
  have hcomp_j : ∀ j : Fin n,
      fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv θ) θ'') θ x
        (EuclideanSpace.single j 1) = (hSj j).choose x := by
    intro j
    have huniq := (hG.hasFDerivAt.clm_apply
      (hasFDerivAt_const
        (EuclideanSpace.single j (1 : ℝ) : ParamSpace n) θ)).unique
      (hSj j).choose_spec.1
    have h := DFunLike.congr_fun huniq x
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
      map_zero, zero_add] using h
  -- ── First slot in the basis: components are rows of the Fisher matrix. ──
  have hx_expand : ∀ j : Fin n,
      fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv θ) θ'') θ x
        (EuclideanSpace.single j 1) =
      ∑ i : Fin n, x.ofLp i *
        M.toRegularStatisticalModel.fisherMatrix θ i j := by
    intro j
    rw [hcomp_j j]
    conv_lhs => rw [paramSpace_eq_sum_single x]
    rw [map_sum]; simp_rw [map_smul, smul_eq_mul, (hSj j).choose_spec.2]
  -- ── Second slot in the basis; close against the Fisher double sum. ──
  conv_lhs => rw [paramSpace_eq_sum_single y]
  rw [map_sum]; simp_rw [map_smul, smul_eq_mul, hx_expand]
  rw [M.toRegularStatisticalModel.fisherBilin_eq_sum_fisherMatrix hθ
    (M.scoreSqIntegrable θ hθ)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext j; ring

end TwiceDifferentiableModel

end Spectra.InformationGeometry

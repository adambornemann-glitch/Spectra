/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Divergence

/-!
# Bartlett Identities

The **Bartlett identities** are the integral identities satisfied by the score
function and its derivatives under a regular statistical model: differentiating the
normalization `∫ p(θ,ω) dμ = 1` repeatedly in `θ` produces a family of vanishing
expectations. This file formalizes the order-2 and order-3 identities, which are the
analytic backbone of the Amari–Chentsov cubic tensor and the third-derivative
decomposition of the KL divergence (see `AmariChentsov.lean`).

## Main statements

* `bartlett_second` — order-2 identity: `∫ (∂ⱼsₖ + sⱼsₖ)·p dμ = 0`, equivalently
  `∫ ∂ⱼ∂ₖp dμ = 0`.
* `bartlett_third` — order-3 identity: the five-term integrand
  `∫ (∂ᵢ∂ⱼsₖ + sⱼ∂ᵢsₖ + sᵢ∂ⱼsₖ + sₖ∂ᵢsⱼ + sᵢsⱼsₖ)·p dμ = 0`, obtained by
  differentiating `bartlett_second`.

## References

* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
-/
open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)

/-- **Bartlett identity of order 2.**
  ∫ (∂ⱼsₖ + sⱼsₖ) · p dμ = 0

Equivalently, ∫ ∂ⱼ∂ₖp dμ = 0.  This is `integral_second_partial_eq_zero`
repackaged through the a.e. identity (∂ⱼsₖ + sⱼsₖ)p = ∂ⱼ∂ₖp. -/
lemma bartlett_second
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (j k : Fin n)
    (_h_int : Integrable (fun ω =>
      (M.scorePartial θ j k ω +
       M.toRegularStatisticalModel.score θ j ω *
       M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω) M.refMeasure) :
    ∫ ω, (M.scorePartial θ j k ω +
      M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω ∂M.refMeasure = 0 := by
  -- ═════════════════════════════════════════════════════════
  -- The integral equals ∫ ∂ⱼ∂ₖp dμ, which is 0 by
  -- integral_second_partial_eq_zero.
  -- ═════════════════════════════════════════════════════════
  -- Step 1: a.e. identity  (∂ⱼsₖ + sⱼsₖ) · p = ∂ⱼ∂ₖp
  --
  -- From ∂ₖp = sₖ · p (partialDensity_eq_score_mul_density_ae):
  --   ∂ⱼ(∂ₖp) = ∂ⱼ(sₖ · p) = (∂ⱼsₖ)·p + sₖ·(∂ⱼp)
  --            = (∂ⱼsₖ)·p + sₖ·sⱼ·p = (∂ⱼsₖ + sⱼsₖ)·p
  have h_ae : ∀ᵐ ω ∂M.refMeasure,
      (M.scorePartial θ j k ω +
       M.toRegularStatisticalModel.score θ j ω *
       M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω =
      fderiv ℝ (fun θ' =>
        fderiv ℝ (fun θ'' => M.density θ'' ω) θ' (EuclideanSpace.single k 1)) θ
          (EuclideanSpace.single j 1) := by
    filter_upwards [M.density_pos_ae θ hθ] with ω hω
    have h_ne : M.density θ ω ≠ 0 := ne_of_gt hω
    have h_den_diff : DifferentiableAt ℝ (fun θ' => M.density θ' ω) θ :=
      M.toStatisticalModel.density_differentiableAt hθ ω
    have hcda : ContDiffAt ℝ 2 (fun θ' => M.density θ' ω) θ :=
      (M.density_twice_diff ω).contDiffAt (M.isOpen_paramDomain.mem_nhds hθ)
    -- The score at θ
    have h_score_diff : DifferentiableAt ℝ
        (fun θ' => M.toRegularStatisticalModel.score θ' k ω) θ := by
      have h_eq : ∀ θ', M.toRegularStatisticalModel.score θ' k ω =
          fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
            (EuclideanSpace.single k 1) * (M.density θ' ω)⁻¹ := by
        intro θ'; rfl
      simp_rw [h_eq]
      exact ((hcda.fderiv_right le_rfl).differentiableAt one_ne_zero |>.clm_apply
        (differentiableAt_const _)).mul (h_den_diff.inv h_ne)
    -- Product rule: ∂ⱼ(sₖ · p) evaluated at eⱼ
    -- sₖ(θ') · p(θ') = partialDensity θ' k ω  (near θ, where p > 0)
    have h_prod_eq : (fun θ' => M.toRegularStatisticalModel.score θ' k ω *
        M.density θ' ω) =ᶠ[𝓝 θ]
        (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single k 1)) := by
      filter_upwards [h_den_diff.continuousAt.eventually
          (isOpen_Ioi.mem_nhds hω)] with θ' hθ'
      unfold RegularStatisticalModel.score RegularStatisticalModel.partialDensity
      field_simp
    -- ∂ⱼ(sₖ · p)(θ)(eⱼ) = ∂ⱼ(∂ₖp)(θ)(eⱼ)
    have h_fderiv_eq :
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' k ω *
          M.density θ' ω) θ =
        fderiv ℝ (fun θ' => fderiv ℝ (fun θ'' => M.density θ'' ω) θ'
          (EuclideanSpace.single k 1)) θ :=
      h_prod_eq.fderiv_eq
    -- Product rule on LHS: ∂ⱼ(sₖ · p) = (∂ⱼsₖ)·p + sₖ·(∂ⱼp) = (∂ⱼsₖ)·p + sₖ·sⱼ·p
    have h_prod_rule :
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' k ω *
          M.density θ' ω) θ (EuclideanSpace.single j 1) =
        M.scorePartial θ j k ω * M.density θ ω +
        M.toRegularStatisticalModel.score θ k ω *
          (fderiv ℝ (fun θ' => M.density θ' ω) θ (EuclideanSpace.single j 1)) := by
      -- Product rule, with explicit type forcing defeq resolution
      have hfd : fderiv ℝ (fun θ' =>
          M.toRegularStatisticalModel.score θ' k ω * M.density θ' ω) θ =
        M.toRegularStatisticalModel.score θ k ω •
          fderiv ℝ (fun θ' => M.density θ' ω) θ +
        M.density θ ω •
          fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' k ω) θ :=
        (h_score_diff.hasFDerivAt.mul h_den_diff.hasFDerivAt).fderiv
      -- Now the annotation matches the goal's function, so congr_fun works
      have := DFunLike.congr_fun hfd (EuclideanSpace.single j 1)
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul] at this
      rw [this]; unfold scorePartial; ring
    -- ∂ⱼp(θ)(eⱼ) = sⱼ · p
    have h_pd_j : fderiv ℝ (fun θ' => M.density θ' ω) θ
        (EuclideanSpace.single j 1) =
        M.toRegularStatisticalModel.score θ j ω * M.density θ ω := by
      unfold RegularStatisticalModel.score RegularStatisticalModel.partialDensity
      field_simp
    -- Combine
    rw [h_pd_j] at h_prod_rule
    have h_lhs : (M.scorePartial θ j k ω +
        M.toRegularStatisticalModel.score θ j ω *
        M.toRegularStatisticalModel.score θ k ω) * M.density θ ω =
        fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' k ω *
          M.density θ' ω) θ (EuclideanSpace.single j 1) := by
      linarith [h_prod_rule]
    rw [h_lhs, ← DFunLike.congr_fun h_fderiv_eq (EuclideanSpace.single j 1)]
  -- Step 2: Rewrite the integral and apply integral_second_partial_eq_zero
  rw [integral_congr_ae h_ae,
      M.integral_second_partial_eq_zero hθ j k]

/-- **Bartlett identity of order 3.**

  ∫ [∂ᵢ∂ⱼsₖ + sⱼ·∂ᵢsₖ + sᵢ·∂ⱼsₖ + sₖ·∂ᵢsⱼ + sᵢsⱼsₖ] · p dμ = 0

Proved by differentiating the Bartlett-2 identity.  The five-term
integrand is ∂ᵢ((∂ⱼsₖ + sⱼsₖ) · p), so its integral is the θᵢ-derivative
of the Bartlett-2 integral, which is identically zero. -/
lemma bartlett_third
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (i j k : Fin n)
    /- Integrability of the five-term integrand. -/
    (_h_int : Integrable (fun ω =>
      (fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
          (EuclideanSpace.single i 1) +
       M.toRegularStatisticalModel.score θ j ω * M.scorePartial θ i k ω +
       M.toRegularStatisticalModel.score θ i ω * M.scorePartial θ j k ω +
       M.toRegularStatisticalModel.score θ k ω * M.scorePartial θ i j ω +
       M.toRegularStatisticalModel.score θ i ω *
         M.toRegularStatisticalModel.score θ j ω *
         M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω) M.refMeasure)
    /- Bartlett-2 holds throughout paramDomain (from bartlett_second). -/
    (h_bartlett2 : ∀ θ' ∈ M.paramDomain,
      ∫ ω, (M.scorePartial θ' j k ω +
        M.toRegularStatisticalModel.score θ' j ω *
        M.toRegularStatisticalModel.score θ' k ω) *
        M.density θ' ω ∂M.refMeasure = 0)
    /- Leibniz interchange: the Bartlett-2 integral is Fréchet differentiable,
       with eᵢ-component of the derivative equal to the five-term integral.
       This is the analytic hypothesis — justified by the same domination
       machinery as klDiv_third_partial (Lemma A). -/
    (h_hasFDerivAt : ∃ L : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => ∫ ω, (M.scorePartial θ' j k ω +
          M.toRegularStatisticalModel.score θ' j ω *
          M.toRegularStatisticalModel.score θ' k ω) *
          M.density θ' ω ∂M.refMeasure) L θ ∧
      L (EuclideanSpace.single i 1) =
        ∫ ω, (fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
              (EuclideanSpace.single i 1) +
           M.toRegularStatisticalModel.score θ j ω * M.scorePartial θ i k ω +
           M.toRegularStatisticalModel.score θ i ω * M.scorePartial θ j k ω +
           M.toRegularStatisticalModel.score θ k ω * M.scorePartial θ i j ω +
           M.toRegularStatisticalModel.score θ i ω *
             M.toRegularStatisticalModel.score θ j ω *
             M.toRegularStatisticalModel.score θ k ω) *
          M.density θ ω ∂M.refMeasure) :
    ∫ ω,
      (fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
          (EuclideanSpace.single i 1) +
       M.toRegularStatisticalModel.score θ j ω * M.scorePartial θ i k ω +
       M.toRegularStatisticalModel.score θ i ω * M.scorePartial θ j k ω +
       M.toRegularStatisticalModel.score θ k ω * M.scorePartial θ i j ω +
       M.toRegularStatisticalModel.score θ i ω *
         M.toRegularStatisticalModel.score θ j ω *
         M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω ∂M.refMeasure = 0 := by
  -- ═══════════════════════════════════════════════════════════════
  -- Step 1: The Bartlett-2 integral is locally zero on paramDomain.
  -- ═══════════════════════════════════════════════════════════════
  set F : ParamSpace n → ℝ := fun θ' =>
    ∫ ω, (M.scorePartial θ' j k ω +
      M.toRegularStatisticalModel.score θ' j ω *
      M.toRegularStatisticalModel.score θ' k ω) *
      M.density θ' ω ∂M.refMeasure with _hF_def
  have hF_locally_zero : F =ᶠ[𝓝 θ] 0 := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    exact h_bartlett2 θ' hθ'
  -- ═══════════════════════════════════════════════════════════════
  -- Step 2: Therefore HasFDerivAt F 0 θ.
  -- ═══════════════════════════════════════════════════════════════
  have hF_zero : HasFDerivAt F (0 : ParamSpace n →L[ℝ] ℝ) θ :=
    (hasFDerivAt_const (0 : ℝ) θ).congr_of_eventuallyEq hF_locally_zero
  -- ═══════════════════════════════════════════════════════════════
  -- Step 3: Extract the Leibniz derivative and its evaluation.
  -- ═══════════════════════════════════════════════════════════════
  obtain ⟨L, hL_fderiv, hL_eval⟩ := h_hasFDerivAt
  -- ═══════════════════════════════════════════════════════════════
  -- Step 4: Uniqueness of Fréchet derivatives ⟹ L = 0.
  -- ═══════════════════════════════════════════════════════════════
  have hL_zero : L = 0 := hL_fderiv.unique hF_zero
  -- ═══════════════════════════════════════════════════════════════
  -- Step 5: The five-term integral = L(eᵢ) = 0(eᵢ) = 0.
  -- ═══════════════════════════════════════════════════════════════
  rw [← hL_eval, hL_zero, ContinuousLinearMap.zero_apply]


end TwiceDifferentiableModel
end Spectra.InformationGeometry

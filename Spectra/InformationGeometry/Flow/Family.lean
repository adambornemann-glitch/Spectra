/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Connection.AmariChentsov
import Spectra.InformationGeometry.Connection.Basic
import Spectra.InformationGeometry.Divergence

/-!
# Divergence-Preserving Families

The information-geometric analogue of a one-parameter unitary group: a smooth family
`φ_t : Θ → Θ` that preserves the KL divergence between every pair of points. This file defines
the family, its second derivative, and the m-connection trilinear form, and shows that
divergence preservation already forces preservation of the Fisher metric.

## Main definitions

* `DivergencePreservingFamily` — a divergence-preserving one-parameter family `φ_t`.
* `mConnectionTrilin` — the m-connection as a trilinear form.
* `secondDerivPhi` — the second derivative `d²φ_t` of the family.

## Main statements

* `preserves_fisher` — a divergence-preserving family preserves the Fisher metric.
* `mConnectionTrilin_single` — the trilinear form on a basis triple recovers `Γᵐ_{ab,c}`.

## References

* S. Amari, H. Nagaoka, *Methods of Information Geometry*, AMS, 2000.
-/
open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)


-- ============================================================================
-- §4. Divergence-Preserving One-Parameter Families
-- ============================================================================

/-! ### The dynamic structure

A divergence-preserving one-parameter family is the information-geometric
analogue of Stone's `OneParameterUnitaryGroup`.

| Stone / Hilbert Space         | Amari / Statistical Manifold         |
|-------------------------------|--------------------------------------|
| `U(t) : H → H`                | `φ_t : Θ → Θ`                        |
| `⟨U(t)ψ, U(t)φ⟩ = ⟨ψ,φ⟩`      | `D(φ_t(θ₁) ‖ φ_t(θ₂)) = D(θ₁‖θ₂)`.   |
| `U(s+t) = U(s)∘U(t)`          | `φ_{s+t} = φ_s ∘ φ_t`                |
| `U(0) = id`                   | `φ_0 = id`                           |
| strong continuity             | smooth dependence on t               |
| generator: self-adjoint A     | generator: Killing + C-preserving X  |
| `U(t) = e^{itA}`              | `φ_t = Fl^X_t`                       |

The **information-geometric Stone's theorem** will assert a bijection
between such families and their generators, under completeness. -/

/-- A **divergence-preserving one-parameter family** on a statistical model.

This is the central dynamical structure. The five axioms mirror
Stone's `OneParameterUnitaryGroup` with the inner product replaced
by the KL divergence. -/
structure DivergencePreservingFamily where
  /-- The one-parameter family of maps on the parameter space. -/
  φ : ℝ → ParamSpace n → ParamSpace n
  /-- The maps preserve the parameter domain. -/
  maps_domain : ∀ t, ∀ θ ∈ M.paramDomain, φ t θ ∈ M.paramDomain
  /-- **Divergence preservation**: D(φ_t(θ₁) ‖ φ_t(θ₂)) = D(θ₁ ‖ θ₂).
  This is the analogue of unitarity ⟨U(t)ψ, U(t)φ⟩ = ⟨ψ,φ⟩. -/
  preserves_divergence : ∀ t, ∀ θ₁ ∈ M.paramDomain, ∀ θ₂ ∈ M.paramDomain,
    M.klDiv (φ t θ₁) (φ t θ₂) = M.klDiv θ₁ θ₂
  /-- **Group law**: φ_{s+t} = φ_s ∘ φ_t. -/
  group_law : ∀ s t θ, φ (s + t) θ = φ s (φ t θ)
  /-- **Identity**: φ_0 = id. -/
  identity : ∀ θ, φ 0 θ = θ
  /-- **Smoothness**: φ is jointly smooth in (t, θ).
  This is the analogue of strong continuity. In the finite-dimensional
  statistical setting, smoothness is the natural regularity — it is
  stronger than Stone's strong continuity, but the statistical manifold
  is finite-dimensional so this is not restrictive. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ)


/-- The m-connection as a trilinear form:
  Γᵐ(θ)(u, v, w) = ∑_{a,b,c} u_a · v_b · w_c · Γᵐ_{ab,c}(θ)

The first two slots (u,v) correspond to (differentiation direction,
score being differentiated); the third slot (w) is the covariant index.
NOT totally symmetric — contrast with `cubicTrilin`. -/
noncomputable def mConnectionTrilin
    (θ : ParamSpace n) (u v w : ParamSpace n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
    u a * v b * w c * M.mConnectionCoeff θ a b c

/-- Evaluating the m-connection trilinear form on the coordinate basis triple
`(eₐ, e_b, e_c)` recovers the coefficient `Γᵐ_{ab,c}(θ)`. -/
lemma mConnectionTrilin_single (θ : ParamSpace n) (a b c : Fin n) :
    M.mConnectionTrilin θ
      (EuclideanSpace.single a 1)
      (EuclideanSpace.single b 1)
      (EuclideanSpace.single c 1) =
    M.mConnectionCoeff θ a b c := by
  unfold mConnectionTrilin
  -- Same pattern as bilinSum_single but for triple sum
  simp only [PiLp.single_apply]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_irrel,
    sum_ite_eq', mem_univ, ↓reduceIte, sum_const_zero]

/-- A vector in `ParamSpace n` is the finite sum of its coordinate components in the
standard basis. -/
private lemma paramSpace_eq_sum_single (u : ParamSpace n) :
    u = ∑ a : Fin n, u a • EuclideanSpace.single a 1 := by
  ext i
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, sum_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ↓reduceIte]

/-- The operator norm of a scalar continuous linear map on `ParamSpace n` is bounded by
the sum of the norms of its standard-basis values. -/
private lemma continuousLinearMap_opNorm_le_sum_single
    (L : ParamSpace n →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ j : Fin n, ‖L (EuclideanSpace.single j 1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  conv_lhs => rw [paramSpace_eq_sum_single v]
  rw [map_sum]
  simp_rw [map_smul]
  calc ‖∑ j, v j • L (EuclideanSpace.single j 1)‖
      ≤ ∑ j, ‖v j • L (EuclideanSpace.single j 1)‖ := norm_sum_le _ _
    _ = ∑ j, |v j| * ‖L (EuclideanSpace.single j 1)‖ := by
        simp_rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j, ‖v‖ * ‖L (EuclideanSpace.single j 1)‖ := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
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
    _ = (∑ j, ‖L (EuclideanSpace.single j 1)‖) * ‖v‖ := by
        rw [Finset.sum_mul]
        ring_nf

/-- The KL divergence `D(α‖·)` is differentiable at every point of the parameter domain. -/
private lemma klDiv_differentiableAt
    {α θ₀ : ParamSpace n} (hα : α ∈ M.paramDomain) (hθ₀ : θ₀ ∈ M.paramDomain) :
    DifferentiableAt ℝ (M.klDiv α) θ₀ := by
  obtain ⟨g, hg⟩ := negCrossEntropy_hasFDerivAt (M := M) hα hθ₀
  have h1 : HasFDerivAt
      (fun θ' => ∫ ω, M.density α ω * Real.log (M.density α ω) ∂M.refMeasure +
        (-∫ ω, M.density α ω * Real.log (M.density θ' ω) ∂M.refMeasure))
      g θ₀ := hg.const_add _
  have hev : (M.klDiv α) =ᶠ[𝓝 θ₀]
      (fun θ' => ∫ ω, M.density α ω * Real.log (M.density α ω) ∂M.refMeasure +
        (-∫ ω, M.density α ω * Real.log (M.density θ' ω) ∂M.refMeasure)) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₀] with θ' hθ'
    exact M.klDiv_decomp hα hθ'
  exact (hev.hasFDerivAt_iff.mpr h1).differentiableAt

/-- The coordinate partial of `D(θ‖·)` is differentiable at the diagonal point `θ`. -/
private lemma klDiv_partial_differentiableAt_self
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (j : Fin n) :
    DifferentiableAt ℝ
      (fun θ' => fderiv ℝ (M.klDiv θ) θ' (EuclideanSpace.single j 1)) θ := by
  obtain ⟨g₁, hg₁, _⟩ := M.cross_score_hasFDerivAt hθ j
  exact (hg₁.congr_of_eventuallyEq (by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    exact M.klDiv_partial_j hθ hθ' j)).differentiableAt


namespace DivergencePreservingFamily

variable {M : TwiceDifferentiableModel n Ω}
variable (F : M.DivergencePreservingFamily)

-- ============================================================================
-- §4a. Consequences of divergence preservation
-- ============================================================================

/-- **Derivative of the moving first variation against a moving vector.**

With `α := φ_t θ`, for any vector field `V` differentiable at `θ`, the scalar map
`θ₁ ↦ (d D(α‖·))(φ_t θ₁) (V θ₁)` is differentiable at `θ`, and its `a`-th
partial is `g_α(dφ_t(θ)(eₐ), V θ)`.

This is the frozen-vector computation used by `preserves_fisher`; the motion of `V`
contributes only a little-o term because `fderiv (klDiv α)` vanishes at `α`. -/
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
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) (F.φ t) :=
    F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hφ_diff_at : ∀ θ₂, DifferentiableAt ℝ (F.φ t) θ₂ :=
    fun θ₂ => (hφ_smooth.differentiable (by simp)).differentiableAt
  have hKL_zero : fderiv ℝ (M.klDiv α) α = 0 :=
    (M.klDiv_fderiv_eq_zero hα).fderiv
  set v₀ := V θ with _hv₀_def
  set G : ParamSpace n → ℝ := fun θ₂ =>
    fderiv ℝ (M.klDiv α) (F.φ t θ₂) (V θ₂) with hG_def
  set R : ParamSpace n → ℝ := fun θ₂ =>
    fderiv ℝ (M.klDiv α) (F.φ t θ₂) v₀ with hR_def
  have hφtθ_eq_α : F.φ t θ = α := hα_def.symm
  have hG_zero : G θ = 0 := by
    simp only [hG_def, hφtθ_eq_α, hKL_zero, ContinuousLinearMap.zero_apply]
  have hR_zero : R θ = 0 := by
    simp only [hR_def, hφtθ_eq_α, hKL_zero, ContinuousLinearMap.zero_apply]
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
      exact M.klDiv_partial_j hα hθ' j)
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
    · convert hg'ⱼ_α.comp θ (hφ_diff_at θ).hasFDerivAt using 1
    · intro i
      rw [ContinuousLinearMap.comp_apply]
      set w := fderiv ℝ (F.φ t) θ (EuclideanSpace.single i 1)
      conv_lhs => rw [show w = ∑ k : Fin n, w.ofLp k •
          EuclideanSpace.single k 1 from paramSpace_eq_sum_single w]
      rw [map_sum]
      simp_rw [map_smul, smul_eq_mul, hg'ⱼ_eval]
  have hR_eq : ∀ θ₂, R θ₂ = ∑ j : Fin n, v₀.ofLp j *
      fderiv ℝ (M.klDiv α) (F.φ t θ₂) (EuclideanSpace.single j 1) := by
    intro θ₂
    simp only [hR_def]
    conv_lhs => rw [show v₀ = ∑ j : Fin n, v₀.ofLp j •
        EuclideanSpace.single j 1 from paramSpace_eq_sum_single v₀]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
  set fR : ParamSpace n →L[ℝ] ℝ :=
    ∑ j : Fin n, v₀.ofLp j • (hSj_comp j).choose with hfR_def
  have hR_fderiv : HasFDerivAt R fR θ := by
    have hR_sum : R =ᶠ[𝓝 θ] (fun θ₂ => ∑ j : Fin n, v₀.ofLp j *
        fderiv ℝ (M.klDiv α) (F.φ t θ₂) (EuclideanSpace.single j 1)) := by
      filter_upwards with θ₂
      exact hR_eq θ₂
    apply HasFDerivAt.congr_of_eventuallyEq _ hR_sum
    apply HasFDerivAt.fun_sum
    intro j _
    exact ((hSj_comp j).choose_spec.1).const_mul (v₀.ofLp j)
  have hGR_eq : ∀ θ₂, G θ₂ - R θ₂ =
      fderiv ℝ (M.klDiv α) (F.φ t θ₂) (V θ₂ - v₀) := by
    intro θ₂
    simp only [hG_def, hR_def, ← map_sub]
  have h_factor1 : Tendsto
      (fun θ₂ => ‖fderiv ℝ (M.klDiv α) (F.φ t θ₂)‖) (𝓝 θ) (𝓝 0) := by
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
      have h_cont : ContinuousAt (fun θ' => fderiv ℝ (M.klDiv α) θ'
          (EuclideanSpace.single j 1)) α :=
        hg_j.continuousAt.congr h_ev.symm
      have h_val : fderiv ℝ (M.klDiv α) α (EuclideanSpace.single j 1) = 0 := by
        rw [hKL_zero]
        exact ContinuousLinearMap.zero_apply _
      rw [← h_val]
      exact h_cont.tendsto.comp
        (hφtθ_eq_α ▸ hφ_smooth.continuous.continuousAt.tendsto)
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun θ₂ => continuousLinearMap_opNorm_le_sum_single
        (fderiv ℝ (M.klDiv α) (F.φ t θ₂)))
    have := tendsto_finsetSum Finset.univ (fun j _ => (h_comp j).norm)
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
          · exact hest
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
  have hG_fderiv : HasFDerivAt G fR θ := by
    have h1 := hR_fderiv.isLittleO.add hGR_littleo
    have h2 : (fun θ₂ => (R θ₂ - R θ - fR (θ₂ - θ)) + (G θ₂ - R θ₂)) =
        (fun θ₂ => G θ₂ - G θ - fR (θ₂ - θ)) := by
      ext θ₂
      rw [hR_zero, hG_zero]
      ring
    rw [h2] at h1
    exact hasFDerivAt_iff_isLittleO.mpr h1
  rw [show fderiv ℝ G θ = fR from hG_fderiv.fderiv]
  simp only [hfR_def, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  conv_lhs =>
    arg 2
    ext j
    rw [(hSj_comp j).choose_spec.2 a]
  rw [M.toRegularStatisticalModel.fisherBilin_eq_sum_fisherMatrix hα
    (M.scoreSqIntegrable α hα)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext k
  congr 1
  ext j
  ring

/-- **Divergence preservation implies Fisher metric preservation**

If D(φ_t(θ₁) ‖ φ_t(θ₂)) = D(θ₁ ‖ θ₂), then differentiating twice
in the second argument at θ₂ = θ₁ and using the Hessian theorem:

  g_{ij}(φ_t(θ)) · ∂φ_t^a/∂θⁱ · ∂φ_t^b/∂θʲ = g_{ab}(θ)

i.e., φ_t is a Riemannian isometry of the Fisher metric -/
lemma preserves_fisher {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (t : ℝ) (v w : ParamSpace n) :
    M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ v) (fderiv ℝ (F.φ t) θ w) =
    M.toRegularStatisticalModel.fisherBilin θ v w := by
  set α := F.φ t θ with _hα_def
  have hα : α ∈ M.paramDomain := F.maps_domain t θ hθ
  suffices h_component : ∀ a b : Fin n,
      M.toRegularStatisticalModel.fisherBilin α
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) =
      M.toRegularStatisticalModel.fisherMatrix θ a b by
    have hSq_θ : M.toRegularStatisticalModel.ScoreSqIntegrableModel θ :=
      M.scoreSqIntegrable θ hθ
    have hSq_α : M.toRegularStatisticalModel.ScoreSqIntegrableModel α :=
      M.scoreSqIntegrable α hα
    rw [← M.toRegularStatisticalModel.fisherBilinForm_apply hα hSq_α,
        ← M.toRegularStatisticalModel.fisherBilinForm_apply hθ hSq_θ]
    have hdφ : ∀ u : ParamSpace n,
        fderiv ℝ (F.φ t) θ u =
        ∑ a : Fin n, u a • fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1) := by
      intro u
      conv_lhs => rw [paramSpace_eq_sum_single u, map_sum]
      simp only [map_smul]
    -- ── Reduce first argument to basis ──
    rw [hdφ v]; conv_rhs => rw [paramSpace_eq_sum_single v]
    simp only [map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    congr 1; ext a; congr 1
    -- ── Reduce second argument to basis ──
    rw [hdφ w]; conv_rhs => rw [paramSpace_eq_sum_single w]
    simp only [map_sum, map_smul, smul_eq_mul]
    congr 1; ext b; congr 1
    -- ── On basis pairs, appeal to h_component ──
    rw [M.toRegularStatisticalModel.fisherBilinForm_apply,
        M.toRegularStatisticalModel.fisherBilinForm_apply,
        M.toRegularStatisticalModel.fisherBilin_single]
    exact h_component a b
  -- ════════ Proof of the componentwise identity ════════
  intro a b
  -- ── Step 1: The two KL functions agree on an open neighborhood ──
  have h_funcs_eq : ∀ θ₂ ∈ M.paramDomain,
      M.klDiv α (F.φ t θ₂) = M.klDiv θ θ₂ :=
    fun θ₂ hθ₂ => F.preserves_divergence t θ hθ θ₂ hθ₂
  have _h_ev_eq : (fun θ₂ => M.klDiv α (F.φ t θ₂)) =ᶠ[𝓝 θ] M.klDiv θ := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ₂ hθ₂
    exact h_funcs_eq θ₂ hθ₂
  -- ── Step 2: Their fderivs agree on an open neighborhood ──
  have h_fderiv_ev : ∀ᶠ θ₂ in 𝓝 θ,
      fderiv ℝ (fun θ₂' => M.klDiv α (F.φ t θ₂')) θ₂ =
      fderiv ℝ (M.klDiv θ) θ₂ := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ₂ hθ₂
    exact Filter.EventuallyEq.fderiv_eq
      (by filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₂] with θ₃ hθ₃
          exact h_funcs_eq θ₃ hθ₃)
  -- ── Step 3: The b-th partials agree near θ ──
  have h_partial_ev : (fun θ₂ =>
      fderiv ℝ (fun θ₂' => M.klDiv α (F.φ t θ₂')) θ₂
        (EuclideanSpace.single b 1)) =ᶠ[𝓝 θ]
      (fun θ₂ => fderiv ℝ (M.klDiv θ) θ₂
        (EuclideanSpace.single b 1)) := by
    filter_upwards [h_fderiv_ev] with θ₂ hθ₂
    rw [hθ₂]
  -- ── Step 4: Second derivatives agree at θ ──
  have h_second_eq :
      fderiv ℝ (fun θ₂ => fderiv ℝ (fun θ₂' => M.klDiv α (F.φ t θ₂')) θ₂
        (EuclideanSpace.single b 1)) θ (EuclideanSpace.single a 1) =
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv θ) θ₂
        (EuclideanSpace.single b 1)) θ (EuclideanSpace.single a 1) := by
    exact DFunLike.congr_fun (h_partial_ev.fderiv_eq (𝕜 := ℝ)) (EuclideanSpace.single a 1)
  -- ── Step 5: RHS = g_{ab}(θ) by the Hessian theorem ──
  have h_RHS : fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv θ) θ₂
      (EuclideanSpace.single b 1)) θ (EuclideanSpace.single a 1) =
      M.toRegularStatisticalModel.fisherMatrix θ a b := by
    have hHess := M.klDiv_hessian_eq_fisher hθ a b
    have h_diff : DifferentiableAt ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single b 1)) θ := by
      exact M.klDiv_partial_differentiableAt_self hθ b
    exact hHess _ h_diff.hasFDerivAt
  -- ── Step 6: LHS = fisherBilin(α)(dφ·eₐ, dφ·e_b) ──
  have h_LHS : fderiv ℝ (fun θ₂ =>
        fderiv ℝ (fun θ₂' => M.klDiv α (F.φ t θ₂')) θ₂
          (EuclideanSpace.single b 1)) θ (EuclideanSpace.single a 1) =
        M.toRegularStatisticalModel.fisherBilin α
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) := by
      -- Key differentiability facts
      have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) (F.φ t) :=
        F.smooth.comp (contDiff_const.prodMk contDiff_id)
      have hφ_diff_at : ∀ θ₂, DifferentiableAt ℝ (F.φ t) θ₂ :=
        fun θ₂ => (hφ_smooth.differentiable (by simp)).differentiableAt
      have _hKL_zero : fderiv ℝ (M.klDiv α) α = 0 :=
        (M.klDiv_fderiv_eq_zero hα).fderiv
      -- Step 1: Chain rule — near θ, the b-th partial factors
      have h_chain_ev : ∀ᶠ θ₂ in 𝓝 θ,
          fderiv ℝ (fun θ₂' => M.klDiv α (F.φ t θ₂')) θ₂
            (EuclideanSpace.single b 1) =
          fderiv ℝ (M.klDiv α) (F.φ t θ₂)
            (fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single b 1)) := by
        filter_upwards [hφ_smooth.continuous.continuousAt.preimage_mem_nhds
          (M.isOpen_paramDomain.mem_nhds hα)] with θ₂ hθ₂
        change fderiv ℝ (M.klDiv α ∘ F.φ t) θ₂ (EuclideanSpace.single b 1) = _
        have hcomp := ((M.klDiv_differentiableAt hα hθ₂).hasFDerivAt.comp θ₂
          (hφ_diff_at θ₂).hasFDerivAt).fderiv
        rw [hcomp, ContinuousLinearMap.comp_apply]
      -- Step 2: Transfer the fderiv via eventuallyEq
      have h_fderiv_eq : fderiv ℝ
          (fun θ₂ => fderiv ℝ (fun θ₂' => M.klDiv α (F.φ t θ₂')) θ₂
            (EuclideanSpace.single b 1)) θ =
          fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)
            (fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single b 1))) θ :=
        Filter.EventuallyEq.fderiv_eq h_chain_ev
      rw [DFunLike.congr_fun h_fderiv_eq (EuclideanSpace.single a 1)]
      have hV : DifferentiableAt ℝ
          (fun θ₂ => fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single b 1)) θ := by
        exact ((hφ_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by exact_mod_cast le_top)).differentiable (by simp)
          ).differentiableAt.clm_apply (differentiableAt_const _)
      exact F.fderiv_klDiv_phi_apply_live hθ t a hV
  -- ── Step 7: Combine ──
  rw [h_LHS.symm, h_second_eq, h_RHS]

/-- Third derivatives of D(α, φ_t(·)) and D(θ, ·) at θ agree.
Same pattern as `h_second_eq` in `preserves_fisher`, one more level. -/
lemma third_deriv_transfer
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ)
    (a b c : Fin n) :
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (fun θ₃ => M.klDiv (F.φ t θ) (F.φ t θ₃)) θ₂
          (EuclideanSpace.single c 1)) θ₁
        (EuclideanSpace.single b 1)) θ
      (EuclideanSpace.single a 1) =
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv θ) θ₂
          (EuclideanSpace.single c 1)) θ₁
        (EuclideanSpace.single b 1)) θ
      (EuclideanSpace.single a 1) := by
  -- Level 0→1: For θ₂ ∈ paramDomain, fderivs of the two KL functions agree
  have h_L1 : ∀ θ₂ ∈ M.paramDomain,
      fderiv ℝ (fun θ₃ => M.klDiv (F.φ t θ) (F.φ t θ₃)) θ₂ =
      fderiv ℝ (M.klDiv θ) θ₂ := by
    intro θ₂ hθ₂
    exact Filter.EventuallyEq.fderiv_eq
      (by filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₂] with θ₃ hθ₃
          exact F.preserves_divergence t θ hθ θ₃ hθ₃)
  -- Level 1→2: c-th partials agree on paramDomain, so their fderivs agree
  have h_L2 : ∀ θ₁ ∈ M.paramDomain,
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (fun θ₃ => M.klDiv (F.φ t θ) (F.φ t θ₃)) θ₂
          (EuclideanSpace.single c 1)) θ₁ =
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv θ) θ₂ (EuclideanSpace.single c 1)) θ₁ := by
    intro θ₁ hθ₁
    exact Filter.EventuallyEq.fderiv_eq
      (by filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₁] with θ₂ hθ₂
          exact DFunLike.congr_fun (h_L1 θ₂ hθ₂) (EuclideanSpace.single c 1))
  -- Level 2→3: b-th partials agree on paramDomain, lift once more + evaluate at eₐ
  exact DFunLike.congr_fun
    (Filter.EventuallyEq.fderiv_eq
      (by filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ₁ hθ₁
          exact DFunLike.congr_fun (h_L2 θ₁ hθ₁) (EuclideanSpace.single b 1)))
    (EuclideanSpace.single a 1)

/-- The second Fréchet derivative of φ_t at θ, applied to basis pairs.
  d²φ_t(θ)(eₐ, eᵦ) ∈ ParamSpace n -/
noncomputable def secondDerivPhi
    (t : ℝ) (θ : ParamSpace n) (a b : Fin n) : ParamSpace n :=
  fderiv ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂
    (EuclideanSpace.single b 1)) θ (EuclideanSpace.single a 1)

end DivergencePreservingFamily
end TwiceDifferentiableModel
end Spectra.InformationGeometry

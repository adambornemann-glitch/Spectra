/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/Dynamics/FaaDiBruno/Basic.lean
-/
import Spectra.InformationGeometry.Stone.FaaDiBruno.Helpers
import Spectra.InformationGeometry.Stone.Family
import Spectra.InformationGeometry.Dynamics.CubicTensor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
namespace ThriceDifferentiableModel
variable (M : ThriceDifferentiableModel n Ω)
namespace DivergencePreservingFamily
variable {M : ThriceDifferentiableModel n Ω}
variable (F : M.toTwiceDifferentiableModel.DivergencePreservingFamily)
open TwiceDifferentiableModel ThriceDifferentiableModel

set_option maxHeartbeats 220000 in
/-- **Faà di Bruno at critical point.** Since fderiv(klDiv α)(α) = 0,
the third derivative of θ₂ ↦ D(α, φ_t(θ₂)) at θ₂ = θ is:

  D'''(α)(dφ·eₐ, dφ·eᵦ, dφ·ec)
  + g(α)(d²φ_{ab}, dφ_c) + g(α)(d²φ_{ac}, dφ_b) + g(α)(dφ_a, d²φ_{bc})

The f'·d³φ term vanishes because f'(α) = 0.  The f'' = g identification
is the Hessian theorem (`klDiv_hessian_eq_fisher`). -/
lemma kl_faa_di_bruno
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (t : ℝ)
    (a b c : Fin n) :
    let α := F.φ t θ
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (fun θ₃ => M.klDiv α (F.φ t θ₃)) θ₂
          (EuclideanSpace.single c 1)) θ₁
        (EuclideanSpace.single b 1)) θ
      (EuclideanSpace.single a 1) =
    -- ── Third KL deriv at α, evaluated on pushed-forward basis ──
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv α) θ₂
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) α
      (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
    -- ── Three Hessian × d²φ correction terms ──
    + M.toRegularStatisticalModel.fisherBilin α
        (F.secondDerivPhi t θ a b)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
    + M.toRegularStatisticalModel.fisherBilin α
        (F.secondDerivPhi t θ a c)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
    + M.toRegularStatisticalModel.fisherBilin α
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        (F.secondDerivPhi t θ b c) := by
  -- ═══ Setup ═══
  set α := F.φ t θ with hα_def
  have hα : α ∈ M.paramDomain := F.maps_domain t θ hθ
  have hφ_smooth : ContDiff ℝ ⊤ (F.φ t) :=
    F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hf'_zero : fderiv ℝ (M.klDiv α) α = 0 :=
    (M.klDiv_fderiv_eq_zero hα).fderiv
  -- ═══ Level 1→2: Chain rule holds on paramDomain ═══
  have h_chain : ∀ θ₂ ∈ M.paramDomain,
      fderiv ℝ (fun θ₃ => M.klDiv α (F.φ t θ₃)) θ₂
        (EuclideanSpace.single c 1) =
      fderiv ℝ (M.klDiv α) (F.φ t θ₂)
        (fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single c 1)) := by
    intro θ₂ hθ₂
    have hKL_diff : DifferentiableAt ℝ (M.klDiv α) (F.φ t θ₂) := by
      obtain ⟨g, hg⟩ := M.negCrossEntropy_hasFDerivAt hα (F.maps_domain t θ₂ hθ₂)
      exact (hg.const_add _).differentiableAt |>.congr_of_eventuallyEq
        (by filter_upwards [M.isOpen_paramDomain.mem_nhds (F.maps_domain t θ₂ hθ₂)]
              with θ' hθ'; exact M.klDiv_decomp hα hθ')
    show fderiv ℝ (M.klDiv α ∘ F.φ t) θ₂ (EuclideanSpace.single c 1) = _
    rw [(hKL_diff.hasFDerivAt.comp θ₂
      ((hφ_smooth.differentiable WithTop.top_ne_zero).differentiableAt).hasFDerivAt).fderiv]
    rfl
  -- ═══ Level 2→3: fderiv_eq cascade ═══
  have h_L2 : ∀ θ₁ ∈ M.paramDomain,
      fderiv ℝ (fun θ₂ => fderiv ℝ (fun θ₃ => M.klDiv α (F.φ t θ₃)) θ₂
        (EuclideanSpace.single c 1)) θ₁ =
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)
        (fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single c 1))) θ₁ := by
    intro θ₁ hθ₁
    exact Filter.EventuallyEq.fderiv_eq
      (by filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₁] with θ₂ hθ₂
          exact h_chain θ₂ hθ₂)
  -- Level 3: evaluate at eᵇ, then fderiv_eq + evaluate at eₐ
  have h_L3 : fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ => fderiv ℝ (fun θ₃ => M.klDiv α (F.φ t θ₃)) θ₂
        (EuclideanSpace.single c 1)) θ₁
        (EuclideanSpace.single b 1)) θ (EuclideanSpace.single a 1) =
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)
        (fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single c 1))) θ₁
        (EuclideanSpace.single b 1)) θ (EuclideanSpace.single a 1) :=
    DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq
      (by filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ₁ hθ₁
          exact DFunLike.congr_fun (h_L2 θ₁ hθ₁) (EuclideanSpace.single b 1)))
      (EuclideanSpace.single a 1)
  simp [h_L3]
  -- ═══ Product rule at Level 2 ═══
  -- fderiv(L(·)(v(·)))(θ₁)(eᵇ) = dL(eᵇ)(v(θ₁)) + L(θ₁)(dv(eᵇ))
  -- This holds for all θ₁ ∈ paramDomain → EventuallyEq near θ
  have h_prod : ∀ᶠ θ₁ in 𝓝 θ,
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)
        (fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single c 1))) θ₁
        (EuclideanSpace.single b 1) =
      -- P(θ₁): dL(eᵇ) applied to v(θ₁)
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁
        (EuclideanSpace.single b 1)
        (fderiv ℝ (F.φ t) θ₁ (EuclideanSpace.single c 1))
      +
      -- Q(θ₁): L(θ₁) applied to dv(eᵇ) = d²φ(θ₁)(eᵇ, eᶜ)
      fderiv ℝ (M.klDiv α) (F.φ t θ₁)
        (fderiv ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂
          (EuclideanSpace.single c 1)) θ₁
          (EuclideanSpace.single b 1)) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ₁ hθ₁
    have hθ₁_im : F.φ t θ₁ ∈ M.paramDomain := F.maps_domain t θ₁ hθ₁
    -- L(θ₂) := fderiv(klDiv α)(φ_t θ₂) is differentiable at θ₁
    have hL_diff : DifferentiableAt ℝ
        (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁ := by
      -- Componentwise: for each j, θ₀ ↦ fderiv(klDiv α)(θ₀)(eⱼ) agrees with
      -- the cross-score integral near F.φ t θ₁ (via klDiv_partial_j),
      -- which is differentiable (cross_score_hasFDerivAt). Finite-dimensional
      -- reconstruction gives full CLM differentiability, then compose with smooth φ_t.
      have h_fKL : DifferentiableAt ℝ (fderiv ℝ (M.klDiv α)) (F.φ t θ₁) := by
        have h_comp : ∀ j : Fin n, DifferentiableAt ℝ
            (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀
              (EuclideanSpace.single j 1)) (F.φ t θ₁) := by
          intro j
          -- cross_score_differentiableAt gives DifferentiableAt for the
          -- cross-score integral at F.φ t θ₁
          have h_cs := M.cross_score_differentiableAt hα hθ₁_im j
          -- klDiv_partial_j identifies fderiv(klDiv α)(θ₀)(eⱼ) with the
          -- cross-score integral near F.φ t θ₁
          exact h_cs.congr_of_eventuallyEq (by
            filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₁_im] with θ₀ hθ₀
            exact (M.klDiv_partial_j hα hθ₀ j))
        -- Reconstruct CLM differentiability from components
        have h_eq : (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀) =
            (fun θ₀ => ∑ j : Fin n,
              fderiv ℝ (M.klDiv α) θ₀ (EuclideanSpace.single j 1) •
              (innerSL ℝ (EuclideanSpace.single j (1 : ℝ)) :
                ParamSpace n →L[ℝ] ℝ)) := by
          ext θ₀ w
          simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul, innerSL_apply_apply]
          conv_lhs => rw [show w = ∑ j : Fin n, w.ofLp j • EuclideanSpace.single j (1 : ℝ) from by
            ext i; simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, sum_apply,
              Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
            exact Eq.symm (Fintype.sum_ite_eq i w.ofLp)]
          simp only [map_sum, map_smul, smul_eq_mul]
          apply Finset.sum_congr rfl; intro j _
          erw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]
          ring
        show DifferentiableAt ℝ (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀) (F.φ t θ₁)
        rw [h_eq]
        refine DifferentiableAt.fun_sum fun j _ => ?_
        haveI : IsScalarTower ℝ ℝ (ParamSpace n →L[ℝ] ℝ) :=
          ⟨fun r s f => by ext x; simp only [ContinuousLinearMap.smul_apply,
            smul_eq_mul, mul_assoc]⟩
        exact (h_comp j).smul_const _
      exact h_fKL.comp θ₁
        (hφ_smooth.differentiable WithTop.top_ne_zero).differentiableAt
    -- v(θ₂) := fderiv(φ_t)(θ₂)(eᶜ) is differentiable at θ₁
    have hv_diff : DifferentiableAt ℝ
        (fun θ₂ => fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single c 1)) θ₁ :=
      ((hφ_smooth.fderiv_right le_rfl).differentiable
        WithTop.top_ne_zero).differentiableAt.clm_apply
        (differentiableAt_const _)
    -- Product rule for CL map evaluation: d(L(·)(v(·))) = dL(·)(v) + L(dv(·))
    have h_pr := hL_diff.hasFDerivAt.clm_apply hv_diff.hasFDerivAt
    rw [DFunLike.congr_fun h_pr.fderiv (EuclideanSpace.single b 1),
        ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply]
    -- The two terms match (possibly in opposite order)
    abel
  -- ═══ fderiv_eq: third derivative = fderiv(P + Q) ═══
  rw [DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq h_prod)
      (EuclideanSpace.single a 1)]
  -- ═══════════════════════════════════════════════════════════════════
  -- Goal: fderiv(P + Q)(θ)(eₐ) = [tensorial] + 3 corrections
  -- Split: fderiv(P)(θ)(eₐ) + fderiv(Q)(θ)(eₐ)
  -- ═══════════════════════════════════════════════════════════════════
  -- Use fderiv_add (both P and Q are differentiable at θ)
  -- ════ Third-order regularity toolkit (hoisted from `h_P_diff` so that
  -- `h_P_val` in the final calc step can reuse it) ════
  -- ─── Step 1: G(θ') := fderiv(klDiv α)(θ') is DifferentiableAt every
  -- point of paramDomain. Same h_fKL template as in h_Q_diff, lifted to
  -- vary the base point.
  have hG_diff : ∀ θ' ∈ M.paramDomain,
      DifferentiableAt ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ' := by
    intro θ' hθ'
    have h_comp : ∀ j : Fin n, DifferentiableAt ℝ
        (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀ (EuclideanSpace.single j 1)) θ' := by
      intro j
      have h_cs := M.cross_score_differentiableAt hα hθ' j
      exact h_cs.congr_of_eventuallyEq (by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ'] with θ₀ hθ₀
        exact (M.klDiv_partial_j hα hθ₀ j))
    have h_eq : (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀) =
        (fun θ₀ => ∑ j : Fin n,
          fderiv ℝ (M.klDiv α) θ₀ (EuclideanSpace.single j 1) •
          (innerSL ℝ (EuclideanSpace.single j (1 : ℝ)) :
            ParamSpace n →L[ℝ] ℝ)) := by
      ext θ₀ w
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, innerSL_apply_apply]
      conv_lhs => rw [show w = ∑ j : Fin n, w.ofLp j • EuclideanSpace.single j (1 : ℝ) from by
        ext i; simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, sum_apply,
          Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
        exact Eq.symm (Fintype.sum_ite_eq i w.ofLp)]
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl; intro j _
      erw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]
      ring
    show DifferentiableAt ℝ (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀) θ'
    rw [h_eq]
    refine DifferentiableAt.fun_sum fun j _ => ?_
    haveI : IsScalarTower ℝ ℝ (ParamSpace n →L[ℝ] ℝ) :=
      ⟨fun r s f => by ext x; simp only [ContinuousLinearMap.smul_apply,
        smul_eq_mul, mul_assoc]⟩
    exact (h_comp j).smul_const _
  have hF_diff : ∀ θ₂, DifferentiableAt ℝ (F.φ t) θ₂ := fun _ =>
    (hφ_smooth.differentiable WithTop.top_ne_zero).differentiableAt
  -- ─── Step 2: Chain rule formula for fderiv of K := (fderiv(klDiv α)) ∘ φ_t.
  -- Holds on a neighborhood of θ (= the open set paramDomain).
  have hK_fderiv_ev :
      (fun θ₂ => fderiv ℝ (fun θ₃ => fderiv ℝ (M.klDiv α) (F.φ t θ₃)) θ₂) =ᶠ[𝓝 θ]
      (fun θ₂ => (fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₂)).comp
        (fderiv ℝ (F.φ t) θ₂)) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ₂ hθ₂
    have hF : F.φ t θ₂ ∈ M.paramDomain := F.maps_domain t θ₂ hθ₂
    show fderiv ℝ ((fun θ' => fderiv ℝ (M.klDiv α) θ') ∘ F.φ t) θ₂ = _
    exact ((hG_diff _ hF).hasFDerivAt.comp θ₂ (hF_diff θ₂).hasFDerivAt).fderiv
  -- ─── Step 3: The chain rule RHS is DifferentiableAt θ — clm_comp of:
  --   • outer factor: fderiv(G) at α (helper) composed with smooth φ_t
  --   • inner factor: fderiv(φ_t), C^⊤ since φ_t is.
  -- NOTE: the former `letI inst_ncg/inst_ns : … (ParamSpace n)` locals
  -- were removed.  Local *data* instances make every CLM type formed in
  -- their scope carry fvar instance paths (`inst_ncg.toAddCommGroup`,
  -- `NormedSpace.toModule`, …) that fail to unify with the global
  -- `WithLp.instAddCommGroup`/`PiLp.topologicalSpace` paths appearing
  -- in ascribed statement types — they were the actual source of the
  -- "WithLp/PiLp instance gap", not `DifferentiableAt.comp`.
  -- ── Third-order regularity of D(α‖·) at α. ──
  -- Strategy (one tensor level above the h_fKL template):
  --  (i)   hCLM:  basis decomposition L = ∑ₖ L(eₖ)•⟪eₖ,·⟫ of scalar CLMs;
  --  (ii)  hS:    the scalar third partials θ' ↦ ∂ⱼ[−∫ p(α)sₖ(θ')](θ')
  --        are differentiable at α — identify ∂ⱼ of the cross-score
  --        integral with −∫ p(α)·∂ⱼsₖ(θ') near α via
  --        `cross_score_hasFDerivAt'`, then one more Leibniz pass via
  --        `klDiv_third_partial` fed by the ThriceDifferentiableModel
  --        domination/measurability fields;
  --  (iii) doubly-scalar rank-one representation: near α the
  --        second-derivative map equals ∑ₖ∑ⱼ ∂ⱼCₖ(θ')•(⟪eⱼ,·⟫⊗⟪eₖ,·⟫),
  --        differentiable at α by (ii); conclude by congruence.
  have h_helper : DifferentiableAt ℝ
      (fun θ' => fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ') α := by
    haveI : IsScalarTower ℝ ℝ (ParamSpace n →L[ℝ] ℝ) :=
      ⟨fun r s f => by ext x; simp only [ContinuousLinearMap.smul_apply,
        smul_eq_mul, mul_assoc]⟩
    -- (i) Basis decomposition of scalar-valued CLMs (pointwise h_eq).
    have hCLM : ∀ L : ParamSpace n →L[ℝ] ℝ,
        L = ∑ k : Fin n, L (EuclideanSpace.single k 1) •
          (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)) :
            ParamSpace n →L[ℝ] ℝ) := by
      intro L
      ext w
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, innerSL_apply_apply]
      conv_lhs => rw [show w = ∑ k : Fin n, w.ofLp k • EuclideanSpace.single k (1 : ℝ) from by
        ext i; simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, sum_apply,
          Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
        exact Eq.symm (Fintype.sum_ite_eq i w.ofLp)]
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl; intro k _
      erw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]
      ring
    -- (ii) Scalar third partials are differentiable at α.
    have hS : ∀ j k : Fin n, DifferentiableAt ℝ
        (fun θ' => fderiv ℝ (fun θ'' =>
          -∫ ω, M.density α ω *
            M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) θ'
          (EuclideanSpace.single j 1)) α := by
      intro j k
      obtain ⟨g₂, hg₂, _⟩ := M.klDiv_third_partial hα j k
        (M.scorePartial_fderiv_bound α hα α hα j k)
        (M.scorePartial_density_integrable α hα j k)
        (M.scorePartial_deriv_aestronglyMeasurable α hα j k)
        (M.scorePartial_density_aestronglyMeasurable α hα j k)
      refine hg₂.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [M.isOpen_paramDomain.mem_nhds hα] with θ' hθ'
      obtain ⟨g₁, hg₁, heval⟩ := M.cross_score_hasFDerivAt' hα hθ' k
      rw [hg₁.fderiv]
      exact heval j
    -- (iii) Doubly-scalar rank-one representation.  Near α the
    -- second-derivative map equals
    --   ∑ₖ ∑ⱼ ∂ⱼCₖ(θ') • (⟪eⱼ,·⟫.smulRight ⟪eₖ,·⟫),
    -- a finite sum of scalar functions (differentiable at α by (ii))
    -- times *constant* rank-one operators.  All types are pinned via
    -- named arguments: with metavariables in the operator-valued
    -- codomain `ParamSpace n →L[ℝ] (ParamSpace n →L[ℝ] ℝ)`, typeclass
    -- resolution of `NormedSpace ?𝕜 ?F` gets stuck — which is what
    -- killed the `smulRightL`/`clm_apply` formulation of this step.
    haveI : IsScalarTower ℝ ℝ (ParamSpace n →L[ℝ] (ParamSpace n →L[ℝ] ℝ)) :=
      ⟨fun r s f => by
        ext x v
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc]⟩
    have hsum : ∀ k : Fin n, DifferentiableAt ℝ
        (fun θ' => ∑ j : Fin n,
          fderiv ℝ (fun θ'' =>
            -∫ ω, M.density α ω *
              M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) θ'
            (EuclideanSpace.single j 1) •
          (((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).smulRight
            (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)))) :
            ParamSpace n →L[ℝ] (ParamSpace n →L[ℝ] ℝ))) α := fun k =>
      DifferentiableAt.fun_sum (𝕜 := ℝ)
        (u := (Finset.univ : Finset (Fin n))) (x := α)
        (A := fun j θ' =>
          fderiv ℝ (fun θ'' =>
            -∫ ω, M.density α ω *
              M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) θ'
            (EuclideanSpace.single j 1) •
          (((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).smulRight
            (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)))) :
            ParamSpace n →L[ℝ] (ParamSpace n →L[ℝ] ℝ)))
        -- `smul_const` demands `[IsBoundedSMul ℝ F]` on the
        -- operator-valued type, and that goal's instance arguments
        -- (inherited from `smul_const`'s binders) sit on paths the
        -- global `NormedSpace.toIsBoundedSMul` won't unify with.
        -- Route around it: `θ' ↦ ∂ⱼCₖ(θ') • Eⱼₖ` factors through the
        -- *continuous linear map* `(1 : ℝ →L[ℝ] ℝ).smulRight Eⱼₖ`
        -- (generic topological-module layer, no `IsBoundedSMul`), and
        -- `(smulRight 1 Eⱼₖ) r = r • Eⱼₖ` is `rfl`.  `g` is pinned as
        -- the coercion of that map, so the `f` of
        -- `ContinuousLinearMap.differentiableAt` is forced by
        -- unification and the operator blob is written only once.
        fun j _ =>
          DifferentiableAt.fun_comp' (𝕜 := ℝ)
            (g := ⇑((1 : ℝ →L[ℝ] ℝ).smulRight
              (((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).smulRight
                (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)))) :
                ParamSpace n →L[ℝ] (ParamSpace n →L[ℝ] ℝ))))
            (f := fun θ' =>
              fderiv ℝ (fun θ'' =>
                -∫ ω, M.density α ω *
                  M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) θ'
                (EuclideanSpace.single j 1))
            α
            (ContinuousLinearMap.differentiableAt _)
            (hS j k)
    have h_repr_diff : DifferentiableAt ℝ
        (fun θ' => ∑ k : Fin n, ∑ j : Fin n,
          fderiv ℝ (fun θ'' =>
            -∫ ω, M.density α ω *
              M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) θ'
            (EuclideanSpace.single j 1) •
          (((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).smulRight
            (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)))) :
            ParamSpace n →L[ℝ] (ParamSpace n →L[ℝ] ℝ))) α :=
      -- `𝕜`, `u`, `x` must be pinned in addition to `A`: they are the
      -- metavariables that were still unassigned when unification
      -- compared the (normed-path) conclusion of `fun_sum` against the
      -- (TVS-path) ascription above, making the defeq instance-path
      -- bridge fail.  With all arguments ground, the final defeq check
      -- unfolds the paths (same situation as `h1` below).
      DifferentiableAt.fun_sum (𝕜 := ℝ)
        (u := (Finset.univ : Finset (Fin n))) (x := α)
        (A := fun k θ' => ∑ j : Fin n,
          fderiv ℝ (fun θ'' =>
            -∫ ω, M.density α ω *
              M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) θ'
            (EuclideanSpace.single j 1) •
          (((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).smulRight
            (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)))) :
            ParamSpace n →L[ℝ] (ParamSpace n →L[ℝ] ℝ)))
        fun k _ => hsum k
    refine h_repr_diff.congr_of_eventuallyEq ?_
    filter_upwards [M.isOpen_paramDomain.mem_nhds hα] with θ' hθ'
    calc fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ'
        = fderiv ℝ (fun θ'' => ∑ k : Fin n,
            (-∫ ω, M.density α ω *
              M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) •
            (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)) :
              ParamSpace n →L[ℝ] ℝ)) θ' := by
          -- The second-derivative map agrees near θ' with the
          -- component sum: klDiv_partial_j inside the hCLM expansion.
          refine Filter.EventuallyEq.fderiv_eq ?_
          filter_upwards [M.isOpen_paramDomain.mem_nhds hθ'] with θ'' hθ''
          rw [hCLM (fderiv ℝ (M.klDiv α) θ'')]
          exact Finset.sum_congr rfl fun k _ => by
            rw [M.klDiv_partial_j hα hθ'' k]
      _ = ∑ k : Fin n, fderiv ℝ (fun θ'' =>
            (-∫ ω, M.density α ω *
              M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) •
            (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)) :
              ParamSpace n →L[ℝ] ℝ)) θ' :=
          fderiv_fun_sum fun k _ =>
            (M.cross_score_differentiableAt hα hθ' k).smul_const _
      _ = ∑ k : Fin n, ∑ j : Fin n,
          fderiv ℝ (fun θ'' =>
            -∫ ω, M.density α ω *
              M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) θ'
            (EuclideanSpace.single j 1) •
          (((innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).smulRight
            (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)))) :
            ParamSpace n →L[ℝ] (ParamSpace n →L[ℝ] ℝ)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          -- fderiv of (scalar • const), as a term-mode equation:
          -- `rw [fderiv_smul_const …]` fails its keyed match on the
          -- instance-laden CLM types, but elaboration-level defeq
          -- (`Eq.trans` against the goal) is fine.
          refine (((M.cross_score_differentiableAt hα hθ' k).hasFDerivAt.smul_const
            (innerSL ℝ (EuclideanSpace.single k (1 : ℝ)) :
              ParamSpace n →L[ℝ] ℝ)).fderiv).trans ?_
          -- (fderiv Cₖ θ').smulRight ⟪eₖ,·⟫ = ∑ⱼ ∂ⱼCₖ(θ') • Eⱼₖ:
          -- expand fderiv Cₖ θ' by (i) and push the sum through.
          conv_lhs => rw [hCLM (fderiv ℝ (fun θ'' =>
            -∫ ω, M.density α ω *
              M.toRegularStatisticalModel.score θ'' k ω ∂M.refMeasure) θ')]
          ext w v
          simp only [ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul]
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  -- Third-order regularity composed with the smooth flow.  Re-type the
  -- helper at the unfolded point `F.φ t θ`, then compose with
  -- `fun_comp'`, whose conclusion is the applied-lambda form (no `∘` to
  -- unify), pinning `g` and `f` by name so no metavariable reaches the
  -- operator-valued instance problems (`comp` left `NormedSpace ?𝕜 ?G`
  -- stuck and errored on `hg`).
  have h_helper' : DifferentiableAt ℝ
      (fun θ' => fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ')
      (F.φ t θ) := by
    rw [← hα_def]; exact h_helper
  have h1 : DifferentiableAt ℝ
      (fun θ₂ => fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₂)) θ :=
    DifferentiableAt.fun_comp' (𝕜 := ℝ)
      (g := fun θ' => fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ')
      (f := F.φ t)
      θ h_helper' (hF_diff θ)
  have h2 : DifferentiableAt ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂) θ :=
    ((hφ_smooth.fderiv_right le_rfl).differentiable WithTop.top_ne_zero).differentiableAt
  have h_RHS_diff : DifferentiableAt ℝ
      (fun θ₂ => (fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₂)).comp
        (fderiv ℝ (F.φ t) θ₂)) θ :=
    h1.clm_comp h2
  -- ─── Step 4: Lift to fderiv(K) DifferentiableAt θ via EventuallyEq.
  have hfK_diff : DifferentiableAt ℝ
      (fun θ₂ => fderiv ℝ (fun θ₃ => fderiv ℝ (M.klDiv α) (F.φ t θ₃)) θ₂) θ :=
    h_RHS_diff.congr_of_eventuallyEq hK_fderiv_ev
  -- ─── Step 5: Apply at single b 1 (clm_apply with const).
  have hN_diff : DifferentiableAt ℝ
      (fun θ₁ => fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁
        (EuclideanSpace.single b 1)) θ :=
    hfK_diff.clm_apply (differentiableAt_const _)
  -- ─── Step 6: v(θ₁) := dφ(θ₁)(single c 1) DifferentiableAt θ (same as h_Q_diff's hw level 1).
  have hv_diff : DifferentiableAt ℝ
      (fun θ₁ => fderiv ℝ (F.φ t) θ₁ (EuclideanSpace.single c 1)) θ :=
    ((hφ_smooth.fderiv_right le_rfl).differentiable WithTop.top_ne_zero
      ).differentiableAt.clm_apply (differentiableAt_const _)
  have h_P_diff : DifferentiableAt ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁
        (EuclideanSpace.single b 1)
        (fderiv ℝ (F.φ t) θ₁ (EuclideanSpace.single c 1))) θ :=
    -- ─── Step 7: Outer clm_apply.
    hN_diff.clm_apply hv_diff
  have h_Q_diff : DifferentiableAt ℝ (fun θ₁ =>
      fderiv ℝ (M.klDiv α) (F.φ t θ₁)
        (fderiv ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂
          (EuclideanSpace.single c 1)) θ₁
          (EuclideanSpace.single b 1))) θ := by
    -- Q(θ₁) = L(θ₁)(w(θ₁)) where:
    --   L(θ₁) := fderiv(klDiv α)(F.φ t θ₁)        : ParamSpace →L[ℝ] ℝ
    --   w(θ₁) := d²φ_bc(θ₁)                       : ParamSpace
    -- Differentiability via clm_apply.
    --
    -- L differentiable at θ: same template as `hL_diff` inside `h_prod`,
    -- lifted from θ₁ ∈ paramDomain to the specific point θ.
    have hL_diff : DifferentiableAt ℝ
        (fun θ₁ => fderiv ℝ (M.klDiv α) (F.φ t θ₁)) θ := by
      have h_comp : ∀ j : Fin n, DifferentiableAt ℝ
          (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀
            (EuclideanSpace.single j 1)) α := by
        intro j
        have h_cs := M.cross_score_differentiableAt hα hα j
        exact h_cs.congr_of_eventuallyEq (by
          filter_upwards [M.isOpen_paramDomain.mem_nhds hα] with θ₀ hθ₀
          exact (M.klDiv_partial_j hα hθ₀ j))
      have h_eq : (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀) =
          (fun θ₀ => ∑ j : Fin n,
            fderiv ℝ (M.klDiv α) θ₀ (EuclideanSpace.single j 1) •
            (innerSL ℝ (EuclideanSpace.single j (1 : ℝ)) :
              ParamSpace n →L[ℝ] ℝ)) := by
        ext θ₀ w
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul, innerSL_apply_apply]
        conv_lhs => rw [show w = ∑ j : Fin n, w.ofLp j • EuclideanSpace.single j (1 : ℝ) from by
          ext i; simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, sum_apply,
            Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
          exact Eq.symm (Fintype.sum_ite_eq i w.ofLp)]
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl; intro j _
        erw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]
        ring
      have h_fKL : DifferentiableAt ℝ (fderiv ℝ (M.klDiv α)) α := by
        show DifferentiableAt ℝ (fun θ₀ => fderiv ℝ (M.klDiv α) θ₀) α
        rw [h_eq]
        refine DifferentiableAt.fun_sum fun j _ => ?_
        haveI : IsScalarTower ℝ ℝ (ParamSpace n →L[ℝ] ℝ) :=
          ⟨fun r s f => by ext x; simp only [ContinuousLinearMap.smul_apply,
            smul_eq_mul, mul_assoc]⟩
        exact (h_comp j).smul_const _
      exact h_fKL.comp θ
        (hφ_smooth.differentiable WithTop.top_ne_zero).differentiableAt
    -- w differentiable at θ: φ_t is C^⊤, hence so is fderiv(φ_t), hence so is
    -- (· (single c 1)) ∘ fderiv(φ_t), hence so is its fderiv, hence we can
    -- apply at the constant single b 1.
    have hw_diff : DifferentiableAt ℝ
        (fun θ₁ => fderiv ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂
          (EuclideanSpace.single c 1)) θ₁ (EuclideanSpace.single b 1)) θ := by
      have hg : ContDiff ℝ ⊤
          (fun θ₂ => fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single c 1)) :=
        (hφ_smooth.fderiv_right le_rfl).clm_apply contDiff_const
      exact ((hg.fderiv_right le_rfl).differentiable WithTop.top_ne_zero
        ).differentiableAt.clm_apply (differentiableAt_const _)
    exact hL_diff.clm_apply hw_diff
  -- Split fderiv(P + Q) = fderiv(P) + fderiv(Q) via HasFDerivAt
  set P := fun θ₁ =>
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁
        (EuclideanSpace.single b 1)
        (fderiv ℝ (F.φ t) θ₁ (EuclideanSpace.single c 1))
  set Q := fun θ₁ =>
      fderiv ℝ (M.klDiv α) (F.φ t θ₁)
        (fderiv ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂
          (EuclideanSpace.single c 1)) θ₁
          (EuclideanSpace.single b 1))
  have h_PQ : HasFDerivAt (fun θ₁ => P θ₁ + Q θ₁)
      (fderiv ℝ P θ + fderiv ℝ Q θ) θ :=
    h_P_diff.hasFDerivAt.add h_Q_diff.hasFDerivAt
  calc fderiv ℝ (fun θ₁ => P θ₁ + Q θ₁) θ (EuclideanSpace.single a 1)
      = (fderiv ℝ P θ + fderiv ℝ Q θ) (EuclideanSpace.single a 1) := by
        rw [h_PQ.fderiv]
    _ = fderiv ℝ P θ (EuclideanSpace.single a 1) +
        fderiv ℝ Q θ (EuclideanSpace.single a 1) :=
        ContinuousLinearMap.add_apply _ _ _
    _ = _ := by -- Heartbeat increase stems from this calc block
    -- ═══════════════════════════════════════════════════════════════════
      -- Compute fderiv(Q)(θ)(eₐ)
      -- Q(θ₁) = fderiv(klDiv α)(φ_t θ₁)(d²φ(θ₁)(eᵇ, eᶜ))
      -- Product rule: dL(eₐ)(d²φ_bc) + L(θ)(d(d²φ)(eₐ))
      -- Second term vanishes: L(θ) = fderiv(klDiv α)(α) = 0
      -- First term: fderiv²(klDiv α)(α)(uₐ)(d²φ_bc) = fisherBilin α uₐ d²φ_bc
      -- ═══════════════════════════════════════════════════════════════════
      have h_Q_val : fderiv ℝ (fun θ₁ =>
          fderiv ℝ (M.klDiv α) (F.φ t θ₁)
            (fderiv ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂
              (EuclideanSpace.single c 1)) θ₁
              (EuclideanSpace.single b 1))) θ (EuclideanSpace.single a 1) =
        M.toRegularStatisticalModel.fisherBilin α
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
          (F.secondDerivPhi t θ b c) := by
        -- Product rule for L(θ₁)(w(θ₁)) where L = fderiv(klDiv α) ∘ φ_t:
        -- this is `fderiv_klDiv_phi_apply_live` with the live vector
        -- V(θ₁) := d²φ(θ₁)(e_b, e_c).  At θ the operator factor
        -- fderiv(klDiv α)(φ_t θ) vanishes, so only the frozen vector
        -- V(θ) = secondDerivPhi t θ b c (definitionally) survives,
        -- paired against the Hessian = Fisher.
        have hV : DifferentiableAt ℝ
            (fun θ₁ => fderiv ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂
              (EuclideanSpace.single c 1)) θ₁ (EuclideanSpace.single b 1)) θ := by
          have hg : ContDiff ℝ ⊤
              (fun θ₂ => fderiv ℝ (F.φ t) θ₂ (EuclideanSpace.single c 1)) :=
            (hφ_smooth.fderiv_right le_rfl).clm_apply contDiff_const
          exact ((hg.fderiv_right le_rfl).differentiable WithTop.top_ne_zero
            ).differentiableAt.clm_apply (differentiableAt_const _)
        rw [hα_def]
        exact DivergencePreservingFamily.fderiv_klDiv_phi_apply_live F hθ t a hV
      -- ═══════════════════════════════════════════════════════════════════
      -- Compute fderiv(P)(θ)(eₐ)
      -- P(θ₁) = M(θ₁)(w(θ₁)) where
      --   M(θ₁) = fderiv(fderiv(klDiv α) ∘ φ_t)(θ₁)(eᵇ) : ParamSpace n →L[ℝ] ℝ
      --   w(θ₁) = dφ(θ₁)·eᶜ : ParamSpace n
      -- Product rule: M'(eₐ)(w(θ)) + M(θ)(dw(eₐ))
      --   M(θ) = fderiv²(klDiv α)(α)(uᵇ) acts as fisherBilin α uᵇ ·
      --   dw(eₐ) = d²φ_ac
      --   → M(θ)(d²φ_ac) = fisherBilin α (d²φ_ac) uᵇ        [correction 3]
      --
      --   M'(eₐ)(u_c) requires differentiating M(θ₁) = fderiv²(klDiv α)(φ_t θ₁)(dφ(θ₁)·eᵇ)
      --   Another product rule: N = fderiv²(klDiv α) ∘ φ_t, w₂ = dφ(·)·eᵇ
      --     N(θ)(d²φ_ab)(u_c) = fisherBilin α (d²φ_ab) u_c     [correction 2]
      --     dN(eₐ)(uᵇ)(u_c) = fderiv³(klDiv α)(α)(uₐ)(uᵇ)(u_c)  [tensorial]
      -- ═══════════════════════════════════════════════════════════════════
      have h_P_val : fderiv ℝ (fun θ₁ =>
          fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁
            (EuclideanSpace.single b 1)
            (fderiv ℝ (F.φ t) θ₁ (EuclideanSpace.single c 1))) θ
          (EuclideanSpace.single a 1) =
        -- Tensorial third KL derivative at α
        fderiv ℝ (fun θ₁ =>
          fderiv ℝ (fun θ₂ =>
            fderiv ℝ (M.klDiv α) θ₂
              (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) α
          (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))
        + M.toRegularStatisticalModel.fisherBilin α
            (F.secondDerivPhi t θ a b)
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
        + M.toRegularStatisticalModel.fisherBilin α
            (F.secondDerivPhi t θ a c)
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) := by
        -- Three nested product rules:
        -- 1. P = M(·)(w(·)):  M'·w + M·w'
        --    M(θ) = Hessian(α)(uᵇ), w' = d²φ_ac → M·w' = fisherBilin correction 3
        --    (Schwarz symmetry of the Hessian swaps the slots)
        -- 2. M = N(·)(w₂(·)):  N'·w₂ + N·w₂'
        --    N(θ) = Hessian(α), w₂' = d²φ_ab → N·w₂' = fisherBilin correction 2
        -- 3. N' composed with chain rule through φ_t gives tensorial part
        have hφtθ : F.φ t θ = α := hα_def.symm
        have hv_b : DifferentiableAt ℝ
            (fun θ₁ => fderiv ℝ (F.φ t) θ₁ (EuclideanSpace.single b 1)) θ :=
          ((hφ_smooth.fderiv_right le_rfl).differentiable WithTop.top_ne_zero
            ).differentiableAt.clm_apply (differentiableAt_const _)
        -- ── Rule 1: split fderiv(P)(θ)(eₐ) = M(θ)(w'(eₐ)) + (dM(eₐ))(w(θ)). ──
        have h_pr := hN_diff.hasFDerivAt.clm_apply hv_diff.hasFDerivAt
        rw [DFunLike.congr_fun h_pr.fderiv (EuclideanSpace.single a 1),
            ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.flip_apply]
        -- ── M(θ) = Hess(α) ∘ dφ(θ) at e_b, via the chain rule at θ. ──
        have hMθ : fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ =
            (fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') α).comp
              (fderiv ℝ (F.φ t) θ) := by
          have h : fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ =
              (fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ)).comp
                (fderiv ℝ (F.φ t) θ) := by
            show fderiv ℝ ((fun θ' => fderiv ℝ (M.klDiv α) θ') ∘ F.φ t) θ = _
            exact ((hG_diff _ (F.maps_domain t θ hθ)).hasFDerivAt.comp θ
              (hF_diff θ).hasFDerivAt).fderiv
          rw [hφtθ] at h
          exact h
        -- ── Schwarz: the Hessian of D(α‖·) at α is symmetric. ──
        have hSchwarz : ∀ v w : ParamSpace n,
            fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') α v w =
            fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') α w v := by
          have hev : ∀ᶠ θ' in 𝓝 α,
              HasFDerivAt (M.klDiv α) (fderiv ℝ (M.klDiv α) θ') θ' := by
            filter_upwards [M.isOpen_paramDomain.mem_nhds hα] with θ' hθ'
            have hd : DifferentiableAt ℝ (M.klDiv α) θ' := by
              obtain ⟨g, hg⟩ := M.negCrossEntropy_hasFDerivAt hα hθ'
              exact (hg.const_add _).differentiableAt |>.congr_of_eventuallyEq
                (by filter_upwards [M.isOpen_paramDomain.mem_nhds hθ']
                      with θ'' hθ''; exact M.klDiv_decomp hα hθ'')
            exact hd.hasFDerivAt
          exact fun v w => second_derivative_symmetric_of_eventually_of_real
            hev (hG_diff α hα).hasFDerivAt v w
        -- ── Correction 3: M(θ)(d²φ_ac) = g(α)(d²φ_ac, dφ_b). ──
        have hterm1 : fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ
            (EuclideanSpace.single b 1)
            (fderiv ℝ (fun θ₁ => fderiv ℝ (F.φ t) θ₁
              (EuclideanSpace.single c 1)) θ (EuclideanSpace.single a 1)) =
          M.toRegularStatisticalModel.fisherBilin α
            (F.secondDerivPhi t θ a c)
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) := by
          rw [DFunLike.congr_fun hMθ (EuclideanSpace.single b 1),
              ContinuousLinearMap.comp_apply, hSchwarz]
          exact M.klDiv_hessian_vec hα _ _
        -- ── Rule 2: dM(eₐ) via M(θ₁) = N(θ₁)(dφ(θ₁)e_b) near θ. ──
        have hM_ev : (fun θ₁ =>
            fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁
              (EuclideanSpace.single b 1)) =ᶠ[𝓝 θ]
            (fun θ₁ => fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₁)
              (fderiv ℝ (F.φ t) θ₁ (EuclideanSpace.single b 1))) := by
          filter_upwards [hK_fderiv_ev] with θ₁ h₁
          rw [h₁, ContinuousLinearMap.comp_apply]
        have h_pr2 := h1.hasFDerivAt.clm_apply hv_b.hasFDerivAt
        have hterm2 : fderiv ℝ (fun θ₁ =>
            fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁
              (EuclideanSpace.single b 1)) θ (EuclideanSpace.single a 1)
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) =
          M.toRegularStatisticalModel.fisherBilin α
            (F.secondDerivPhi t θ a b)
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))
          + fderiv ℝ (fun θ₁ =>
              fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₁)) θ
              (EuclideanSpace.single a 1)
              (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
              (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) := by
          rw [DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq hM_ev)
                (EuclideanSpace.single a 1),
              DFunLike.congr_fun h_pr2.fderiv (EuclideanSpace.single a 1)]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.flip_apply]
          refine congrArg₂ (· + ·) ?_ rfl
          rw [hφtθ]
          exact M.klDiv_hessian_vec hα _ _
        -- ── Rule 3: the tensorial term — chain rule through φ_t, then
        -- scalarize the operator-valued third derivative at α. ──
        have hT : fderiv ℝ (fun θ₁ =>
            fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₁)) θ
            (EuclideanSpace.single a 1)
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) =
          fderiv ℝ (fun θ₁ =>
            fderiv ℝ (fun θ₂ =>
              fderiv ℝ (M.klDiv α) θ₂
                (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
              (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) α
            (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1)) := by
          have hN_chain : fderiv ℝ (fun θ₁ =>
              fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₁)) θ =
              (fderiv ℝ (fun θ'' =>
                fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') θ'') α).comp
                (fderiv ℝ (F.φ t) θ) := by
            have h : fderiv ℝ (fun θ₁ =>
                fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₁)) θ =
                (fderiv ℝ (fun θ'' =>
                  fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') θ'') (F.φ t θ)).comp
                  (fderiv ℝ (F.φ t) θ) := by
              show fderiv ℝ ((fun θ'' =>
                fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') θ'') ∘ F.φ t) θ = _
              -- `comp` must be fully pinned: with `g`/`g'` as metavariables,
              -- unification gives up bridging the generic vs normed instance
              -- paths on the operator-valued codomain (same disease as the
              -- `fun_comp'` NOTE above for `h1`).
              exact (HasFDerivAt.comp (𝕜 := ℝ)
                (g := fun θ' => fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ')
                (g' := fderiv ℝ (fun θ' =>
                  fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ') (F.φ t θ))
                (f := F.φ t) (f' := fderiv ℝ (F.φ t) θ)
                θ h_helper'.hasFDerivAt (hF_diff θ).hasFDerivAt).fderiv
            rw [hφtθ] at h
            exact h
          rw [DFunLike.congr_fun hN_chain (EuclideanSpace.single a 1),
              ContinuousLinearMap.comp_apply]
          -- Scalarize: near α, the b-partial of the frozen-c-direction map
          -- is the second-derivative operator applied to (u_b, u_c).
          have hmid_ev : (fun θ₁ => fderiv ℝ (fun θ₂ =>
              fderiv ℝ (M.klDiv α) θ₂
                (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) θ₁
              (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))) =ᶠ[𝓝 α]
              (fun θ₁ => fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ₁
                (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1))
                (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1))) := by
            filter_upwards [M.isOpen_paramDomain.mem_nhds hα] with θ₁ hθ₁
            rw [((hG_diff θ₁ hθ₁).hasFDerivAt.clm_apply
              (hasFDerivAt_const
                (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) θ₁)).fderiv]
            simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
              ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
              map_zero, zero_add]
          rw [DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq hmid_ev)
              (fderiv ℝ (F.φ t) θ (EuclideanSpace.single a 1))]
          -- Two `clm_apply`s with constant directions unpack the
          -- operator-valued third derivative.
          have hd1 := h_helper.hasFDerivAt.clm_apply
            (hasFDerivAt_const
              (fderiv ℝ (F.φ t) θ (EuclideanSpace.single b 1)) α)
          have hd2 := hd1.clm_apply
            (hasFDerivAt_const
              (fderiv ℝ (F.φ t) θ (EuclideanSpace.single c 1)) α)
          rw [hd2.fderiv]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
            ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
            map_zero, zero_add]
        rw [hterm1, hterm2, hT]
        ring
      -- ═══ Assemble ═══
      rw [h_P_val, h_Q_val]


end DivergencePreservingFamily
end ThriceDifferentiableModel
end Spectra.InformationGeometry

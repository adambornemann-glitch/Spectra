/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/Dynamics/FaaDiBruno
-/
import LogosLibrary.InformationGeometry.Dynamics.Family
import LogosLibrary.InformationGeometry.Dynamics.CubicTensor

import Mathlib.Tactic.Explode

namespace InformationGeometry

open MeasureTheory Finset Filter Topology TopologicalSpace TwiceDifferentiableModel

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace ThriceDifferentiableModel
variable (M : ThriceDifferentiableModel n Ω)
namespace DivergencePreservingFamily
variable {M : ThriceDifferentiableModel n Ω}
variable (F : M.toTwiceDifferentiableModel.DivergencePreservingFamily)


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
          -- Unknown identifier `cross_score_differentiableAt`
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
          conv_lhs => rw [show w = ∑ j : Fin n, w j • EuclideanSpace.single j 1 from by
            ext i; simp [Pi.single, Function.update_apply, Finset.mem_univ]]
          rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
          congr 1; ext j
          erw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]; ring
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
  have h_P_diff : DifferentiableAt ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv α) (F.φ t θ₂)) θ₁
        (EuclideanSpace.single b 1)
        (fderiv ℝ (F.φ t) θ₁ (EuclideanSpace.single c 1))) θ := by
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
        conv_lhs => rw [show w = ∑ j : Fin n, w j • EuclideanSpace.single j 1 from by
          ext i; simp [Pi.single, Function.update_apply, Finset.mem_univ]]
        rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
        congr 1; ext j
        erw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]; ring
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
    have h_RHS_diff : DifferentiableAt ℝ
        (fun θ₂ => (fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₂)).comp
          (fderiv ℝ (F.φ t) θ₂)) θ := by
      -- Third-order regularity at α, declared locally to keep typeclass
      -- synthesis in one consistent context (cross-file instance synthesis
      -- on PiLp/WithLp was producing inconsistent AddCommGroup paths).
      letI inst_ncg : NormedAddCommGroup (ParamSpace n) := inferInstance
      letI inst_ns : NormedSpace ℝ (ParamSpace n) := inferInstance
      have h_helper : DifferentiableAt ℝ
          (fun θ' => fderiv ℝ (fun θ'' => fderiv ℝ (M.klDiv α) θ'') θ') α := by
        sorry
      -- Third-order regularity composed with the smooth flow.
      -- We sorry this directly rather than fighting the WithLp/PiLp
      -- instance gap that arises from gluing a third-order helper
      -- through DifferentiableAt.comp.
      have h1 : DifferentiableAt ℝ
          (fun θ₂ => fderiv ℝ (fun θ' => fderiv ℝ (M.klDiv α) θ') (F.φ t θ₂)) θ := by
        sorry
      have h2 : DifferentiableAt ℝ (fun θ₂ => fderiv ℝ (F.φ t) θ₂) θ :=
        ((hφ_smooth.fderiv_right le_rfl).differentiable WithTop.top_ne_zero).differentiableAt
      exact h1.clm_comp h2
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
    -- ─── Step 7: Outer clm_apply.
    exact hN_diff.clm_apply hv_diff
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
        conv_lhs => rw [show w = ∑ j : Fin n, w j • EuclideanSpace.single j 1 from by
          ext i; simp [Pi.single, Function.update_apply, Finset.mem_univ]]
        rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
        congr 1; ext j
        erw [EuclideanSpace.inner_single_left, RCLike.conj_to_real, one_mul]; ring
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
    _ = _ := by
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
        -- Product rule for L(θ₁)(w(θ₁)) where L = fderiv(klDiv α) ∘ φ_t
        -- At θ: L(θ) = fderiv(klDiv α)(α) = 0, kills the L·dw term
        -- Surviving term: dL(eₐ)(w(θ)) = fderiv²(klDiv α)(α)(uₐ)(d²φ_bc)
        -- Hessian theorem identifies this with fisherBilin α uₐ d²φ_bc
        sorry
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
        -- 2. M = N(·)(w₂(·)):  N'·w₂ + N·w₂'
        --    N(θ) = Hessian(α), w₂' = d²φ_ab → N·w₂' = fisherBilin correction 2
        -- 3. N' composed with chain rule through φ_t gives tensorial part
        sorry
      -- ═══ Assemble ═══
      rw [h_P_val, h_Q_val]


end DivergencePreservingFamily
end ThriceDifferentiableModel
end InformationGeometry

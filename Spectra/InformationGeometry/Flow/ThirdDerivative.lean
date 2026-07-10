/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Flow.MixtureSymmetry
import Spectra.InformationGeometry.StatisticalManifold
import Spectra.InformationGeometry.CramerRao.Quantum
import Spectra.InformationGeometry.Divergence
import Spectra.InformationGeometry.Connection.AmariChentsov
import Spectra.InformationGeometry.Connection.Basic
import Spectra.InformationGeometry.Flow.Family
import Spectra.InformationGeometry.Flow.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.WithTop
-- For Stone Uniqueness --
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Order.Compact

/-!
# The integrated Bartlett identities and the diagonal third KL derivative

Second of four files proving the m-connection transformation law (see
`MixtureConnection.lean`'s module docstring for the full roadmap). Builds on
`MixtureSymmetry.lean`'s relabeling lemmas to assemble, entirely from `ThriceDifferentiableModel`'s
bundled regularity fields, the integrated Bartlett identities and the componentwise/trilinear
diagonal third derivative of the KL divergence.

## On the name clash with `Connection.Bartlett`

`Connection/Bartlett.lean` also declares `bartlett_second`/`bartlett_third`, over
`TwiceDifferentiableModel`. This is **not** a duplicate: this file does not import
`Connection.Bartlett` (there is no import relationship in either direction), and the two are
genuinely different statements dressed in the same name and conclusion. `Connection.Bartlett`'s
versions take the needed analytic facts (integrability of the integrand, and for `bartlett_third`
also the order-2 identity and a Leibniz/Fréchet-derivative witness) as *explicit hypotheses*, so
they apply to any model satisfying those hypotheses directly. This file's versions are
*zero-hypothesis corollaries* specialized to `ThriceDifferentiableModel`: every one of those
hypotheses is discharged automatically from the model's own bundled structure fields
(`scorePartial_density_integrable`, `bartlett2_hasFDerivAt`, etc.) — the point of bundling that
regularity in the first place.

## Main statements

* `bartlett_second`, `bartlett_third` — the integrated Bartlett identities (see above for how
  these relate to the same-named lemmas in `Connection.Bartlett`)
* `fisherMatrix_hasFDerivAt'`, `fisherMatrix_fderiv_single` — the derivative of the Fisher matrix
  along the parameter, `∂ᵢg_{jk} = C_{ijk} + Γᵐ_{ij,k} + Γᵐ_{ik,j}`
* `klDiv_third_deriv_eval`, `klDiv_third_deriv_trilin` — the diagonal third KL derivative,
  componentwise and as a trilinear form

Downstream: `PullbackIdentities.lean` → `MixtureConnection.lean`.
-/

open MeasureTheory Finset Filter Topology TopologicalSpace
namespace Spectra.InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace ThriceDifferentiableModel

variable (M : ThriceDifferentiableModel n Ω)
open TwiceDifferentiableModel

-- ════════════════════════════════════════════════════════════════════
-- §3. The Bartlett identities, integrated
-- ════════════════════════════════════════════════════════════════════

/-- **Bartlett-2**: `∫ (∂ⱼsₖ + sⱼsₖ)·p dμ = 0` at every domain point. -/
lemma bartlett_second {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (j k : Fin n) :
    ∫ ω, (M.scorePartial θ j k ω +
        M.toRegularStatisticalModel.score θ j ω *
        M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω ∂M.refMeasure = 0 := by
  have h1 : Integrable
      (fun ω => M.scorePartial θ j k ω * M.density θ ω) M.refMeasure :=
    (M.scorePartial_density_integrable θ hθ j k).congr
      (by filter_upwards with ω; exact mul_comm _ _)
  have h2 : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω *
      M.density θ ω) M.refMeasure :=
    M.toRegularStatisticalModel.fisherEntry_integrable hθ
      (M.scoreSqIntegrable θ hθ) j k
  have hsplit : (fun ω => (M.scorePartial θ j k ω +
      M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω) * M.density θ ω) =
      fun ω => M.scorePartial θ j k ω * M.density θ ω +
        M.toRegularStatisticalModel.score θ j ω *
        M.toRegularStatisticalModel.score θ k ω * M.density θ ω := by
    funext ω; ring
  rw [hsplit, integral_add h1 h2,
      M.integral_scorePartial_eq_neg_fisherMatrix hθ j k]
  have hg : (∫ ω, M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω *
      M.density θ ω ∂M.refMeasure) =
      M.toRegularStatisticalModel.fisherMatrix θ j k := rfl
  rw [hg]
  ring

/-- **Bartlett-3**: the five-term derivative of the Bartlett-2 integral
vanishes.  This is precisely the `h_B` hypothesis of
`klDiv_third_deriv_decomposition`. -/
lemma bartlett_third {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (i j k : Fin n) :
    ∫ ω,
      (fderiv ℝ (fun θ'' => M.scorePartial θ'' j k ω) θ
          (EuclideanSpace.single i 1) +
       M.toRegularStatisticalModel.score θ j ω *
         M.scorePartial θ i k ω +
       M.toRegularStatisticalModel.score θ i ω *
         M.scorePartial θ j k ω +
       M.toRegularStatisticalModel.score θ k ω *
         M.scorePartial θ i j ω +
       M.toRegularStatisticalModel.score θ i ω *
         M.toRegularStatisticalModel.score θ j ω *
         M.toRegularStatisticalModel.score θ k ω) *
      M.density θ ω ∂M.refMeasure = 0 := by
  obtain ⟨L, hL, hL_eval⟩ := M.bartlett2_hasFDerivAt θ hθ i j k
  -- the Bartlett-2 integral is the zero function on the (open) domain
  have hzero : HasFDerivAt
      (fun θ' => ∫ ω, (M.scorePartial θ' j k ω +
        M.toRegularStatisticalModel.score θ' j ω *
        M.toRegularStatisticalModel.score θ' k ω) *
        M.density θ' ω ∂M.refMeasure)
      (0 : ParamSpace n →L[ℝ] ℝ) θ := by
    refine (hasFDerivAt_const (0 : ℝ) θ).congr_of_eventuallyEq ?_
    filter_upwards [M.isOpen_paramDomain.mem_nhds hθ] with θ' hθ'
    exact M.bartlett_second hθ' j k
  have h0 : L (EuclideanSpace.single i 1) = 0 := by
    rw [hL.unique hzero]
    exact ContinuousLinearMap.zero_apply _
  exact hL_eval.symm.trans h0

-- ════════════════════════════════════════════════════════════════════
-- §4. The derivative of the Fisher matrix along the parameter
-- ════════════════════════════════════════════════════════════════════

/-- `θ' ↦ g_{jk}(θ')` is differentiable, with components
`∂ᵢg_{jk} = C_{ijk} + Γᵐ_{ij,k} + Γᵐ_{ik,j}`.  Post-processed form of
the `fisherMatrix_hasFDerivAt` structure field. -/
lemma fisherMatrix_hasFDerivAt' {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (j k : Fin n) :
    ∃ L : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' j k) L θ ∧
      ∀ i : Fin n,
        L (EuclideanSpace.single i 1) =
          M.cubicTensor θ i j k + M.mConnectionCoeff θ i j k +
          M.mConnectionCoeff θ i k j := by
  obtain ⟨L, hL, hL_eval⟩ := M.fisherMatrix_hasFDerivAt θ hθ j k
  refine ⟨L, hL, fun i => ?_⟩
  rw [hL_eval i]
  have h1 : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ i ω *
      M.toRegularStatisticalModel.score θ j ω *
      M.toRegularStatisticalModel.score θ k ω *
      M.density θ ω) M.refMeasure := M.tripleScore_integrable θ hθ i j k
  have h2 : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ k ω *
      M.scorePartial θ i j ω * M.density θ ω) M.refMeasure :=
    M.score_scorePartial_integrable θ hθ k i j
  have h3 : Integrable (fun ω =>
      M.toRegularStatisticalModel.score θ j ω *
      M.scorePartial θ i k ω * M.density θ ω) M.refMeasure :=
    M.score_scorePartial_integrable θ hθ j i k
  have hsplit : (fun ω =>
      (M.toRegularStatisticalModel.score θ i ω *
        M.toRegularStatisticalModel.score θ j ω *
        M.toRegularStatisticalModel.score θ k ω +
      M.toRegularStatisticalModel.score θ k ω *
        M.scorePartial θ i j ω +
      M.toRegularStatisticalModel.score θ j ω *
        M.scorePartial θ i k ω) * M.density θ ω) =
      fun ω =>
        (M.toRegularStatisticalModel.score θ i ω *
          M.toRegularStatisticalModel.score θ j ω *
          M.toRegularStatisticalModel.score θ k ω *
          M.density θ ω +
        M.toRegularStatisticalModel.score θ k ω *
          M.scorePartial θ i j ω * M.density θ ω) +
        M.toRegularStatisticalModel.score θ j ω *
          M.scorePartial θ i k ω * M.density θ ω := by
    funext ω; ring
  rw [hsplit]
  erw [integral_add (h1.add h2) h3, integral_add h1 h2]
  rfl

/-- `∂ᵢ g_{jk}(θ) = C_{ijk} + Γᵐ_{ij,k} + Γᵐ_{ik,j}` as a statement
about the canonical `fderiv`. -/
lemma fisherMatrix_fderiv_single {θ : ParamSpace n}
    (hθ : θ ∈ M.paramDomain) (i j k : Fin n) :
    fderiv ℝ (fun θ' => M.toRegularStatisticalModel.fisherMatrix θ' j k) θ
      (EuclideanSpace.single i 1) =
    M.cubicTensor θ i j k + M.mConnectionCoeff θ i j k +
    M.mConnectionCoeff θ i k j := by
  obtain ⟨L, hL, hL_eval⟩ := M.fisherMatrix_hasFDerivAt' hθ j k
  rw [hL.fderiv]
  exact hL_eval i

-- ════════════════════════════════════════════════════════════════════
-- §5. The third KL derivative at the diagonal
-- ════════════════════════════════════════════════════════════════════

/-- **Componentwise diagonal third derivative.**  At any diagonal point
`β` of the domain,

  `∂ᵢ∂ⱼ∂ₖ D(β‖·)|_β = C_{ijk} + Γᵐ_{ik,j} + Γᵐ_{jk,i} + Γᵐ_{ij,k}`.

This packages `klDiv_third_partial` and
`klDiv_third_deriv_decomposition` with all hypotheses discharged from
the `ThriceDifferentiableModel` fields and the Bartlett identities. -/
lemma klDiv_third_deriv_eval {β : ParamSpace n} (hβ : β ∈ M.paramDomain)
    (i j k : Fin n) :
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) θ₁
        (EuclideanSpace.single j 1)) β (EuclideanSpace.single i 1) =
    M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
    M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k := by
  -- the second partial agrees near β with the scorePartial integral
  have h_ev2 : ∀ᶠ θ' in 𝓝 β,
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) θ'
        (EuclideanSpace.single j 1) =
      -∫ ω, M.density β ω * M.scorePartial θ' j k ω ∂M.refMeasure := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hβ] with θ' hθ'
    obtain ⟨g₁, hg₁, hg₁_eval⟩ := M.cross_score_hasFDerivAt' hβ hθ' k
    have hg₁' : HasFDerivAt (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) g₁ θ' :=
      hg₁.congr_of_eventuallyEq (by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ'] with θ₂ hθ₂
        exact M.klDiv_partial_j hβ hθ₂ k)
    rw [hg₁'.fderiv]
    exact hg₁_eval j
  -- the third Leibniz interchange at β
  obtain ⟨g₂, hg₂, _⟩ := M.klDiv_third_partial hβ j k
    (M.scorePartial_fderiv_bound β hβ β hβ j k)
    (M.scorePartial_density_integrable β hβ j k)
    (M.scorePartial_deriv_aestronglyMeasurable β hβ j k)
    (M.scorePartial_density_aestronglyMeasurable β hβ j k)
  have hg₂' : HasFDerivAt (fun θ' =>
      fderiv ℝ (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) θ'
        (EuclideanSpace.single j 1)) g₂ β :=
    hg₂.congr_of_eventuallyEq h_ev2
  rw [hg₂'.fderiv]
  exact M.klDiv_third_deriv_decomposition hβ i j k
    (fun j' k' => M.klDiv_third_partial hβ j' k'
      (M.scorePartial_fderiv_bound β hβ β hβ j' k')
      (M.scorePartial_density_integrable β hβ j' k')
      (M.scorePartial_deriv_aestronglyMeasurable β hβ j' k')
      (M.scorePartial_density_aestronglyMeasurable β hβ j' k'))
    (fun i' j' k' => M.bartlett_third hβ i' j' k')
    h_ev2
    (M.scorePartial_deriv_integrable β hβ i j k)
    (M.score_scorePartial_integrable β hβ j i k)
    (M.score_scorePartial_integrable β hβ i j k)
    (M.score_scorePartial_integrable β hβ k i j)
    (M.tripleScore_integrable β hβ i j k)
    g₂ hg₂'

/-- **Trilinear diagonal third derivative.**  The third Fréchet
derivative of `D(β‖·)` at `β` is the trilinear form whose entries are
given by `klDiv_third_deriv_eval`:

  `D'''(β‖·)(β)[x, y, z]
     = ∑ᵢⱼₖ xᵢ yⱼ zₖ (C_{ijk} + Γᵐ_{ik,j} + Γᵐ_{jk,i} + Γᵐ_{ij,k})`. -/
lemma klDiv_third_deriv_trilin {β : ParamSpace n} (hβ : β ∈ M.paramDomain)
    (x y z : ParamSpace n) :
    fderiv ℝ (fun θ₁ =>
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂ z) θ₁ y) β x =
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      x i * y j * z k *
        (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
         M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) := by
  -- derivative data for the scalar second partials at every domain point
  have hS : ∀ θ₁ ∈ M.paramDomain, ∀ k : Fin n,
      ∃ g : ParamSpace n →L[ℝ] ℝ,
        HasFDerivAt (fun θ₂ =>
          fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) g θ₁ := by
    intro θ₁ hθ₁ k
    obtain ⟨g₁, hg₁, _⟩ := M.cross_score_hasFDerivAt' hβ hθ₁ k
    exact ⟨g₁, hg₁.congr_of_eventuallyEq (by
      filter_upwards [M.isOpen_paramDomain.mem_nhds hθ₁] with θ₂ hθ₂
      exact M.klDiv_partial_j hβ hθ₂ k)⟩
  -- (i) innermost slot: expand z over the basis (pointwise CLM linearity)
  have hz : (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂ z) =
      fun θ₂ => ∑ k : Fin n, z.ofLp k *
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1) := by
    funext θ₂
    conv_lhs => rw [paramSpace_eq_sum_single z]
    rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
  -- (ii) middle slot: differentiate the k-sum on the domain, expand y
  have h_mid : ∀ θ₁ ∈ M.paramDomain,
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂ z) θ₁ y =
      ∑ k : Fin n, ∑ j : Fin n, z.ofLp k * y.ofLp j *
        fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂
          (EuclideanSpace.single k 1)) θ₁ (EuclideanSpace.single j 1) := by
    intro θ₁ hθ₁
    rw [hz]
    have hsum : HasFDerivAt (fun θ₂ => ∑ k : Fin n, z.ofLp k *
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1))
        (∑ k : Fin n, z.ofLp k • (hS θ₁ hθ₁ k).choose) θ₁ :=
      HasFDerivAt.fun_sum fun k _ =>
        ((hS θ₁ hθ₁ k).choose_spec).const_mul (z.ofLp k)
    rw [hsum.fderiv]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ((hS θ₁ hθ₁ k).choose_spec).fderiv]
    conv_lhs => rw [paramSpace_eq_sum_single y]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- (iii) outermost slot
  have h_mid_ev : (fun θ₁ => fderiv ℝ (fun θ₂ =>
      fderiv ℝ (M.klDiv β) θ₂ z) θ₁ y) =ᶠ[𝓝 β]
      (fun θ₁ => ∑ k : Fin n, ∑ j : Fin n, z.ofLp k * y.ofLp j *
        fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂
          (EuclideanSpace.single k 1)) θ₁ (EuclideanSpace.single j 1)) := by
    filter_upwards [M.isOpen_paramDomain.mem_nhds hβ] with θ₁ hθ₁
    exact h_mid θ₁ hθ₁
  rw [DFunLike.congr_fun h_mid_ev.fderiv_eq x]
  -- derivative data for the scalar third partials at β
  have hT : ∀ j k : Fin n,
      ∃ g₂ : ParamSpace n →L[ℝ] ℝ,
        HasFDerivAt (fun θ₁ =>
          fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂
            (EuclideanSpace.single k 1)) θ₁
            (EuclideanSpace.single j 1)) g₂ β := by
    intro j k
    obtain ⟨g₂, hg₂, _⟩ := M.klDiv_third_partial hβ j k
      (M.scorePartial_fderiv_bound β hβ β hβ j k)
      (M.scorePartial_density_integrable β hβ j k)
      (M.scorePartial_deriv_aestronglyMeasurable β hβ j k)
      (M.scorePartial_density_aestronglyMeasurable β hβ j k)
    refine ⟨g₂, hg₂.congr_of_eventuallyEq ?_⟩
    filter_upwards [M.isOpen_paramDomain.mem_nhds hβ] with θ' hθ'
    obtain ⟨g₁, hg₁, hg₁_eval⟩ := M.cross_score_hasFDerivAt' hβ hθ' k
    have hg₁' : HasFDerivAt (fun θ₂ =>
        fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) g₁ θ' :=
      hg₁.congr_of_eventuallyEq (by
        filter_upwards [M.isOpen_paramDomain.mem_nhds hθ'] with θ₂ hθ₂
        exact M.klDiv_partial_j hβ hθ₂ k)
    rw [hg₁'.fderiv]
    exact hg₁_eval j
  have hsum2 : HasFDerivAt (fun θ₁ => ∑ k : Fin n, ∑ j : Fin n,
      z.ofLp k * y.ofLp j *
      fderiv ℝ (fun θ₂ => fderiv ℝ (M.klDiv β) θ₂
        (EuclideanSpace.single k 1)) θ₁ (EuclideanSpace.single j 1))
      (∑ k : Fin n, ∑ j : Fin n,
        (z.ofLp k * y.ofLp j) • (hT j k).choose) β :=
    HasFDerivAt.fun_sum fun k _ => HasFDerivAt.fun_sum fun j _ =>
      ((hT j k).choose_spec).const_mul (z.ofLp k * y.ofLp j)
  rw [hsum2.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  -- evaluate each (hT j k).choose at x componentwise
  have hT_eval : ∀ j k : Fin n, (hT j k).choose x =
      ∑ i : Fin n, x.ofLp i *
        (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
         M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) := by
    intro j k
    conv_lhs => rw [paramSpace_eq_sum_single x]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [show (hT j k).choose (EuclideanSpace.single i 1) =
        fderiv ℝ (fun θ₁ => fderiv ℝ (fun θ₂ =>
          fderiv ℝ (M.klDiv β) θ₂ (EuclideanSpace.single k 1)) θ₁
          (EuclideanSpace.single j 1)) β (EuclideanSpace.single i 1) from by
      rw [((hT j k).choose_spec).fderiv]]
    exact M.klDiv_third_deriv_eval hβ i j k
  -- assemble and reorder (k, j, i) → (i, j, k)
  calc (∑ k : Fin n, ∑ j : Fin n,
        z.ofLp k * y.ofLp j * (hT j k).choose x)
      = ∑ k : Fin n, ∑ j : Fin n, ∑ i : Fin n,
          x.ofLp i * y.ofLp j * z.ofLp k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hT_eval j k, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
          x.ofLp i * y.ofLp j * z.ofLp k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) :=
        Finset.sum_comm
    _ = ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
          x.ofLp i * y.ofLp j * z.ofLp k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          x.ofLp i * y.ofLp j * z.ofLp k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) :=
        Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          x i * y j * z k *
          (M.cubicTensor β i j k + M.mConnectionCoeff β i k j +
           M.mConnectionCoeff β j k i + M.mConnectionCoeff β i j k) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by ring

end ThriceDifferentiableModel

end Spectra.InformationGeometry

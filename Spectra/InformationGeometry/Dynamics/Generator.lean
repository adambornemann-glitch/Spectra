/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: InformationGeometry/Dynamics/Generator.lean
-/
import LogosLibrary.InformationGeometry.Dynamics.PreservesCubic
/-!
# Infinitesimal Generator and Flow Equation

The infinitesimal generator of a divergence-preserving family is a
vector field on the parameter space — the analogue of Stone's generator
A defined by Aψ = lim_{t→0} (it)⁻¹(U(t)ψ - ψ).

Differentiating the structure-preservation laws of the family yields
the infinitesimal conditions:

  L_X g = 0     (Killing equation — Fisher metric is infinitesimally preserved)
  L_X C = 0     (cubic tensor is infinitesimally preserved)

The family is recovered from its generator by the flow equation

  d/dt φ_t(θ) = X(φ_t(θ))

— the information-geometric analogue of dψ/dt = iAψ.

## Main results

* `generator` — the infinitesimal generator X(θ) = d/dt φ_t(θ)|_{t=0}
* `generator_killing` — infinitesimal Fisher preservation
* `generator_preserves_cubic` — infinitesimal cubic preservation
* `flow_equation` — autonomous ODE satisfied by the family
-/

noncomputable section

namespace InformationGeometry

open MeasureTheory Finset Filter Topology TopologicalSpace

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

namespace TwiceDifferentiableModel.DivergencePreservingFamily

variable {M : TwiceDifferentiableModel n Ω}
variable (F : M.DivergencePreservingFamily)

-- ============================================================================
-- §4b. The infinitesimal generator
-- ============================================================================

/-- The **infinitesimal generator** of a divergence-preserving family:
  X(θ) = d/dt φ_t(θ) |_{t=0}

This is a vector field on the parameter space — the analogue of Stone's
generator A defined by Aψ = lim_{t→0} (it)⁻¹(U(t)ψ - ψ). -/
noncomputable def generator (θ : ParamSpace n) : ParamSpace n :=
  fderiv ℝ (fun t => F.φ t θ) 0 1

/-- The generator is well-defined (the derivative exists). -/
lemma generator_exists (θ : ParamSpace n) :
    DifferentiableAt ℝ (fun t => F.φ t θ) 0 := by
  show DifferentiableAt ℝ (Function.uncurry F.φ ∘ (fun t => (t, θ))) 0
  exact DifferentiableAt.comp 0
    ((F.smooth.differentiable (by simp)).differentiableAt)
    (DifferentiableAt.prodMk differentiableAt_id (differentiableAt_const θ))

/-- The generator satisfies the Killing equation L_X g = 0.

This is the infinitesimal form of `preserves_fisher`: differentiating
g(dφ_t · v, dφ_t · w) = g(v, w) in t at t = 0 gives the Killing
equation. -/
lemma generator_killing {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) :
    ∀ v w : ParamSpace n,
    fderiv ℝ (fun t =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ v) (fderiv ℝ (F.φ t) θ w)) 0 1 = 0 := by
  intro v w
  have hconst : (fun t => M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
      (fderiv ℝ (F.φ t) θ v) (fderiv ℝ (F.φ t) θ w)) =
    fun _ => M.toRegularStatisticalModel.fisherBilin θ v w := by
    ext t; exact F.preserves_fisher hθ t v w
  rw [hconst]
  simp [ContinuousLinearMap.zero_apply]

/-- The generator preserves the cubic tensor: L_X C = 0.

Infinitesimal form of `preserves_cubic`. -/
lemma generator_preserves_cubic
    (M₃ : ThriceDifferentiableModel n Ω)
    (hM₃ : M₃.toTwiceDifferentiableModel = M)
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) :
    ∀ u v w : ParamSpace n,
    fderiv ℝ (fun t =>
      M.cubicTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ u) (fderiv ℝ (F.φ t) θ v)
        (fderiv ℝ (F.φ t) θ w)) 0 1 = 0 := by
  intro u v w
  have hconst : (fun t =>
      M.cubicTrilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ u) (fderiv ℝ (F.φ t) θ v)
        (fderiv ℝ (F.φ t) θ w)) =
    fun _ => M.cubicTrilin θ u v w := by
    ext t
    exact preserves_cubic M F M₃ hM₃ hθ t u v w
  rw [hconst]
  simp [ContinuousLinearMap.zero_apply]

-- ============================================================================
-- §4c. Recovery: the flow from the generator
-- ============================================================================

/-- The family is recovered from its generator by the flow equation:
  d/dt φ_t(θ) = X(φ_t(θ))

This is the ODE that the generator satisfies — the analogue of
the Schrödinger equation dψ/dt = iAψ. -/
lemma flow_equation (θ : ParamSpace n) (t : ℝ) :
    fderiv ℝ (fun s => F.φ s θ) t 1 = F.generator (F.φ t θ) := by
  -- ── Step 1: HasDerivAt at 0 for the trajectory starting at φ_t(θ) ──
  have h₀ : HasDerivAt (fun u => F.φ u (F.φ t θ)) (F.generator (F.φ t θ)) 0 :=
    (F.generator_exists (F.φ t θ)).hasFDerivAt.hasDerivAt
  -- ── Step 2: Group law identifies the trajectories ──
  have h_eq : (fun s => F.φ s θ) = (fun s => F.φ (s - t) (F.φ t θ)) := by
    ext s; rw [← F.group_law (s - t) t θ, sub_add_cancel]
  -- ── Step 3: Chain rule shifts derivative from 0 to t ──
  set g := fun u => F.φ u (F.φ t θ)
  set f := fun s : ℝ => s - t
  have hg : HasFDerivAt g
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F.generator (F.φ t θ)))
      (f t) := by
    simp only [f, sub_self]; exact h₀.hasFDerivAt
  have hf : HasFDerivAt f (ContinuousLinearMap.id ℝ ℝ) t :=
    hasFDerivAt_sub_const t
  have h_comp := hg.comp t hf
  rw [ContinuousLinearMap.comp_id] at h_comp
  -- ── Step 4: Extract fderiv and evaluate at 1 ──
  rw [h_eq, show (fun s => F.φ (s - t) (F.φ t θ)) = g ∘ f from rfl,
      h_comp.fderiv, ContinuousLinearMap.smulRight_apply]
  simp

/-
  Strategy: Specialize generator_killing to v = eᵢ, w = eⱼ.
  This gives d/dt|₀ [g_{ab}(φ_t θ) · (dφ_t·eᵢ)_a · (dφ_t·eⱼ)_b] = 0.

  Expand via the product/chain rule. At t = 0:
  - φ_0(θ) = θ, so dφ_0 = id
  - d/dt|₀ φ_t(θ) = X(θ) (the generator)
  - d/dt|₀ (dφ_t · eᵢ)_a = (dX · eᵢ)_a = fderiv(X)(θ)(eᵢ)_a

  The three terms of the product rule give exactly the three terms in
  the Killing sum.
-/

/-- Component expansion: the coordinate-free derivative equals the
Killing sum. Requires product + chain rule. -/
private lemma killing_expansion (F : M.DivergencePreservingFamily)
    {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (i j : Fin n) :
    fderiv ℝ (fun t =>
      M.toRegularStatisticalModel.fisherBilin (F.φ t θ)
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single i 1))
        (fderiv ℝ (F.φ t) θ (EuclideanSpace.single j 1))) 0 1 =
    ∑ k : Fin n,
      F.generator θ k *
        fderiv ℝ (fun θ' =>
          M.toRegularStatisticalModel.fisherMatrix θ' i j) θ
          (EuclideanSpace.single k 1) +
      M.toRegularStatisticalModel.fisherMatrix θ k j *
        fderiv ℝ (fun θ' => F.generator θ' k) θ
          (EuclideanSpace.single i 1) +
      M.toRegularStatisticalModel.fisherMatrix θ i k *
        fderiv ℝ (fun θ' => F.generator θ' k) θ
          (EuclideanSpace.single j 1) := by
  -- t ↦ ∑_{a,b} g_{ab}(φ_t θ) · (dφ_t·eᵢ)_a · (dφ_t·eⱼ)_b — a finite
  -- sum of products of smooth functions of t. Product rule + chain
  -- rule, then evaluate at t = 0 where φ₀ = id.
  --
  -- Term 1: ∑_k X^k ∂_k g_{ij}   (from g_{ab}(φ_t θ))
  -- Term 2: ∑_k g_{kj} ∂_i X^k   (from (dφ_t·eᵢ)_k)
  -- Term 3: ∑_k g_{ik} ∂_j X^k   (from (dφ_t·eⱼ)_k)
  --
  -- At t = 0: (dφ_0·eᵢ)_a = δ_{ai}, so only a = i survives in Term 1.
  sorry

end TwiceDifferentiableModel.DivergencePreservingFamily

end InformationGeometry

end

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Quantum.Manifold

/-!
# The quantum score: tangent vectors and the vanishing first moment

On a `QuantumStatisticalModel`, the parameter-derivative `∂ᵢ ρ_θ` of the state is a trace-class
operator — the **mixture-representation (m-) tangent vector** of the model at `θ`. This is the
operator analogue of the classical score's role: differentiating the family along a coordinate.

The central lemma here is the operator lift of `score_expectation_eq_zero` (`E_θ[s_i] = 0`):

> **`traceCLM_deriv_eq_zero`** — every tangent vector is **traceless**, `tr(∂ᵢ ρ_θ) = 0`.

It is the infinitesimal shadow of the normalization constraint `tr ρ_θ ≡ 1`: differentiating the
constant map `θ ↦ tr ρ_θ = 1` kills the trace of the derivative. This is the first genuinely
*geometric* fact of the quantum information-geometric second view — the tangent space at a state is
the space of traceless self-adjoint trace-class operators.

## Main definitions

* `QuantumStatisticalModel.deriv M θ i` — the `i`-th tangent vector `∂ᵢ ρ_θ ∈ TraceClass H`.

## Main results

* `QuantumStatisticalModel.traceCLM_deriv_eq_zero` — the tangent vectors are traceless.
-/

namespace Spectra.InformationGeometry.Quantum

open Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace QuantumStatisticalModel

variable {n : ℕ} (M : QuantumStatisticalModel n H)

/-- The **differential** `dρ_θ : ParamSpace n →L[ℝ] TraceClass H` of the model at `θ` — the bundled
tangent map sending a parameter direction to the corresponding tangent vector
(`m`-representation). -/
noncomputable def differential (θ : ParamSpace n) : ParamSpace n →L[ℝ] TraceClass H :=
  fderivWithin ℝ (fun θ' => (M.ρ θ').toTraceClass) M.paramDomain θ

/-- The **`i`-th tangent vector** `∂ᵢ ρ_θ` of the model at a parameter `θ`, a trace-class operator —
the mixture-representation (m-) tangent of the family in the `i`-th coordinate direction. -/
noncomputable def deriv (θ : ParamSpace n) (i : Fin n) : TraceClass H :=
  M.differential θ (EuclideanSpace.single i 1)

lemma deriv_eq_differential (θ : ParamSpace n) (i : Fin n) :
    M.deriv θ i = M.differential θ (EuclideanSpace.single i 1) := rfl

/-- **The quantum score has vanishing first moment, in every tangent direction**: for each parameter
direction `v`, the tangent vector `dρ_θ(v)` is traceless, `tr(dρ_θ(v)) = 0`. This is the operator
analogue of `score_expectation_eq_zero`, and the infinitesimal form of trace preservation
`tr ρ_θ ≡ 1`. Consequently the tangent space at `ρ_θ` lies in the kernel of the trace functional —
it is (contained in) the space of traceless trace-class operators. -/
theorem traceCLM_differential_eq_zero {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain)
    (v : ParamSpace n) : traceCLM (M.differential θ v) = 0 := by
  -- the state family, as a trace-norm-valued curve, is differentiable within the (open) domain
  have hfw : HasFDerivWithinAt (fun θ' => (M.ρ θ').toTraceClass)
      (fderivWithin ℝ (fun θ' => (M.ρ θ').toTraceClass) M.paramDomain θ) M.paramDomain θ :=
    (M.smooth.differentiableOn (by simp) θ hθ).hasFDerivWithinAt
  have hu : UniqueDiffWithinAt ℝ M.paramDomain θ := M.isOpen_paramDomain.uniqueDiffWithinAt hθ
  -- push the derivative through the (ℝ-linearised) trace functional
  set L : TraceClass H →L[ℝ] ℂ := traceCLM.restrictScalars ℝ with _hL
  have h1 : HasFDerivWithinAt (fun θ' => L ((M.ρ θ').toTraceClass))
      (L.comp (fderivWithin ℝ (fun θ' => (M.ρ θ').toTraceClass) M.paramDomain θ)) M.paramDomain θ :=
    L.hasFDerivAt.comp_hasFDerivWithinAt θ hfw
  -- but `θ ↦ tr ρ_θ ≡ 1`, so that same composite has derivative `0`
  have hEq : (fun θ' => L ((M.ρ θ').toTraceClass))
      =ᶠ[nhdsWithin θ M.paramDomain] fun _ => (1 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with y _hy
    change trace ((M.ρ y).toTraceClass).toOp = 1
    exact (M.ρ y).trace_one
  have h2 : HasFDerivWithinAt (fun θ' => L ((M.ρ θ').toTraceClass))
      (0 : ParamSpace n →L[ℝ] ℂ) M.paramDomain θ :=
    (hasFDerivWithinAt_const (1 : ℂ) θ M.paramDomain).congr_of_eventuallyEq hEq
      (by change trace ((M.ρ θ).toTraceClass).toOp = 1; exact (M.ρ θ).trace_one)
  -- uniqueness of the derivative on an open set forces `L ∘ dρ = 0`
  have hzero := hu.eq h1 h2
  have happ := DFunLike.congr_fun hzero v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at happ
  exact happ

/-- **The coordinate tangent vectors are traceless**, `tr(∂ᵢ ρ_θ) = 0` — the coordinate form of
`traceCLM_differential_eq_zero`. -/
lemma traceCLM_deriv_eq_zero {θ : ParamSpace n} (hθ : θ ∈ M.paramDomain) (i : Fin n) :
    traceCLM (M.deriv θ i) = 0 :=
  M.traceCLM_differential_eq_zero hθ _

end QuantumStatisticalModel

end Spectra.InformationGeometry.Quantum

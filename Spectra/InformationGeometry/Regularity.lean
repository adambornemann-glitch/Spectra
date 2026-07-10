/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.StatisticalManifold
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
/-!
# Higher-Order Regularity for Statistical Models

This file defines the regularity classes used throughout the connection,
divergence, and flow theory of `InformationGeometry`:

* `TwiceDifferentiableModel` — extends `RegularStatisticalModel` with
  second-order differentiability, dominating bounds for the second
  Leibniz rule, and entropy/cross-entropy integrability. This is the
  regularity needed for the Hessian theorem ∂²D = g.

* `ThriceDifferentiableModel` — extends with third-order data:
  thrice-differentiability, third-derivative bounds, and the various
  integrability/measurability hypotheses needed for the Bartlett-3
  identity and the cubic tensor decomposition.

The convention `scorePartial θ a b ω = ∂ₐsᵦ(θ, ω)` is defined here
because `ThriceDifferentiableModel`'s field types refer to it; its
richer use lives with the cubic-tensor material downstream.

## Design Note

These structures carry a long list of integrability/measurability
hypotheses as fields. Many of these are morally derivable from the
core `density_*_diff` and `*DerivBound` data, but the derivations are
nontrivial and currently bundled as axioms for tractability. A future
refactor could prove them as lemmas.
-/
open MeasureTheory Filter Topology

namespace Spectra.InformationGeometry

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- **Locally dominated parameter derivative under the integral.**

Shared quantifier shape for the Leibniz-rule domination hypotheses of this
file: near `θ₀` there is a radius `ε` and an integrable dominating function
`bound` such that, for a.e. `ω`, the integrand family `F ω` is Fréchet
differentiable at every `θ' ∈ Metric.ball θ₀ ε` with derivative `F' ω θ'`,
and that derivative's norm is controlled by `bound ω` uniformly in `θ'`.

This is the common pattern behind `crossEntropy_fderiv_bound`,
`score_fderiv_bound`, and `scorePartial_fderiv_bound` (which instantiate `F`
and `F'` with the cross-entropy, score, and `scorePartial` integrands
respectively) and, at third order, `scorePartial_fderiv_bound` on
`ThriceDifferentiableModel`. -/
def LocallyDominatedFDeriv (μ : Measure Ω) (θ₀ : ParamSpace n)
    (F : Ω → ParamSpace n → ℝ) (F' : Ω → ParamSpace n → ParamSpace n →L[ℝ] ℝ) : Prop :=
  ∃ ε > 0, ∃ bound : Ω → ℝ, Integrable bound μ ∧
    (∀ᵐ ω ∂μ, ∀ θ' ∈ Metric.ball θ₀ ε,
      HasFDerivAt (F ω) (F' ω θ') θ' ∧ ‖F' ω θ'‖ ≤ bound ω)

-- ============================================================================
-- TwiceDifferentiableModel
-- ============================================================================

/-- A `RegularStatisticalModel` with second-order regularity.

This extends the first-order derivative bounds with:
- Twice differentiability of the density in the parameter
- Second-derivative domination for interchange of ∂² and ∫
- Second-derivative integrability conditions

These are needed for the Hessian theorem (∂²D = g) and cubic tensor. -/
structure TwiceDifferentiableModel (n : ℕ) (Ω : Type*) [MeasurableSpace Ω]
    extends RegularStatisticalModel n Ω where
  /-- The density is twice differentiable in θ at every point of the domain. -/
  density_twice_diff : ∀ ω, ContDiffOn ℝ 2 (fun θ' => density θ' ω) paramDomain
  /-- Dominating function for second derivatives.
  Needed for Leibniz rule: ∂²/∂θⁱ∂θʲ ∫ f(θ,ω) dμ = ∫ ∂²f/∂θⁱ∂θʲ dμ. -/
  secondDerivBound : Ω → ℝ
  secondDerivBound_integrable : Integrable secondDerivBound refMeasure
  secondDerivBound_nonneg : ∀ ω, 0 ≤ secondDerivBound ω
  /-- The second Fréchet derivative of the density is bounded by the
  dominating function, uniformly in θ. -/
  density_fderiv2_norm_le : ∀ θ ∈ paramDomain, ∀ ω,
    ‖iteratedFDeriv ℝ 2 (fun θ' => density θ' ω) θ‖ ≤ secondDerivBound ω
  /-- The log-density is twice differentiable where the density is positive. -/
  logDensity_twice_diff : ∀ θ ∈ paramDomain, ∀ᵐ ω ∂refMeasure,
    0 < density θ ω →
    ContDiffAt ℝ 2 (fun θ' => Real.log (density θ' ω)) θ
  /-- The entropy is finite: ∫ |p(ω;θ) log p(ω;θ)| dμ < ∞. -/
  entropy_integrable : ∀ θ ∈ paramDomain,
    Integrable (fun ω => density θ ω * Real.log (density θ ω)) refMeasure
  /-- The cross-entropy is finite: ∫ |p(ω;θ) log p(ω;θ')| dμ < ∞. -/
  crossEntropy_integrable : ∀ θ ∈ paramDomain, ∀ θ' ∈ paramDomain,
    Integrable (fun ω => density θ ω * Real.log (density θ' ω)) refMeasure
  /-- Local lower bound on density ratio: near any θ₀, the density doesn't
  collapse to zero faster than an integrable rate. This is needed for
  the Leibniz rule on log-density. -/
  crossEntropy_fderiv_bound : ∀ θ ∈ paramDomain, ∀ θ₀ ∈ paramDomain,
    LocallyDominatedFDeriv refMeasure θ₀
      (fun ω θ'' => density θ ω * Real.log (density θ'' ω))
      (fun ω θ' => density θ ω • fderiv ℝ (fun θ'' => Real.log (density θ'' ω)) θ')
  /-- Domination for the derivative of the score, needed for the second
  Leibniz application (Hessian theorem). Same quantifier structure as
  crossEntropy_fderiv_bound. -/
  score_fderiv_bound : ∀ θ ∈ paramDomain, ∀ θ₀ ∈ paramDomain, ∀ j : Fin n,
    LocallyDominatedFDeriv refMeasure θ₀
      (fun ω θ'' => density θ ω * toRegularStatisticalModel.score θ'' j ω)
      (fun ω θ' => density θ ω •
        fderiv ℝ (fun θ'' => toRegularStatisticalModel.score θ'' j ω) θ')
  /-- The Fisher information is finite: score functions are square-integrable
  with respect to the model measure. This is needed for the Fisher metric
  to be a well-defined bilinear form, and follows from the existence of
  the Hessian of KL divergence. -/
  scoreSqIntegrable : ∀ θ ∈ paramDomain, toRegularStatisticalModel.ScoreSqIntegrableModel θ

namespace TwiceDifferentiableModel

variable (M : TwiceDifferentiableModel n Ω)

/-- The a-th partial derivative of the score sᵦ at θ:
  `scorePartial θ a b ω = (∂/∂θ'ᵃ) sᵦ(θ', ω)|_{θ'=θ}`.

**Argument-order convention**: `a` is the *differentiation direction*
(the coordinate the derivative is taken along) and `b` is the *score
component* being differentiated — i.e. `a` names ∂ₐ, `b` names sᵦ, matching
the field name order `scorePartial θ a b` ↔ `∂ₐsᵦ`. This is the "Hessian
of the log-likelihood" in the (a,b) direction, evaluated at parameter θ
and sample point ω. Defined here because `ThriceDifferentiableModel`'s
field types reference it. -/
noncomputable def scorePartial
    (θ : ParamSpace n) (a b : Fin n) (ω : Ω) : ℝ :=
  fderiv ℝ (fun θ' => M.toRegularStatisticalModel.score θ' b ω) θ
    (EuclideanSpace.single a 1)

end TwiceDifferentiableModel

-- ============================================================================
-- ThriceDifferentiableModel
-- ============================================================================

/-- A `TwiceDifferentiableModel` with third-order regularity.

Adds thrice differentiability, a third-derivative bound, and the
integrability/measurability hypotheses needed for the Bartlett-3
identity and the third-derivative decomposition of KL divergence
into cubic tensor plus m-connection terms. -/
structure ThriceDifferentiableModel (n : ℕ) (Ω : Type*) [MeasurableSpace Ω]
    extends TwiceDifferentiableModel n Ω where
  /-- The density is thrice differentiable in θ. -/
  density_thrice_diff : ∀ ω, ContDiffOn ℝ 3 (fun θ' => density θ' ω) paramDomain
  /-- Dominating function for third derivatives. -/
  thirdDerivBound : Ω → ℝ
  thirdDerivBound_integrable : Integrable thirdDerivBound refMeasure
  thirdDerivBound_nonneg : ∀ ω, 0 ≤ thirdDerivBound ω
  density_fderiv3_norm_le : ∀ θ ∈ paramDomain, ∀ ω,
    ‖iteratedFDeriv ℝ 3 (fun θ' => density θ' ω) θ‖ ≤ thirdDerivBound ω
  /-- The log-density is C³ where the density is positive. -/
  logDensity_thrice_diff : ∀ θ ∈ paramDomain, ∀ᵐ ω ∂refMeasure,
    0 < density θ ω →
    ContDiffAt ℝ 3 (fun θ' => Real.log (density θ' ω)) θ
  /-- Domination for the scorePartial derivative (third Leibniz). -/
  scorePartial_fderiv_bound : ∀ θ ∈ paramDomain, ∀ θ₀ ∈ paramDomain,
    ∀ j k : Fin n,
    LocallyDominatedFDeriv refMeasure θ₀
      (fun ω θ'' => density θ ω * toTwiceDifferentiableModel.scorePartial θ'' j k ω)
      (fun ω θ' => density θ ω •
        fderiv ℝ (fun θ'' => toTwiceDifferentiableModel.scorePartial θ'' j k ω) θ')
  /-- Score × scorePartial integrability. -/
  score_scorePartial_integrable : ∀ θ ∈ paramDomain,
    ∀ x y z : Fin n,
    Integrable (fun ω =>
      toRegularStatisticalModel.score θ x ω *
      toTwiceDifferentiableModel.scorePartial θ y z ω *
      density θ ω) refMeasure
  /-- Triple score integrability. -/
  tripleScore_integrable : ∀ θ ∈ paramDomain,
    ∀ i j k : Fin n,
    Integrable (fun ω =>
      toRegularStatisticalModel.score θ i ω *
      toRegularStatisticalModel.score θ j ω *
      toRegularStatisticalModel.score θ k ω *
      density θ ω) refMeasure
  /-- Derivative of scorePartial integrand integrability. -/
  scorePartial_deriv_integrable : ∀ θ ∈ paramDomain,
    ∀ i j k : Fin n,
    Integrable (fun ω =>
      fderiv ℝ (fun θ'' => toTwiceDifferentiableModel.scorePartial θ'' j k ω) θ
        (EuclideanSpace.single i 1) * density θ ω) refMeasure
  /-- The Bartlett-2 integrand is integrable (needed for bartlett_second
      and bartlett_third). -/
  bartlett2_integrable : ∀ θ ∈ paramDomain, ∀ j k : Fin n,
    Integrable (fun ω =>
      (toTwiceDifferentiableModel.scorePartial θ j k ω +
       toRegularStatisticalModel.score θ j ω *
       toRegularStatisticalModel.score θ k ω) *
      density θ ω) refMeasure
  /-- The density-weighted scorePartial derivative is a.e. strongly measurable. -/
  scorePartial_deriv_aestronglyMeasurable :
    ∀ θ ∈ paramDomain, ∀ j k : Fin n,
    AEStronglyMeasurable
      (fun ω => density θ ω •
        fderiv ℝ (fun θ'' =>
          toTwiceDifferentiableModel.scorePartial θ'' j k ω) θ)
      refMeasure
  /-- The density-weighted scorePartial is a.e. strongly measurable,
      uniformly near any point of paramDomain. -/
  scorePartial_density_aestronglyMeasurable :
    ∀ θ ∈ paramDomain, ∀ j k : Fin n,
    ∀ᶠ θ' in 𝓝 θ, AEStronglyMeasurable
      (fun ω => density θ ω *
        toTwiceDifferentiableModel.scorePartial θ' j k ω)
      refMeasure
  /-- The density-weighted `scorePartial` integrand `p(θ,·)·∂ⱼsₖ(θ,·)` is
      integrable. This is the standalone second-order integrability
      hypothesis feeding `bartlett2_integrable` and the Leibniz interchange
      fields below, as opposed to a derivative of that integrand. -/
  scorePartial_density_integrable :
    ∀ θ ∈ paramDomain, ∀ j k : Fin n,
    Integrable (fun ω => density θ ω *
      toTwiceDifferentiableModel.scorePartial θ j k ω) refMeasure
  /-- Leibniz interchange for differentiating the Bartlett-2 integral.
      The Bartlett-2 integrand (∂ⱼsₖ + sⱼsₖ)·p is Fréchet differentiable
      under the integral sign, and the eᵢ-component of the derivative
      equals the five-term Bartlett-3 integrand. -/
  bartlett2_hasFDerivAt : ∀ θ ∈ paramDomain, ∀ i j k : Fin n,
    ∃ L : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => ∫ ω, (toTwiceDifferentiableModel.scorePartial θ' j k ω +
          toRegularStatisticalModel.score θ' j ω *
          toRegularStatisticalModel.score θ' k ω) *
          density θ' ω ∂refMeasure) L θ ∧
      L (EuclideanSpace.single i 1) =
        ∫ ω, (fderiv ℝ (fun θ'' =>
              toTwiceDifferentiableModel.scorePartial θ'' j k ω) θ
              (EuclideanSpace.single i 1) +
           toRegularStatisticalModel.score θ j ω *
             toTwiceDifferentiableModel.scorePartial θ i k ω +
           toRegularStatisticalModel.score θ i ω *
             toTwiceDifferentiableModel.scorePartial θ j k ω +
           toRegularStatisticalModel.score θ k ω *
             toTwiceDifferentiableModel.scorePartial θ i j ω +
           toRegularStatisticalModel.score θ i ω *
             toRegularStatisticalModel.score θ j ω *
             toRegularStatisticalModel.score θ k ω) *
          density θ ω ∂refMeasure
  /-- Leibniz interchange for differentiating the Fisher matrix entries
      along the parameter: `θ' ↦ g_{jk}(θ')` is Fréchet differentiable at
      every domain point, and the `eᵢ`-component of its derivative is the
      "metric variation" integrand

        `∂ᵢ g_{jk}(θ) = ∫ (sᵢsⱼsₖ + sₖ·∂ᵢsⱼ + sⱼ·∂ᵢsₖ) p dμ`
                      `= C_{ijk} + Γᵐ_{ij,k} + Γᵐ_{ik,j}`.

      This is the live-density analogue of `bartlett2_hasFDerivAt` for the
      summand `sⱼsₖ·p` alone (the Bartlett-2 field only differentiates the
      *sum* `(∂ⱼsₖ + sⱼsₖ)·p`, whose derivative is 0, and so cannot
      separate the two pieces).  Same design rationale as the other
      interchange fields: morally derivable from `density_thrice_diff` +
      `thirdDerivBound`, bundled as a field for tractability. -/
  fisherMatrix_hasFDerivAt : ∀ θ ∈ paramDomain, ∀ j k : Fin n,
    ∃ L : ParamSpace n →L[ℝ] ℝ,
      HasFDerivAt
        (fun θ' => toRegularStatisticalModel.fisherMatrix θ' j k) L θ ∧
      ∀ i : Fin n,
        L (EuclideanSpace.single i 1) =
          ∫ ω, (toRegularStatisticalModel.score θ i ω *
                  toRegularStatisticalModel.score θ j ω *
                  toRegularStatisticalModel.score θ k ω +
                toRegularStatisticalModel.score θ k ω *
                  toTwiceDifferentiableModel.scorePartial θ i j ω +
                toRegularStatisticalModel.score θ j ω *
                  toTwiceDifferentiableModel.scorePartial θ i k ω) *
            density θ ω ∂refMeasure

end Spectra.InformationGeometry

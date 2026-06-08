/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Bochner/Basic.lean
-/
import Spectra.Bochner.GNS.Basic
import Spectra.Bochner.MeasureExists
/-!
# From GNS to Bochner: The Spectral Route

This file completes the existence direction of Bochner's theorem by
composing three deep results:

1. **GNS** (Completion.lean): A continuous positive definite function `f`
   gives a Hilbert space H, a strongly continuous unitary group U(t),
   and a cyclic vector ξ with `f(t) = ⟨ξ, U(t)ξ⟩`.

2. **Stone's theorem** (UnitaryEvo/Stone.lean): The unitary group U(t)
   has a self-adjoint generator A with `U(t) = exp(itA)`.

3. **Spectral theorem** (SpectralTheory/Cayley.lean): The self-adjoint
   operator A has a projection-valued measure E, giving
   `⟨U(t)ξ, ξ⟩ = ∫ e^{itλ} d⟨E(λ)ξ, ξ⟩`.

The representing measure is `μ(S) = ⟨E(S)ξ, ξ⟩`.

## The argument in four lines
f(t) = ⟨ξ, U(t)ξ⟩                       [GNS]
     = ⟨ξ, exp(itA)ξ⟩                   [Stone]
     = ∫ e^{itλ} d⟨E(λ)ξ, ξ⟩            [Spectral theorem]
     = ∫ e^{itλ} dμ(λ)                  [define μ := ⟨E(·)ξ, ξ⟩]

## Tags

Bochner's theorem, spectral theorem, Stone's theorem, GNS construction,
positive definite function, Fourier-Stieltjes transform
-/
open Complex MeasureTheory Filter Topology
open Spectra.Bochner.GNS
open Spectra.Fourier
namespace Spectra.Bochner

/-- **The Bochner measure via the spectral route.**
Given `f` continuous and positive definite:
1. GNS gives (H, U, ξ) with f(t) = ⟨ξ, U(t)ξ⟩
2. Stone gives self-adjoint A with U(t) = exp(itA)
3. Spectral theorem gives PVM E for A
4. Define μ(S) = ⟨E(S)ξ, ξ⟩
Then μ is a finite positive Borel measure with
  f(t) = ∫ e^{itλ} dμ(λ). -/
noncomputable def bochnerMeasureSpectral (f : ℝ → ℂ)
    (hf : IsContinuous f) : Measure ℝ := by
  let gns := gnsUnitaryConstruction hf
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  exact (spectral_scalar_measure_exists (toOneParameterUnitaryGroup gns)
    (gns_cyclic gns.toGNSData)).choose

/-- The Bochner measure is finite, with total mass f(0).re. -/
lemma bochnerMeasureSpectral_finite {f : ℝ → ℂ}
    (hf : IsContinuous f) :
    IsFiniteMeasure (bochnerMeasureSpectral f hf) := by
  let gns := gnsUnitaryConstruction hf
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  exact (spectral_scalar_measure_exists (toOneParameterUnitaryGroup gns)
    (gns_cyclic gns.toGNSData)).choose_spec.1

/-- **Bochner's theorem (Existence)**
Every continuous positive definite function on ℝ is the
Fourier-Stieltjes transform of a finite positive Borel measure.
The proof composes GNS, Stone, and the spectral theorem:
  f(t) = ⟨ξ, U(t)ξ⟩ = ⟨ξ, e^{itA}ξ⟩ = ∫ e^{itλ} dμ(λ). -/
lemma bochner_existence (f : ℝ → ℂ) (hf : IsContinuous f) :
    ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧
      ∀ t, f t = ∫ ω, exp (I * ↑ω * ↑t) ∂μ := by
  refine ⟨bochnerMeasureSpectral f hf, bochnerMeasureSpectral_finite hf, fun t => ?_⟩
  let gns := gnsUnitaryConstruction hf
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  rw [← gns_representation gns t]
  exact (spectral_scalar_measure_exists
    (toOneParameterUnitaryGroup gns) (gns_cyclic gns.toGNSData)).choose_spec.2 t

/-- **Bochner's Theorem (Complete).**
A function `f : ℝ → ℂ` is continuous and positive definite if and only
if it is the Fourier-Stieltjes transform of a unique finite positive
Borel measure on ℝ.  -/
theorem bochner_theorem (f : ℝ → ℂ) (hf : IsContinuous f) :
    ∃! (μ : Measure ℝ), IsFiniteMeasure μ ∧
      ∀ t, f t = ∫ ω, exp (I * ↑ω * ↑t) ∂μ := by
  obtain ⟨μ, hμ_fin, hμ_rep⟩ := bochner_existence f hf
  refine ⟨μ, ⟨hμ_fin, hμ_rep⟩, ?_⟩
  intro ν ⟨hν_fin, hν_rep⟩
  haveI := hμ_fin
  haveI := hν_fin
  exact (fourier_uniqueness μ ν
    (fun t => (hμ_rep t).symm.trans (hν_rep t))).symm

end Spectra.Bochner

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.ProjValMeasure.Basic
/-!
# Pushforward of a projection-valued measure under a measurable map

For a projection-valued measure `P : ProjValMeasure H` on the Borel sets of `ℝ` and a measurable
`φ : ℝ → ℝ`, the **pushforward** `P.map φ hφ` is the PVM whose projections precompose with the
preimage and whose diagonal scalar measures push forward:

* `(P.map φ hφ).proj B = P.proj (φ ⁻¹' B)`  (`map_proj`);
* `(P.map φ hφ).diag ξ = (P.diag ξ).map φ`  (`map_diag`).

This is the projection-valued **spectral-mapping** carrier: for a self-adjoint `A`, the spectral
measure of `f(A)` is `(spectralPVM A).map f`. It is the constructor that `ProjValMeasure` was
missing (there was previously no `map`/`comap`/pushforward on PVMs), and the load-bearing
prerequisite for the `s ↦ s²` spectral pushforward `E^{A²} = (·²)_* E^A` behind positive-square-root
uniqueness (Field-3 polar uniqueness). The PVM axioms transfer because preimage commutes with `∩`,
`ᶜ`, `univ`, `∅`, and `Measure.map φ` of a finite measure is finite.
-/

open MeasureTheory Complex
open scoped InnerProductSpace

namespace Spectra

namespace ProjValMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Pushforward of a PVM under a measurable map** `φ : ℝ → ℝ`: `proj` precomposes with the
preimage and `diag` pushes forward. See `map_proj`, `map_diag`. -/
noncomputable def map (P : ProjValMeasure H) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    ProjValMeasure H where
  proj B hB := P.proj (φ ⁻¹' B) (hφ hB)
  diag ξ := (P.diag ξ).map φ
  diag_finite ξ := by
    haveI := P.diag_finite ξ
    exact (P.diag ξ).isFiniteMeasure_map φ
  inner_proj B hB ξ := by
    rw [P.inner_proj (φ ⁻¹' B) (hφ hB) ξ, Measure.map_apply hφ hB]
  proj_univ := by
    show P.proj (φ ⁻¹' Set.univ) (hφ MeasurableSet.univ) = ContinuousLinearMap.id ℂ H
    rw [P.proj_congr Set.preimage_univ (hφ MeasurableSet.univ) MeasurableSet.univ]
    exact P.proj_univ
  proj_inter B₁ B₂ hB₁ hB₂ := by
    show P.proj (φ ⁻¹' B₁) (hφ hB₁) * P.proj (φ ⁻¹' B₂) (hφ hB₂)
      = P.proj (φ ⁻¹' (B₁ ∩ B₂)) (hφ (hB₁.inter hB₂))
    rw [P.proj_inter (φ ⁻¹' B₁) (φ ⁻¹' B₂) (hφ hB₁) (hφ hB₂)]
    exact P.proj_congr Set.preimage_inter.symm ((hφ hB₁).inter (hφ hB₂)) (hφ (hB₁.inter hB₂))

@[simp] lemma map_proj (P : ProjValMeasure H) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.map φ hφ).proj B hB = P.proj (φ ⁻¹' B) (hφ hB) := rfl

@[simp] lemma map_diag (P : ProjValMeasure H) (φ : ℝ → ℝ) (hφ : Measurable φ) (ξ : H) :
    (P.map φ hφ).diag ξ = (P.diag ξ).map φ := rfl

end ProjValMeasure

end Spectra

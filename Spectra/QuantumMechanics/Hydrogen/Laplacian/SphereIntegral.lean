/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Radial disintegration of the Lebesgue integral

Mathlib's `MeasureTheory.integral_fun_norm_addHaar` reduces `∫ f(‖x‖)` to a one-dimensional
radial integral, but only for **radial** integrands.  For the radial Fourier transform we need
the same disintegration for a *general* integrand `F`:

  `∫ x, F x = ∫_{S} (∫_{r>0} r^{n-1} F(r • ω) dr) dσ(ω)`,

where `σ = μ.toSphere` is the induced surface measure on the unit sphere.  This file proves that
generalisation, reusing `measurePreserving_homeomorphUnitSphereProd` (the measure-preserving
"polar coordinates" homeomorphism `{0}ᶜ ≃ₜ sphere × Ioi`).  It is the first brick toward the
angular reduction `∫_{S²} e^{−2πi r⟨ξ,ω⟩} dσ = 4π·sin(2πr‖ξ‖)/(2πr‖ξ‖)`.
-/

noncomputable section

open MeasureTheory Metric Set Module

namespace Spectra.SphereIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero point is recovered from its sphere×radius coordinates: `x = ‖x‖ • (x/‖x‖)`. -/
theorem coe_homeomorphUnitSphereProd (x : ({0}ᶜ : Set E)) :
    (x : E) = ((homeomorphUnitSphereProd E x).2 : ℝ) • ((homeomorphUnitSphereProd E x).1 : E) := by
  have hne : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr (mem_compl_singleton_iff.mp x.2)
  rw [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe, smul_smul,
    mul_inv_cancel₀ hne, one_smul]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Radial disintegration (product form).**  The Lebesgue integral over `E` equals the integral
over `sphere × Ioi` of `F(r • ω)` against the product of the surface measure `μ.toSphere` and the
`r^{n-1} dr` measure.  Unconditional (no integrability needed). -/
theorem integral_eq_integral_prod_toSphere (F : E → G) :
    ∫ x, F x ∂μ
      = ∫ p : (sphere (0 : E) 1) × (Ioi (0 : ℝ)),
          F ((p.2 : ℝ) • (p.1 : E))
            ∂(μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) := by
  rw [← μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _) (fun p => F ((p.2 : ℝ) • (p.1 : E)))]
  simp_rw [← coe_homeomorphUnitSphereProd]
  rw [integral_subtype_comap (measurableSet_singleton (0 : E)).compl F, restrict_compl_singleton]

/-- **Radial disintegration (iterated form).**  For integrable `F`,
`∫ x, F x = ∫_{ω ∈ sphere} (∫_{r>0} F(r • ω) ∂(r^{n-1}dr)) dσ(ω)`. -/
theorem integral_eq_integral_toSphere (F : E → G) (hF : Integrable F μ) :
    ∫ x, F x ∂μ
      = ∫ ω : sphere (0 : E) 1,
          (∫ r : Ioi (0 : ℝ), F ((r : ℝ) • (ω : E))
            ∂(Measure.volumeIoiPow (finrank ℝ E - 1))) ∂μ.toSphere := by
  rw [integral_eq_integral_prod_toSphere μ F, integral_prod]
  -- integrability of the disintegrated integrand on the product measure.
  rw [← μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
        (Homeomorph.measurableEmbedding _)]
  have hcomp : ((fun p : (sphere (0 : E) 1) × (Ioi (0 : ℝ)) => F ((p.2 : ℝ) • (p.1 : E)))
      ∘ (homeomorphUnitSphereProd E)) = F ∘ Subtype.val := by
    funext x; simp only [Function.comp_apply]; rw [← coe_homeomorphUnitSphereProd]
  rw [hcomp, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : E)).compl]
  exact hF.integrableOn

end Spectra.SphereIntegral

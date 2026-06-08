/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerTheorem/Borel/Identity/Basic.lean
-/
import Spectra.Bochner.Borel.Identity.CauchyVague

open Complex MeasureTheory Filter Topology
open Spectra.Resolvent
open Spectra.Fourier
open Spectra.Kernels
open Spectra.Herglotz
open Spectra.QuantumMechanics
open OneParameterUnitaryGroup
open scoped InnerProductSpace ENNReal ComplexConjugate
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

namespace Spectra.Bochner

/-- **The Borel-transform identity** For every `z` off the real
axis, `⟪ξ, R(z)ξ⟫ = ∫ (λ - z)⁻¹ d(borelMeasure U_grp ξ)(λ)`. -/
lemma m_eq_cauchy_transform
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) {z : ℂ} (hz : z.im ≠ 0) :
    ⟪ξ, resolvent z hz (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ
      = ∫ lambda, ((lambda : ℂ) - z)⁻¹ ∂(borelMeasure U_grp ξ) :=
  tendsto_nhds_unique
    (borel_cauchy_approx_tendsto U_grp ξ hz) (borel_cauchy_vague U_grp ξ hz)

end Spectra.Bochner

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/BochnerTheorem/Borel/Defs.lean
-/
import Spectra.SpectralTheory.FourierTransform.Identity

namespace QuantumMechanics.SpectralTheory

open Complex
open scoped InnerProductSpace
open Resolvent Bochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Poisson density of the diagonal resolvent:
`pε(λ) := (1/π)·Im⟪ξ, R(λ+iε)ξ⟫`. -/
noncomputable def borelDensity
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (lambda : ℝ) : ℝ :=
  let z : ℂ := ⟨lambda, ε⟩
  (1 / Real.pi) *
    (⟪ξ, resolvent z hε.ne'
        (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp)
        (range_minus_i_eq_top U_grp) ξ⟫_ℂ).im

end QuantumMechanics.SpectralTheory

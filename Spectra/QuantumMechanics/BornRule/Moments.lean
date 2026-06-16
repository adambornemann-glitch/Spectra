/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.PVM

open Spectra Spectra.ProjValMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.BornRule
open PVM
namespace Moments

/-! ## §2  Moments

The mean and variance of the outcome distribution, as functionals of the measure.  The
identities tying them to the operator (`⟪ψ, A ψ⟫`, the Robertson variance) live at the
observable level in §3–§4, because they require the operator behind the PVM. -/

/-- The **expectation value** `⟨A⟩_ψ`, defined as the mean of the Born measure.  (Finite
exactly when `ψ` lies in the domain of the operator whose PVM is `P`; see
`bornExpectation_eq_inner`.) -/
noncomputable def bornExpectation (P : ProjValMeasure H) (ψ : H) : ℝ :=
  ∫ s, s ∂(bornMeasure P ψ)

/-- The **variance** `(Δ_ψ A)²`, the second central moment of the Born measure. -/
noncomputable def bornVariance (P : ProjValMeasure H) (ψ : H) : ℝ :=
  ∫ s, (s - bornExpectation P ψ) ^ 2 ∂(bornMeasure P ψ)


end Moments
end Spectra.QuantumMechanics.BornRule

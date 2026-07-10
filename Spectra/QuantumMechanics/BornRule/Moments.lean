/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.PVM
/-!
# Moments of the Born Measure

## Main definitions

* `bornExpectation` — the mean of the Born measure, `⟨A⟩_ψ`.
* `bornVariance` — the second central moment of the Born measure, `(Δ_ψ A)²`.

## Implementation notes

Both are raw Bochner integrals against `bornMeasure P ψ`, not pushed-forward-measure moments
computed some other way — the direct definitions Mathlib's `MeasureTheory.integral` already knows
how to manipulate. Like any Bochner integral, each is a **junk value of `0`** when the integrand is
not integrable, which happens exactly when `ψ` is outside the domain of the operator whose PVM is
`P`; see `bornExpectation_eq_inner` and `bornVariance_eq_central_moment`
(both in `Observable.lean`) for the precise domain hypothesis and the operator-level identities
(`⟪ψ, A ψ⟫`, `‖(A − ⟨A⟩)ψ‖²`) these functionals turn out to equal.

`bornVariance` is defined as the raw second *central* moment
(`∫ (s - ⟨A⟩_ψ)² ∂μ`), not as the algebraically equivalent second-raw-moment-minus-mean-squared
(`∫ s² ∂μ - ⟨A⟩_ψ²`). Both are "the variance" in different textbooks, but they need different
integrability hypotheses in general (the raw-moment route needs `s ↦ s²` integrable, a strictly
stronger condition off `ψ ∈ D(A)` than what the central-moment route needs); the central-moment
definition is the one that matches `bornVariance_eq_central_moment`'s hypothesis exactly.

The identities tying these to the operator (`⟪ψ, A ψ⟫`, the Robertson variance) live at the
observable level in §3–§4 (`Observable.lean`, `Uncertainty.lean`), because they require the
operator behind the PVM, not just the PVM itself.

## References

See `PVM.lean`'s module docstring for the Born-rule references this section's arc builds on.
-/
open Spectra Spectra.ProjValMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.BornRule
open PVM
namespace Moments

/-! ## §2  Moments -/

/-- The **expectation value** `⟨A⟩_ψ`, defined as the mean of the Born measure. (Finite
exactly when `ψ` lies in the domain of the operator whose PVM is `P`; see
`bornExpectation_eq_inner`.) -/
noncomputable def bornExpectation (P : ProjValMeasure H) (ψ : H) : ℝ :=
  ∫ s, s ∂(bornMeasure P ψ)

/-- The **variance** `(Δ_ψ A)²`, the second central moment of the Born measure. (Finite
exactly when `ψ` lies in the domain of the operator whose PVM is `P`, the same hypothesis
`bornExpectation` needs; see `bornVariance_eq_central_moment`.) -/
noncomputable def bornVariance (P : ProjValMeasure H) (ψ : H) : ℝ :=
  ∫ s, (s - bornExpectation P ψ) ^ 2 ∂(bornMeasure P ψ)

end Moments
end Spectra.QuantumMechanics.BornRule

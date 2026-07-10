/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
/-!
# Fourier Uniqueness Theorem

A finite positive Borel measure on `ℝ` is determined by its characteristic function
`t ↦ ∫ exp(iωt) dμ(ω)`.

## Main results

* `fourier_uniqueness` — the uniqueness theorem.

## Implementation notes

This is Mathlib's `Measure.ext_of_charFun` — stated there for any complete, second-countable real
inner product space `E` — specialized to `E = ℝ` with the ordinary inner product
`⟪x, t⟫ = x * t`. The only proof content beyond the specialization is reorienting Mathlib's
character `exp(⟪x, t⟫ * I)` into this development's convention `exp(I * ω * t)`
(`character_orientation_eq`). The specialization to `ℝ` (rather than keeping the general `E`) is
deliberate, not an oversight: the sole call site, `Bochner/Basic.lean`'s `bochner_theorem`, is
scalar throughout, and a general-`E` statement would need to carry the extra inner-product-space
hypotheses through the whole Bochner pipeline for no consumer that needs them.

## References

* `Measure.ext_of_charFun` (`Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic`)
-/
open Complex MeasureTheory

namespace Spectra.Fourier

/-- **Fourier Uniqueness Theorem**: A finite positive Borel measure on ℝ is
    uniquely determined by its characteristic function. -/
theorem fourier_uniqueness (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ω * t) ∂μ = ∫ ω, exp (I * ω * t) ∂ν) : μ = ν := by
  apply Measure.ext_of_charFun
  funext t
  simp only [charFun_apply]
  have character_orientation_eq :
      ∀ x : ℝ, cexp ((↑(inner ℝ x t : ℝ) : ℂ) * I) = cexp (I * ↑x * ↑t) := by
    intro x
    simp only [RCLike.inner_apply, conj_trivial, ofReal_mul]
    ring_nf
  simp_rw [character_orientation_eq]
  exact h t

end Spectra.Fourier

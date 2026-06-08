/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Fourier/Unique.lean
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar

open Complex MeasureTheory Filter Topology Set

namespace Spectra.Fourier

/-! ## §7: The main theorem -/

/-- **Fourier Uniqueness Theorem**: A finite positive Borel measure on ℝ is
    uniquely determined by its characteristic function. -/
theorem fourier_uniqueness (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, ∫ ω, exp (I * ω * t) ∂μ = ∫ ω, exp (I * ω * t) ∂ν) : μ = ν := by
  apply Measure.ext_of_charFun
  funext t
  simp only [charFun_apply]
  have heq : ∀ x : ℝ, cexp ((↑(inner ℝ x t : ℝ) : ℂ) * I) = cexp (I * ↑x * ↑t) := by
    intro x
    simp only [RCLike.inner_apply, conj_trivial, ofReal_mul]
    ring_nf
  simp_rw [heq]
  exact h t

end Spectra.Fourier

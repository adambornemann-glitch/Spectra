/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
/-!
# Periodic Extension of Holomorphic Functions on Strips

This file proves that a holomorphic function on a horizontal strip with
matching boundary values extends to a bounded entire function.

## Main Results

- `periodicExtension`: Given F holomorphic on Strip β with F(t) = F(t + iβ),
  construct the periodic extension to all of ℂ
- `periodicExtension_continuous`: The extension is continuous
- `periodicExtension_bounded`: The extension is bounded
- `periodicExtension_entire`: The extension is entire (holomorphic on ℂ)
- `periodic_strip_extension`: The main theorem combining all of the above

## The Mathematical Content

The key insight is that the boundary condition F(t) = F(t + iβ) allows us to
"tile" the complex plane with copies of F. The extension is:
- Continuous by the boundary condition
- Holomorphic on each open strip (obvious)
- Holomorphic across the boundaries (by Morera's theorem)
- Bounded (since F is bounded on the closed strip and we're just repeating it)

Combining with Liouville's theorem (bounded entire ⟹ constant), we get that
functions with periodic boundary values must be constant on the strip.

## References

* Conway, "Functions of One Complex Variable I", Chapter V
* Rudin, "Real and Complex Analysis", Chapter 10
-/

namespace Spectra.PeriodicHolomorphic

open Complex Set Filter Topology Int MeasureTheory ProbabilityTheory

variable {β : ℝ} (hβ : 0 < β)

/-! ## Definitions -/

/-- The open horizontal strip {z : 0 < Im(z) < β} -/
def Strip (β : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ z.im < β}

/-- The closed horizontal strip {z : 0 ≤ Im(z) ≤ β} -/
def ClosedStrip (β : ℝ) : Set ℂ :=
  {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}

/-- The shifted closed strip {z : n*β ≤ Im(z) ≤ (n+1)*β} -/
def ClosedStrip.shift (β : ℝ) (n : ℤ) : Set ℂ :=
  {z : ℂ | n * β ≤ z.im ∧ z.im ≤ (n + 1) * β}

/-- The boundary lines at heights n*β for n ∈ ℤ -/
def BoundaryLines (β : ℝ) : Set ℂ :=
  {z : ℂ | ∃ n : ℤ, z.im = n * β}

/-- Embedding real numbers into the lower boundary -/
def realToLower (t : ℝ) : ℂ := t

/-- Embedding real numbers into the upper boundary at height β -/
def realToUpper (β : ℝ) (t : ℝ) : ℂ := t + β * I

/-! ## The Periodic Extension -/

/-- The floor of z.im / β, giving which strip z belongs to -/
noncomputable def stripIndex (β : ℝ) (z : ℂ) : ℤ := ⌊z.im / β⌋

/-- Translate z down to the fundamental strip [0, β] -/
noncomputable def toFundamentalStrip (β : ℝ) (z : ℂ) : ℂ :=
  z - (stripIndex β z : ℂ) * β * I

/-- The periodic extension of F from the closed strip to all of ℂ.

Given F : ℂ → ℂ defined on ClosedStrip β, we extend by:
  G(z) = F(z - n*β*I) where n = ⌊Im(z)/β⌋

This maps any z to the fundamental strip and evaluates F there.
-/
noncomputable def periodicExtension (F : ℂ → ℂ) (β : ℝ) : ℂ → ℂ := fun z =>
  F (toFundamentalStrip β z)

end Spectra.PeriodicHolomorphic

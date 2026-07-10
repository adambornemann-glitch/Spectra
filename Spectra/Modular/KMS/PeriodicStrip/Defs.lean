/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
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
# Periodic Extension of Holomorphic Functions on Strips: Definitions

This file lays out the basic *objects* used to state and prove the periodic-extension /
Hadamard-three-lines circle of results for horizontal strips in `ℂ`: the open and closed
strips, their integer shifts, the boundary embeddings of `ℝ` into the lower/upper edge, the
strip index (`⌊Im z / β⌋`), the translation of a point down to the fundamental strip, and the
periodic extension of a function itself. No holomorphy, continuity, or boundedness properties
are established here — those are proved in `Spectra.Modular.KMS.PeriodicStrip.Basic` and the
sibling files (`IndexProps`, `ExtensionProps`, `Hadamard`, `LineRemove`, `Painleve`), which
import this file and build the actual extension/entirety/Hadamard theorems on top of these
definitions.

## Main definitions

- `Strip`, `ClosedStrip`, `ClosedStrip.shift`: the open strip `{0 < Im z < β}`, its closure, and
  the shift of the closed strip to the `n`-th copy `{n·β ≤ Im z ≤ (n+1)·β}`.
- `realToLower`, `realToUpper`: the embeddings of `ℝ` into the lower boundary (`Im = 0`) and
  upper boundary (`Im = β`) of the strip.
- `stripIndex`: `⌊Im z / β⌋`, the index of the shifted strip containing `z`.
- `toFundamentalStrip`: translates `z` down by `stripIndex β z` copies of `β·I`, landing in the
  fundamental strip `ClosedStrip β`. **Seam convention**: a point on the upper boundary
  `Im z = n·β` (for `n : ℤ`) has `stripIndex β z = n` (since `⌊n⌋ = n`), so it is sent to
  `Im = 0`, the *lower* edge of the fundamental strip — not the upper edge `Im = β`. Equivalently,
  `toFundamentalStrip` treats each shifted strip as half-open on top, `[n·β, (n+1)·β)`, even
  though `ClosedStrip.shift` itself is stated as the closed interval `[n·β, (n+1)·β]`. This is
  the convention downstream continuity lemmas (e.g. in `IndexProps`) rely on when matching the
  extension's value at a boundary point to `F` evaluated at `realToLower`, not `realToUpper`.
- `periodicExtension`: given `F` on `ClosedStrip β`, the extension `G(z) = F(z - n·β·I)` where
  `n = stripIndex β z`, i.e. `F` "tiled" periodically across all shifted copies of the strip.

## References

* Conway, "Functions of One Complex Variable I", Chapter V
* Rudin, "Real and Complex Analysis", Chapter 10
-/

namespace Spectra.PeriodicHolomorphic

open Complex Set Filter Topology Int MeasureTheory ProbabilityTheory

/-! ## Definitions -/

/-- The open horizontal strip {z : 0 < Im(z) < β} -/
def Strip (β : ℝ) : Set ℂ :=
  {z : ℂ | 0 < z.im ∧ z.im < β}

@[simp] lemma mem_Strip {β : ℝ} {z : ℂ} : z ∈ Strip β ↔ 0 < z.im ∧ z.im < β := Iff.rfl

/-- The closed horizontal strip {z : 0 ≤ Im(z) ≤ β} -/
def ClosedStrip (β : ℝ) : Set ℂ :=
  {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}

@[simp] lemma mem_ClosedStrip {β : ℝ} {z : ℂ} : z ∈ ClosedStrip β ↔ 0 ≤ z.im ∧ z.im ≤ β := Iff.rfl

/-- The shifted closed strip {z : n*β ≤ Im(z) ≤ (n+1)*β} -/
def ClosedStrip.shift (β : ℝ) (n : ℤ) : Set ℂ :=
  {z : ℂ | n * β ≤ z.im ∧ z.im ≤ (n + 1) * β}

@[simp] lemma mem_ClosedStrip_shift {β : ℝ} {n : ℤ} {z : ℂ} :
    z ∈ ClosedStrip.shift β n ↔ n * β ≤ z.im ∧ z.im ≤ (n + 1) * β := Iff.rfl

/-- The boundary lines at heights `n·β` for `n ∈ ℤ`, i.e. the seams between consecutive
shifted strips `ClosedStrip.shift β n`. Not referenced elsewhere in the library: the
downstream files (`IndexProps`, `LineRemove`) work directly with the explicit range
`Im z = n * β` rather than through this set, so this is kept private scaffolding. -/
private def BoundaryLines (β : ℝ) : Set ℂ :=
  {z : ℂ | ∃ n : ℤ, z.im = n * β}

/-- Embedding real numbers into the lower boundary -/
def realToLower (t : ℝ) : ℂ := t

@[simp] lemma realToLower_re (t : ℝ) : (realToLower t).re = t := rfl

@[simp] lemma realToLower_im (t : ℝ) : (realToLower t).im = 0 := by simp [realToLower]

/-- Embedding real numbers into the upper boundary at height β -/
def realToUpper (β : ℝ) (t : ℝ) : ℂ := t + β * I

@[simp] lemma realToUpper_re (β t : ℝ) : (realToUpper β t).re = t := by simp [realToUpper]

@[simp] lemma realToUpper_im (β t : ℝ) : (realToUpper β t).im = β := by simp [realToUpper]

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

@[simp] lemma periodicExtension_apply (F : ℂ → ℂ) (β : ℝ) (z : ℂ) :
    periodicExtension F β z = F (toFundamentalStrip β z) := rfl

end Spectra.PeriodicHolomorphic

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Spectra.QuantumMechanics.Channels.TraceClass.Basic

/-!
# The Petz recovery map and exact recovery of the reference

Given a quantum channel `N` with Heisenberg (Hilbert–Schmidt) dual `N†` and a faithful reference
`σ`, the **Petz recovery map** is

  `P_{σ,N}(X) = σ^{1/2} · N†( N(σ)^{-1/2} · X · N(σ)^{-1/2} ) · σ^{1/2}`.

It is the canonical channel that *undoes* `N` — whenever anything can — and its defining property is
**exact recovery of the reference state**, `P_{σ,N}(N σ) = σ`, which holds for *every* channel with
no extra hypotheses beyond faithfulness and the unitality of `N†`.

## This file: the operator-algebra core

We formalise the map and the exact-recovery theorem at the level of bounded operators on a Hilbert
space `H`, abstracting the Heisenberg dual as a *unital* map `Φ` (`Φ 1 = 1`) and writing `σ`, `τ`
for the reference and its image `N(σ)`. The two square-root sandwiches are Mathlib's `CFC.conjSqrt`
(`conjSqrt c a = √c · a · √c`), so:

  `petzMap Φ σ τ X = conjSqrt σ (Φ (conjSqrt τ⁻¹ X))`.

The exact-recovery identity is then three rewrites: the inner sandwich collapses `τ` to `1`
(`conjSqrt_ringInverse_self`), unitality sends `Φ 1 = 1`, and the outer sandwich returns `σ`
(`conjSqrt_one`).

**Scope (honest).** The reference image `τ = N(σ)` is required *strictly positive*
(`IsStrictlyPositive`, i.e. positive and invertible / bounded below), so that `τ^{-1/2}` is a
*bounded* operator. This is the natural regularity condition and holds automatically in finite
dimensions and for faithful weights; it is a genuine statement over an arbitrary
(infinite-dimensional) `H`. The refinement to a *trace-class* faithful state — where the density is
compact, its eigenvalues accumulate at `0`, and `τ^{-1/2}` is therefore genuinely **unbounded** —
requires the unbounded
functional calculus and is deferred (cf. `InformationGeometry/Quantum/State.lean`'s `Faithful`
remark). Constructing the Heisenberg dual `N†` from a `QuantumChannel` (so `Φ` is a *theorem*, not a
hypothesis) is the companion milestone.

## Main definitions

* `Spectra.QuantumMechanics.Petz.petzMap Φ σ τ` — the Petz recovery map for a unital dual `Φ`,
  reference `σ`, and image `τ = N(σ)`.

## Main results

* `petzMap_recovery` — **exact recovery**: `petzMap Φ σ τ τ = σ` for unital `Φ`, `0 ≤ σ`, and
  strictly positive `τ`.
* `petzMap_id` — the Petz map of the identity channel is the identity, `petzMap id σ σ = id`.
-/

namespace Spectra.QuantumMechanics.Petz

open CFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **Petz recovery map** `P_{σ,N}(X) = σ^{1/2} Φ(τ^{-1/2} X τ^{-1/2}) σ^{1/2}`, with `Φ` the
Heisenberg dual `N†`, `σ` the faithful reference, and `τ = N(σ)` its image. Written with Mathlib's
`conjSqrt` (`conjSqrt c = √c · · · √c`): an inner conjugation by `√(τ⁻¹) = τ^{-1/2}`, the dual `Φ`,
then an outer conjugation by `√σ = σ^{1/2}`. -/
noncomputable def petzMap (Φ : (H →L[ℂ] H) → H →L[ℂ] H) (σ τ : H →L[ℂ] H) :
    (H →L[ℂ] H) → H →L[ℂ] H :=
  fun X => conjSqrt σ (Φ (conjSqrt (Ring.inverse τ) X))

@[simp] lemma petzMap_apply (Φ : (H →L[ℂ] H) → H →L[ℂ] H) (σ τ X : H →L[ℂ] H) :
    petzMap Φ σ τ X = conjSqrt σ (Φ (conjSqrt (Ring.inverse τ) X)) := rfl

/-- **Exact recovery of the reference state.** For a unital dual `Φ` (`Φ 1 = 1`), a positive
reference `σ`, and a strictly positive image `τ = N(σ)`, the Petz map sends `τ` back to `σ`:
`P_{σ,N}(N σ) = σ`. This is the defining property of the Petz recovery map, and needs no hypothesis
beyond faithfulness and unitality — it holds for *any* channel. -/
theorem petzMap_recovery {Φ : (H →L[ℂ] H) → H →L[ℂ] H} {σ τ : H →L[ℂ] H}
    (hΦ : Φ 1 = 1) (hσ : 0 ≤ σ) (hτ : IsStrictlyPositive τ) :
    petzMap Φ σ τ τ = σ := by
  rw [petzMap_apply, conjSqrt_ringInverse_self τ hτ, hΦ, conjSqrt_one σ hσ]

/-- **The Petz map of the identity channel is the identity.** For the identity channel `N = id` one
has `N† = id` and `N(σ) = σ`, and `P_{σ,id} = id`: the two square-root sandwiches cancel. -/
@[simp] theorem petzMap_id {σ : H →L[ℂ] H} (hσ : IsStrictlyPositive σ) (X : H →L[ℂ] H) :
    petzMap id σ σ X = X := by
  simp only [petzMap_apply, id_eq]
  exact conjSqrt_conjSqrt_ringInverse σ X hσ

end Spectra.QuantumMechanics.Petz

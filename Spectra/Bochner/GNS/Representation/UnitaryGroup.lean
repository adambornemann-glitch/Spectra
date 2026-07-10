/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.Hilbert.Constructor

/-!
# The GNS Unitary Group Structure

This file bundles the translation action extended to the GNS Hilbert space into a single
structure, `GNSUnitaryGroup`, sitting between the raw `GNSData` (Hilbert space + embedding) and
`Spectra.OneParameterUnitaryGroup` (the standard interface Stone's theorem consumes).

## Main definitions

* `GNSUnitaryGroup`: a `GNSData f` together with the extended translation action
  `unitaryAction : ℝ → H →L[ℂ] H`, its inner-product-preserving (`isometry`), group-law,
  identity, and strong-continuity properties, and its compatibility with `embed`/`translate`.

## References

* `Representation/UnitaryConstructor.lean`'s `gnsUnitaryConstruction` builds the witness;
  `Representation/ToStone.lean`'s `toOneParameterUnitaryGroup` repackages it for Stone's theorem.
-/
open scoped InnerProductSpace
namespace Spectra.Bochner.GNS

/-- Extended translation action on the GNS Hilbert space.

Since `translate t` is an isometry of the pre-inner product:
  `⟨U(t)α, U(t)β⟩ = ⟨α, β⟩`
it descends to an isometry on the quotient, which extends uniquely
to an isometry on the completion. -/
structure GNSUnitaryGroup (f : ℝ → ℂ) extends GNSData f where
  /-- The unitary group action on H, bundled as continuous linear maps — the type
  `Spectra.OneParameterUnitaryGroup` itself consumes, so `Representation/ToStone.lean`'s
  repackaging needs no re-wrap. -/
  unitaryAction : ℝ → H →L[ℂ] H
  /-- U(t) is an isometry. -/
  isometry : ∀ (t : ℝ) (ψ φ : H),
    letI := instIPS
    ⟪unitaryAction t ψ, unitaryAction t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ
  /-- Group law: U(s+t) = U(s) ∘ U(t). -/
  group_law : ∀ (s t : ℝ) (ψ : H),
    unitaryAction (s + t) ψ = unitaryAction s (unitaryAction t ψ)
  /-- Identity: U(0) = id. -/
  identity : ∀ (ψ : H), unitaryAction 0 ψ = ψ
  /-- Strong continuity: t ↦ U(t)ψ is continuous for each ψ. -/
  strong_continuous : ∀ (ψ : H), Continuous (fun t => unitaryAction t ψ)
  /-- Compatibility: U(t) ∘ embed = embed ∘ translate(t). -/
  compat : ∀ (t : ℝ) (α : ℝ →₀ ℂ),
    unitaryAction t (toGNSData.embed α) = toGNSData.embed (translate t α)

end Spectra.Bochner.GNS

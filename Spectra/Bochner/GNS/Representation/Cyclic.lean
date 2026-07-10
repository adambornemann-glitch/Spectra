/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.Representation.UnitaryConstructor

/-!
# The GNS Cyclic Vector

This file identifies the cyclic vector `ξ` of the GNS Hilbert space and proves the representation
theorem at the Hilbert-space level: `f(t) = ⟨ξ, U(t)ξ⟩_H`. This is the reproducing-kernel identity
of `Bochner/GNS/PreHilbert/Cyclic.lean` transported across the GNS embedding.

## Main definitions

* `gnsCyclic` — the cyclic vector `ξ = embed(δ₀) = embed(single 0 1)` in the GNS Hilbert space.

## Main statements

* `gns_representation` — `f(t) = ⟨ξ, U(t)ξ⟩_H` for every `t`, the representation theorem.
* `gns_cyclic_norm_sq` — the `t = 0` corollary `⟨ξ, ξ⟩_H = f(0)`, i.e. `‖ξ‖² = (f 0).re`.
-/
open Spectra.PositiveDefinite
namespace Spectra.Bochner.GNS

/-- The cyclic vector in the GNS Hilbert space:
    `ξ = embed(δ₀) = embed(single 0 1)`. -/
noncomputable def gnsCyclic {f : ℝ → ℂ} (gns : GNSData f) : gns.H :=
  gns.embed cyclicVector

/-- **THE KEY IDENTITY in H**: `f(t) = ⟨ξ, U(t)ξ⟩_H`.

This is the representation theorem at the Hilbert space level.
It follows directly from PreHilbert's `pdInner_cyclic` composed
with the embedding's inner product preservation.

Proof:
  ⟨ξ, U(t)ξ⟩_H
    = ⟨embed(δ₀), U(t)(embed(δ₀))⟩_H           [definition of ξ]
    = ⟨embed(δ₀), embed(translate t δ₀)⟩_H       [compatibility]
    = pdInner f δ₀ (translate t δ₀)               [embed_inner]
    = f(t)                                         [pdInner_cyclic] -/
theorem gns_representation {f : ℝ → ℂ}
    (gns : GNSUnitaryGroup f) (t : ℝ) :
    @inner ℂ gns.H gns.instIPS.toInner
      (gnsCyclic gns.toGNSData)
      (gns.unitaryAction t (gnsCyclic gns.toGNSData)) = f t := by
  unfold gnsCyclic
  rw [gns.compat t cyclicVector,
      gns.toGNSData.embed_inner cyclicVector (translate t cyclicVector),
      pdInner_cyclic f t]

/-- The norm of the cyclic vector: `‖ξ‖² = f(0).re`. This is the `t = 0` case of
`gns_representation`, recorded standalone since it needs no `GNSUnitaryGroup`, only the underlying
`GNSData`.

Proof: ‖ξ‖² = Re⟨ξ,ξ⟩ = Re(pdInner f δ₀ δ₀) = Re(f(0)) = f(0).re. -/
lemma gns_cyclic_norm_sq {f : ℝ → ℂ} (gns : GNSData f) :
    @inner ℂ gns.H gns.instIPS.toInner
      (gnsCyclic gns) (gnsCyclic gns) = f 0 := by
  unfold gnsCyclic
  rw [gns.embed_inner]
  have := pdInner_cyclic f 0
  rw [translate_zero] at this
  exact this

end Spectra.Bochner.GNS

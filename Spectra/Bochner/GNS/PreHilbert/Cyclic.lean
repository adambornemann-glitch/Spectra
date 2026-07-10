/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PreHilbert.TransAction

/-!
# The GNS Cyclic Vector

Defines the cyclic vector `ξ = δ_0` for the GNS pre-Hilbert space and proves the key identity
`⟨ξ, U(t)ξ⟩_f = f(t)` that reproduces `f` from the inner product and the translation action.
In the completed Hilbert space, `ξ` will be genuinely cyclic: `span(U(t)ξ : t ∈ ℝ)` is dense.

## Main definitions

* `cyclicVector` — the cyclic vector `ξ = δ_0 = Finsupp.single 0 1`.

## Main statements

* `pdInner_cyclic` — the GNS reproducing-kernel identity `⟨ξ, U(t)ξ⟩_f = f(t)`.

## References

* Folland, *A Course in Abstract Harmonic Analysis*, §3.3
* Reed & Simon, *Methods of Modern Mathematical Physics I*, §II.6
-/

open Finsupp

namespace Spectra.Bochner.GNS

-- §7  The cyclic vector

/-- The cyclic vector: `ξ = δ_0 = single 0 1`.

In the completed Hilbert space, this will satisfy:
  `f(t) = ⟨ξ, U(t)ξ⟩`  and  `span(U(t)ξ : t ∈ ℝ)` is dense. -/
noncomputable def cyclicVector : ℝ →₀ ℂ := Finsupp.single 0 1

/-- `U(t)(ξ) = δ_t`. -/
@[simp]
lemma translate_cyclicVector (t : ℝ) :
    translate t cyclicVector = Finsupp.single t 1 := by
  unfold cyclicVector
  rw [translate_single]
  simp

/-- **The GNS reproducing-kernel identity**: `f(t) = ⟨ξ, U(t)ξ⟩_f`.

This is the fundamental formula that connects the abstract positive
definite function to the concrete inner product on the GNS space.

Proof: `⟨ξ, U(t)ξ⟩ = ⟨δ₀, δ_t⟩ = conj(1) · 1 · f(t - 0) = f(t)`. -/
theorem pdInner_cyclic (f : ℝ → ℂ) (t : ℝ) :
    pdInner f cyclicVector (translate t cyclicVector) = f t := by
  rw [translate_cyclicVector]
  unfold cyclicVector
  rw [pdInner_single_single, map_one, one_mul, one_mul, sub_zero]

end Spectra.Bochner.GNS

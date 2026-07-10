/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.Hilbert.NullSpace

/-!
# GNS Data Bundle

The complete GNS data for a continuous positive definite function `f : ℝ → ℂ`, bundled into a
single existential-style structure rather than the individual quotient/completion/embedding
pieces.

## Main definitions

* `GNSData` — a Hilbert space `H` together with an embedding of formal sums `ℝ →₀ ℂ →ₗ[ℂ] H`
  that respects the pre-inner product (`embed_inner`), is dense (`embed_dense`), and has kernel
  exactly the null space (`embed_ker`).

## Implementation notes

Constructing the GNS Hilbert space step by step — quotient by the null space, then complete —
needs enough Mathlib quotient/completion plumbing that bundling the *result* into one structure
and constructing an inhabitant directly is simpler here. `GNSData`'s fields are not established
in this file: `Hilbert/Constructor.lean`'s `gnsConstruction` builds the quotient-completion
construction and shows `GNSData f` is inhabited for every continuous positive definite `f`.

## References

* Folland, *A Course in Abstract Harmonic Analysis*, §3.3
* Reed & Simon, *Methods of Modern Mathematical Physics I*, §II.6
-/
namespace Spectra.Bochner.GNS

/-- The complete GNS data for a continuous positive definite function.

Rather than constructing the quotient and completion step by step (which requires heavy
Mathlib plumbing), we bundle everything into a single structure and show it exists —
see `Hilbert/Constructor.lean`'s `gnsConstruction` for the construction. -/
structure GNSData (f : ℝ → ℂ) where
  /-- The GNS Hilbert space. -/
  H : Type*
  /-- H is a normed additive commutative group. -/
  instNACG : NormedAddCommGroup H
  /-- H is an inner product space over ℂ. -/
  instIPS : @InnerProductSpace ℂ H _ instNACG.toSeminormedAddCommGroup
  /-- H is complete (Hilbert). -/
  instComplete : @CompleteSpace H instNACG.toUniformSpace
  /-- Embedding of formal sums into H. -/
  embed : letI := instNACG; letI := instIPS; (ℝ →₀ ℂ) →ₗ[ℂ] H
  /-- The embedding respects the pre-inner product. -/
  embed_inner : ∀ (α β : ℝ →₀ ℂ),
    @inner ℂ H instIPS.toInner (embed α) (embed β) = pdInner f α β
  /-- The embedded formal sums are dense in H. -/
  embed_dense : letI := instNACG; Dense (Set.range embed)
  /-- The kernel of the embedding is the null space. -/
  embed_ker : letI := instNACG; ∀ α, embed α = 0 ↔ α ∈ pdNullSpace f

end Spectra.Bochner.GNS

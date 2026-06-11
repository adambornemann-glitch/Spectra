/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerTheorem/GNS/Basic.lean
-/
import Spectra.Bochner.GNS.Representation.ToStone
open Complex Finsupp Filter Topology
namespace Spectra.Bochner.GNS

/-- **The GNS theorem for positive definite functions on `ℝ`.**

Every continuous positive definite function `f : ℝ → ℂ` is a diagonal
matrix coefficient of a strongly continuous one-parameter group of
isometries. Concretely, there exist:

* a complex Hilbert space `H`;
* linear maps `U t : H →ₗ[ℂ] H` preserving the inner product
  (`⟪U t ψ, U t φ⟫ = ⟪ψ, φ⟫`), with `U (s + t) = U s ∘ U t`, `U 0 = id`,
  and `t ↦ U t ψ` continuous for every `ψ`;
* a vector `ξ : H` with `f t = ⟪ξ, U t ξ⟫` for all `t`.

Taking `t = 0` gives `⟪ξ, ξ⟫ = f 0`, hence `‖ξ‖² = (f 0).re`.

This is the existence half of the GNS construction; combined with Stone's
theorem and the spectral theorem it gives the existence direction of
Bochner's theorem. -/
theorem gns_theorem {f : ℝ → ℂ} (hf : IsContinuous f) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (U : ℝ → H →ₗ[ℂ] H) (ξ : H),
      (∀ t ψ φ, @inner ℂ H ‹InnerProductSpace ℂ H›.toInner (U t ψ) (U t φ) =
                 @inner ℂ H ‹InnerProductSpace ℂ H›.toInner ψ φ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ ψ, Continuous (fun t => U t ψ)) ∧
      (∀ t, @inner ℂ H ‹InnerProductSpace ℂ H›.toInner ξ (U t ξ) = f t) := by
  let gns := gnsUnitaryConstruction hf
  exact ⟨gns.H, gns.instNACG, gns.instIPS, gns.instComplete,
    gns.unitaryAction, gns_cyclic gns.toGNSData,
    gns.isometry, gns.group_law, gns.identity, gns.strong_continuous,
    fun t => gns_representation gns t⟩

  end Spectra.Bochner.GNS

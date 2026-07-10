/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.Representation.ToStone

/-!
# The GNS Theorem for Positive-Definite Functions

## Main statements

* `gns_theorem`: every positive-definite, Hermitian-symmetric, continuous-at-`0`
  `f : ℝ → ℂ` is a diagonal matrix coefficient of a strongly continuous one-parameter group of
  isometries.

## Implementation notes

`gns_theorem` is a standalone summary re-packaging of `gnsUnitaryConstruction` (the actual GNS
construction, in `Representation/UnitaryConstructor.lean`) and `gns_representation` (in
`Representation/Cyclic.lean`), stated as a clean existential independent of any particular
downstream use. It is not itself load-bearing: `Bochner/Basic.lean`'s `bochner_theorem` calls
`gnsUnitaryConstruction`/`gns_representation` directly rather than through this theorem, since it
needs more than this existential packages (the spectral measure machinery on top). `gns_theorem`
exists purely for readability — a self-contained statement of "GNS existence" a reader can check
without following the full Bochner pipeline.

## References

* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VIII.5 (Gelfand–Naimark–Segal
  construction)
-/
open scoped InnerProductSpace
namespace Spectra.Bochner.GNS

/-- **The GNS theorem for positive definite functions on `ℝ`.**

Every positive-definite, Hermitian-symmetric `f : ℝ → ℂ` that is continuous at `0`
(bundled as `IsContinuous f`) is a diagonal matrix coefficient of a strongly continuous
one-parameter group of isometries. Concretely, there exist:

* a complex Hilbert space `H`;
* continuous linear maps `U t : H →L[ℂ] H` preserving the inner product
  (`⟪U t ψ, U t φ⟫ = ⟪ψ, φ⟫`), with `U (s + t) = U s ∘ U t`, `U 0 = id`,
  and `t ↦ U t ψ` continuous for every `ψ`;
* a vector `ξ : H` with `f t = ⟪ξ, U t ξ⟫` for all `t`.

Taking `t = 0` gives `⟪ξ, ξ⟫ = f 0`, hence `‖ξ‖² = (f 0).re`; this is `gns_cyclic_norm_sq`
specialized to `gnsUnitaryConstruction hf`.

This is the existence half of the GNS construction; combined with Stone's
theorem and the spectral theorem it gives the existence direction of
Bochner's theorem. -/
theorem gns_theorem {f : ℝ → ℂ} (hf : IsContinuous f) :
    ∃ (H : Type) (instNACG : NormedAddCommGroup H) (instIPS : InnerProductSpace ℂ H)
      (_ : CompleteSpace H)
      (U : ℝ → H →L[ℂ] H) (ξ : H),
      letI := instNACG; letI := instIPS
      (∀ t ψ φ, ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ ψ, Continuous (fun t => U t ψ)) ∧
      (∀ t, ⟪ξ, U t ξ⟫_ℂ = f t) := by
  let gns := gnsUnitaryConstruction hf
  exact ⟨gns.H, gns.instNACG, gns.instIPS, gns.instComplete,
    gns.unitaryAction, gnsCyclic gns.toGNSData,
    gns.isometry, gns.group_law, gns.identity, gns.strong_continuous,
    fun t => gns_representation gns t⟩

end Spectra.Bochner.GNS

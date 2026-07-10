/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.ResolventForm
import Spectra.CayleyTransform.Generator.Stone
/-!
# The spectral theorem, independently proved via Cayley/Riesz–Markov

`spectralTheorem` (`SpectralTheory/ResolventForm.lean`) is von Neumann's spectral theorem in
resolvent form: every self-adjoint `A` has a **unique** `ProjValMeasure` representing its
resolvent (`∃! P, ∀ z (hz : z.im ≠ 0) ξ, ⟪ξ,(A-z)⁻¹ξ⟫ = ∫(s-z)⁻¹ d(P.diag ξ)`). Its existence
witness there is `spectralPVM hA := groupPVM (genToGroup hA)`, built through the Hille–Yosida
route.

This file proves the **same** theorem a second, independent way: through the Cayley/Riesz–Markov
route, with existence witnessed by `groupPVM (stoneGroup hA)` — mentioning `genToGroup` nowhere.
The uniqueness half, `spectralPVM_unique`, is already fully generic (it characterizes `P` purely
by the resolvent formula it satisfies, never by how `P` was constructed), so once the Cayley PVM
is shown to satisfy that same formula, uniqueness alone forces it to equal `spectralPVM hA`.

This is the historical point of the Cayley transform (von Neumann, 1929/1932): the spectral
theorem for an unbounded self-adjoint operator, *derived* from Riesz–Markov on its bounded
unitary transform — not merely identified with a derivation obtained some other way. That weaker
identification is `StoneBridge/SpectralPVM.lean`'s `spectralPVM_eq_groupPVM_stoneGroup`, which
reached the same conclusion by borrowing the *group*-level identity `stoneGroup_eq_genToGroup`
instead of proving existence directly. This file supersedes it with a genuine second proof.

## Main results

* `selfAdjointResolvent_eq_stoneGroup` — the resolvent of `A` is the resolvent of the generator of
  `stoneGroup hA`. Mirrors `selfAdjointResolvent_eq_genToGroup` verbatim, using
  `generator_stoneGroup` in place of `generator_genToGroup`. No `z = -i` exclusion: unlike the
  intermediate `generator_resolvent_eq_selfAdjoint` it's built from, the *final*
  `generator_stoneGroup` is unconditional in `z`, so this transport is unconditional too.
* `cayleyPVM_resolvent_formula` — **existence, Cayley route**: `groupPVM (stoneGroup hA)` satisfies
  the resolvent formula for every `z` with `Im z ≠ 0`.
* `spectralTheoremCayley` — the spectral theorem, `∃!`, witnessed by the Cayley PVM.
* `groupPVM_stoneGroup_eq_spectralPVM_independent` — `groupPVM (stoneGroup hA) = spectralPVM hA`,
  reproving `spectralPVM_eq_groupPVM_stoneGroup` a second, independent way (existence + uniqueness,
  not group-equality).
-/
open InnerProductSpace Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.OneParameterUnitaryGroup Spectra.Resolvent Spectra.Borel
open Spectra.YosidaHille Spectra.Cayley

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

namespace Spectra.QuantumMechanics.SpectralTheory

/-- The resolvent of `A` is the resolvent of the generator of `stoneGroup hA` — the Cayley-route
mirror of `selfAdjointResolvent_eq_genToGroup`. -/
theorem selfAdjointResolvent_eq_stoneGroup [Nontrivial H] (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) :
    selfAdjointResolvent hA z hz
      = resolvent z hz (generator_isFormalAdjoint (stoneGroup hA))
          (range_plus_i_eq_top (stoneGroup hA)) (range_minus_i_eq_top (stoneGroup hA)) := by
  unfold selfAdjointResolvent
  exact resolvent_congr_operator (generator_stoneGroup hA).symm z hz
    (isFormalAdjoint_of_isSelfAdjoint hA)
    (isSelfAdjoint_to_surjective hA).1 (isSelfAdjoint_to_surjective hA).2
    (generator_isFormalAdjoint _) (range_plus_i_eq_top _) (range_minus_i_eq_top _)

/-- **Existence, via Cayley.** The Cayley/Borel-built PVM `groupPVM (stoneGroup hA)` represents
the resolvent of `A` — proved without ever mentioning `genToGroup`. -/
theorem cayleyPVM_resolvent_formula [Nontrivial H] (hA : IsSelfAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) (ξ : H) :
    ⟪ξ, selfAdjointResolvent hA z hz ξ⟫_ℂ
      = ∫ s, ((s : ℂ) - z)⁻¹ ∂((groupPVM (stoneGroup hA)).diag ξ) := by
  rw [selfAdjointResolvent_eq_stoneGroup hA z hz, groupPVM_diag]
  exact inner_resolvent_diag_eq_integral (stoneGroup hA) z hz ξ

/-- **The reproof.** The Cayley PVM equals the canonical `spectralPVM`, now via existence +
uniqueness rather than the group-level `stoneGroup_eq_genToGroup` — a second, independent proof of
`spectralPVM_eq_groupPVM_stoneGroup` (`StoneBridge/SpectralPVM.lean`). -/
theorem groupPVM_stoneGroup_eq_spectralPVM_independent [Nontrivial H] (hA : IsSelfAdjoint A) :
    groupPVM (stoneGroup hA) = spectralPVM hA :=
  spectralPVM_unique hA (groupPVM (stoneGroup hA)) (cayleyPVM_resolvent_formula hA)

/-- **The spectral theorem, proved independently via Cayley.** Same statement as `spectralTheorem`
— existence witnessed by the Cayley PVM; uniqueness reused verbatim (it's already generic), then
composed with `groupPVM_stoneGroup_eq_spectralPVM_independent` to land on the chosen witness. -/
theorem spectralTheoremCayley [Nontrivial H] (hA : IsSelfAdjoint A) :
    ∃! P : ProjValMeasure H,
      ∀ (z : ℂ) (hz : z.im ≠ 0) (ξ : H),
        ⟪ξ, selfAdjointResolvent hA z hz ξ⟫_ℂ
          = ∫ s, ((s : ℂ) - z)⁻¹ ∂(P.diag ξ) :=
  ⟨groupPVM (stoneGroup hA), cayleyPVM_resolvent_formula hA,
    fun P hP => (spectralPVM_unique hA P hP).trans
      (groupPVM_stoneGroup_eq_spectralPVM_independent hA).symm⟩

end Spectra.QuantumMechanics.SpectralTheory

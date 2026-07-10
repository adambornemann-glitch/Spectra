/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Spectra.Operator.Unitary.Basic
import Spectra.Operator.Unitary.Powers
import Spectra.CayleyTransform.Defs
import Spectra.PositiveDefinite.Unitary
/-!
# Bridge: `Operator.Unitary` ↔ Mathlib's `unitary` submonoid

Our `QuantumMechanics.Operator.Unitary U` is a bespoke predicate (inner-product preservation +
surjectivity).  Mathlib's continuous functional calculus is keyed instead to membership in the
`unitary` submonoid of the C⋆-algebra `H →L[ℂ] H` (`star U * U = 1 ∧ U * star U = 1`), for which
the `CStarAlgebra (H →L[ℂ] H)` instance and `IsStarNormal.instContinuousFunctionalCalculus`
provide `cfc` with no further work.

This file is the (one-way is all we need, but it is an iff) translation.  After it, for the
Cayley transform of a self-adjoint operator:

* `cfc f (cayleyTransform hsym hplus)` is available for `f : ℂ → ℂ` continuous on the spectrum;
* the spectrum lives on the unit circle (`Operator.spectrum_subset_circle`);
* `IsStarNormal` holds via `isStarNormal_of_mem_unitary` (independent re-derivation of our
  `cayleyTransform_isStarNormal`, which can then be retired or kept as a sanity check).

## Main declarations

* `mem_unitary_of_inner_map_map_of_surjective` — the workhorse implication.
* `mem_unitary_iff_inner_map_map_and_surjective` — the characterization.
* `Cayley.Unitary.mem_unitary` — glue to the project's predicate (commented until import wired).
-/
open Complex ContinuousLinearMap
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Operator

/-- An inner-product–preserving surjective continuous linear map belongs to Mathlib's
`unitary` submonoid of the C⋆-algebra `H →L[ℂ] H`. -/
lemma mem_unitary_of_inner_map_map_of_surjective {U : H →L[ℂ] H}
    (hinner : ∀ ψ φ : H, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (hsurj : Function.Surjective U) :
    U ∈ unitary (H →L[ℂ] H) := by
  have hstar : star U * U = 1 := by
    ext ψ
    refine ext_inner_right ℂ fun φ => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    exact hinner ψ φ
  refine Unitary.mem_iff.mpr ⟨hstar, ?_⟩
  -- `U ∘ U† = 1` from `U† ∘ U = 1` and surjectivity.
  ext φ
  obtain ⟨ψ, rfl⟩ := hsurj φ
  have hψ : (star U * U) ψ = ψ := by rw [hstar]; rfl
  calc (U * star U) (U ψ) = U ((star U * U) ψ) := rfl
    _ = U ψ := by rw [hψ]

/-- Conversely, unitary elements preserve the inner product and are surjective; together with
the previous lemma this characterizes `unitary (H →L[ℂ] H)`. -/
lemma mem_unitary_iff_inner_map_map_and_surjective {U : H →L[ℂ] H} :
    U ∈ unitary (H →L[ℂ] H) ↔
      (∀ ψ φ : H, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ) ∧ Function.Surjective U := by
  refine ⟨fun hU => ⟨fun ψ φ => ?_, fun φ => ⟨(star U) φ, ?_⟩⟩,
    fun ⟨h₁, h₂⟩ => mem_unitary_of_inner_map_map_of_surjective h₁ h₂⟩
  · calc ⟪U ψ, U φ⟫_ℂ
        = ⟪(star U * U) ψ, φ⟫_ℂ := by
          rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪ψ, φ⟫_ℂ := by rw [hU.1]; rfl
  · calc U ((star U) φ) = (U * star U) φ := rfl
      _ = φ := by rw [hU.2]; rfl

/-- Inner-product–preserving surjections are star-normal: the cfc trigger, derived from
the unitary bridge rather than by hand. (Currently unused.) -/
lemma isStarNormal_of_inner_map_map_of_surjective {U : H →L[ℂ] H}
    (hinner : ∀ ψ φ : H, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (hsurj : Function.Surjective U) :
    IsStarNormal U :=
  isStarNormal_of_mem_unitary (mem_unitary_of_inner_map_map_of_surjective hinner hsurj)

/-- Spectrum of an inner-product-preserving surjection lies on the unit circle.
(Currently unused.) -/
lemma spectrum_subset_circle_of_inner_map_map_of_surjective {U : H →L[ℂ] H}
    (hinner : ∀ ψ φ : H, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (hsurj : Function.Surjective U) :
    spectrum ℂ U ⊆ Metric.sphere (0 : ℂ) 1 :=
  -- name as of master 2026-06: `Unitary.spectrum_subset_circle (u : unitary E)`
  Unitary.spectrum_subset_circle
    (⟨U, mem_unitary_of_inner_map_map_of_surjective hinner hsurj⟩ : unitary (H →L[ℂ] H))

end Spectra.Operator

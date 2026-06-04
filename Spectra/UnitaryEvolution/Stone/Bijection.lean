/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Stone/Bijection.lean
-/
import Spectra.UnitaryEvolution.Stone.Helpers
import Spectra.UnitaryEvolution.Stone.Unique
import Spectra.UnitaryEvolution.Stone.Converse
/-!
# Stone's Theorem: Complete Statement

This file assembles the complete Stone's theorem, establishing a bijective
correspondence between strongly continuous one-parameter unitary groups and
self-adjoint operators on a Hilbert space.

## References

* [Stone, "On one-parameter unitary groups in Hilbert space"][stone1932]
* [von Neumann, "Über Funktionen von Funktionaloperatoren"][vonneumann1932]
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VIII.8

## Tags

Stone's theorem, unitary group, self-adjoint operator, spectral theory
-/
namespace QuantumMechanics.StonesTheorem
open InnerProductSpace Complex Filter Topology
open Yosida Resolvent Bochner Stoneslemma
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


noncomputable def stoneEquiv :
    OneParameterUnitaryGroup (H := H) ≃ {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} where
  toFun  U := ⟨generator U, generator_isSelfAdjoint U⟩
  invFun A := genToGroup A.2
  left_inv  U := group_unique _ _ (generator_genToGroup (generator_isSelfAdjoint U))
  right_inv A := Subtype.ext (generator_genToGroup A.2)


@[simp] lemma stoneEquiv_apply (U : OneParameterUnitaryGroup (H := H)) :
    (stoneEquiv U : H →ₗ.[ℂ] H) = generator U := rfl

@[simp] lemma stoneEquiv_symm_apply {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    stoneEquiv.symm ⟨A, hA⟩ = genToGroup hA := rfl

@[simp] lemma stoneEquiv_symm_U {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (t : ℝ) (ψ : H) :
    (stoneEquiv.symm ⟨A, hA⟩).U t ψ = (genToGroup hA).U t ψ := rfl

/-- For self-adjoint `A` and `ψ ∈ dom A`, the orbit `t ↦ U_A(t) ψ` solves `f'(t) = i A f(t)`. -/
theorem stone_orbit_hasDerivAt (U : OneParameterUnitaryGroup (H := H))
    (ψ : (generator U).domain) (t : ℝ) :
    HasDerivAt (fun s => U.U s (ψ : H))
      (I • generator U ⟨U.U t (ψ : H), generator_domain_invariant U t ψ⟩) t := by
  rw [generator_comm]; exact unitary_orbit_hasDerivAt U ψ t


end QuantumMechanics.StonesTheorem

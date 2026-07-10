/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.VonNeumannExtensionSelfAdjoint
import Spectra.CayleyTransform.Defs

/-!
# Von Neumann's self-adjoint extension theorem

A symmetric, densely-defined operator `A : H →ₗ.[ℂ] H` admits a self-adjoint extension **iff**
its deficiency subspaces `N₊(A)` and `N₋(A)` are isometrically isomorphic
(`exists_le_isSelfAdjoint_iff_nonempty_deficiencyEquiv`).

*"If"*: given a unitary `V : N₊(A) ≃ₗᵢ[ℂ] N₋(A)`, the von Neumann extension `A_V` is
essentially self-adjoint (`vonNeumannExtension_isEssentiallySelfAdjoint`), so its closure is a
self-adjoint extension of `A`. No closedness of `A` is needed — the closure absorbs it. (For
closed `A`, `A_V` itself is already self-adjoint by `vonNeumannExtension_isSelfAdjoint`.)

*"Only if"*: given a self-adjoint extension `B ≥ A`, the Cayley transform of `B` is a
surjective isometry of `H` (`cayleyEquiv`) sending `(B + i)ψ ↦ (B - i)ψ`; since `B` extends
`A` it maps `ran(A + i)` onto `ran(A - i)` (`map_cayleyEquiv_rangeSubmodule`), hence — a
unitary carries orthogonal complements to orthogonal complements
(`Submodule.map_orthogonal_equiv`) — it restricts to an isometric isomorphism of the
deficiency subspaces `N₊(A) = ran(A + i)ᗮ` onto `N₋(A) = ran(A - i)ᗮ`.

Note the theorem is stated for arbitrary symmetric densely-defined `A`, not just closed `A` as
in the textbook statement: the deficiency subspaces of `A` and of its closure coincide (both
are defined through `A* = (A.closure)*`), so closedness is a cosmetic hypothesis that the
closure trick in the "if" direction removes.

On the **cardinal-valued** phrasing (`deficiencyIndexPlus A = deficiencyIndexMinus A`, i.e.
equal `Module.rank`): this is deliberately NOT stated. In infinite dimension the algebraic
(Hamel) rank is the wrong invariant — two closed subspaces can have equal `Module.rank` (e.g.
both `2^ℵ₀`) while having different orthonormal-basis cardinalities, hence NOT be isometrically
isomorphic. The honest cardinal version needs a Hilbert-dimension notion (orthonormal-basis
cardinality) and its bridge to `LinearIsometryEquiv`; the `Nonempty (N₊ ≃ₗᵢ N₋)` phrasing used
here is the mathematically correct core.

## Main definitions

* `cayleyEquiv` — the Cayley transform of a symmetric operator with surjective `B ± i`,
  bundled as a `LinearIsometryEquiv` of `H`.
* `isometryEquivOfMapEq` — restriction of an ambient `LinearIsometryEquiv` to a submodule it
  maps onto another (fills a Mathlib gap: `LinearEquiv.submoduleMap` has no isometry version).
* `inducedDeficiencyEquiv` — the deficiency identification `N₊(A) ≃ₗᵢ[ℂ] N₋(A)` induced by a
  self-adjoint extension `B ≥ A`: the restriction of `B`'s Cayley transform. This is the `V`
  for which `B = A_V` (proved in `Spectra.Operator.SelfAdjointExtensionClassification`).

## Main statements

* `map_cayleyEquiv_rangeSubmodule` — the Cayley transform of an extension maps `ran(A + i)`
  onto `ran(A - i)`.
* `nonempty_deficiencyEquiv_of_le_isSelfAdjoint` — the "only if" half.
* `exists_le_isSelfAdjoint_of_nonempty_deficiencyEquiv` — the "if" half.
* `exists_le_isSelfAdjoint_iff_nonempty_deficiencyEquiv` — **von Neumann's extension
  theorem**.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.2.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The Cayley transform as a linear isometry equivalence -/

/-- The Cayley transform of a symmetric operator `B` with surjective `B ± i`, bundled as a
linear isometry **equivalence** of the ambient space: the isometry is
`cayleyTransform_isometry`, the surjectivity is `cayleyTransform_surjective`. -/
noncomputable def cayleyEquiv {B : H →ₗ.[ℂ] H} (hsym : B.IsFormalAdjoint B)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    ⟨(Spectra.Cayley.cayleyTransform hsym hplus).toLinearMap,
      Spectra.Cayley.cayleyTransform_isometry hsym hplus⟩
    (Spectra.Cayley.cayleyTransform_surjective hsym hplus hminus)

omit [CompleteSpace H] in
/-- The bundled Cayley equivalence acts as the Cayley transform. -/
lemma cayleyEquiv_apply {B : H →ₗ.[ℂ] H} (hsym : B.IsFormalAdjoint B)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) (φ : H) :
    cayleyEquiv hsym hplus hminus φ = Spectra.Cayley.cayleyTransform hsym hplus φ :=
  rfl

omit [CompleteSpace H] in
/-- On the domain of the restriction `A ≤ B`, the Cayley equivalence of `B` sends
`Aψ - (-i)ψ = Aψ + iψ` to `Aψ - iψ`; the `-(-i)` spelling matches the generators of
`rangeSubmodule (A := A) (-I)`. -/
lemma cayleyEquiv_apply_extension {A B : H →ₗ.[ℂ] H} (hAB : A ≤ B)
    (hsym : B.IsFormalAdjoint B)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) (ψ : A.domain) :
    cayleyEquiv hsym hplus hminus (A ψ - (-I) • (ψ : H)) = A ψ - I • (ψ : H) := by
  have hmem : (ψ : H) ∈ B.domain := hAB.1 ψ.2
  have hval : A ψ = B ⟨(ψ : H), hmem⟩ := hAB.2 (x := ψ) (y := ⟨(ψ : H), hmem⟩) rfl
  rw [cayleyEquiv_apply, neg_smul, sub_neg_eq_add, hval]
  exact Spectra.Cayley.cayleyTransform_apply_resolvent hsym hplus ⟨(ψ : H), hmem⟩

omit [CompleteSpace H] in
/-- **Key range computation.** The Cayley equivalence of an extension `B ≥ A` maps
`ran(A + i)` (spelled `rangeSubmodule (A := A) (-I)`) onto `ran(A - i)` (spelled
`rangeSubmodule (A := A) I`): on generators, `Aψ + iψ = Bψ + iψ ↦ Bψ - iψ = Aψ - iψ`. -/
lemma map_cayleyEquiv_rangeSubmodule {A B : H →ₗ.[ℂ] H} (hAB : A ≤ B)
    (hsym : B.IsFormalAdjoint B)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) :
    Submodule.map ((cayleyEquiv hsym hplus hminus).toLinearEquiv : H →ₗ[ℂ] H)
        (Spectra.Resolvent.rangeSubmodule (A := A) (-I))
      = Spectra.Resolvent.rangeSubmodule (A := A) I := by
  apply le_antisymm
  · rintro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, ⟨ψ, rfl⟩, rfl⟩ := hy
    exact ⟨ψ, (cayleyEquiv_apply_extension hAB hsym hplus hminus ψ).symm⟩
  · rintro y ⟨ψ, rfl⟩
    rw [Submodule.mem_map]
    exact ⟨A ψ - (-I) • (ψ : H), ⟨ψ, rfl⟩,
      cayleyEquiv_apply_extension hAB hsym hplus hminus ψ⟩

/-- A linear isometry equivalence of the ambient space restricts to a linear isometry
equivalence `p ≃ₗᵢ[ℂ] q` whenever it maps the submodule `p` onto the submodule `q`. The
underlying linear equivalence is `LinearEquiv.submoduleMap` transported along the image
identification `h` via `LinearEquiv.ofEq`; the norm identity is inherited from the ambient
isometry. -/
noncomputable def isometryEquivOfMapEq (e : H ≃ₗᵢ[ℂ] H) {p q : Submodule ℂ H}
    (h : Submodule.map (e.toLinearEquiv : H →ₗ[ℂ] H) p = q) : p ≃ₗᵢ[ℂ] q where
  toLinearEquiv := (e.toLinearEquiv.submoduleMap p).trans (LinearEquiv.ofEq _ q h)
  norm_map' x := by
    simp only [LinearEquiv.trans_apply, Submodule.coe_norm, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.submoduleMap_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map]

omit [CompleteSpace H] in
/-- The restricted isometry equivalence acts as the ambient one. -/
@[simp]
lemma isometryEquivOfMapEq_apply_coe (e : H ≃ₗᵢ[ℂ] H) {p q : Submodule ℂ H}
    (h : Submodule.map (e.toLinearEquiv : H →ₗ[ℂ] H) p = q) (x : p) :
    ((isometryEquivOfMapEq e h x : q) : H) = e (x : H) :=
  rfl

/-- The Cayley equivalence of a self-adjoint extension `B ≥ A` maps `N₊(A)` onto `N₋(A)`:
combine the range computation `map_cayleyEquiv_rangeSubmodule` with the orthogonal
identifications of the deficiency subspaces and `Submodule.map_orthogonal_equiv`. -/
lemma map_cayleyEquiv_deficiencySubspacePlus {A B : H →ₗ.[ℂ] H}
    (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B) (hsym : B.IsFormalAdjoint B)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - I • (ψ : H) = φ) :
    Submodule.map ((cayleyEquiv hsym hplus hminus).toLinearEquiv : H →ₗ[ℂ] H)
        (deficiencySubspacePlus A)
      = deficiencySubspaceMinus A := by
  rw [deficiencySubspacePlus_eq_orthogonal A hdense,
    deficiencySubspaceMinus_eq_orthogonal A hdense,
    Submodule.map_orthogonal_equiv,
    map_cayleyEquiv_rangeSubmodule hAB hsym hplus hminus]

/-- The **deficiency identification induced by a self-adjoint extension** `B ≥ A`: the
restriction of `B`'s Cayley transform to `N₊(A) ≃ₗᵢ[ℂ] N₋(A)`. This is the unitary `V` for
which `B = A_V` (`Spectra.Operator.SelfAdjointExtensionClassification`). -/
noncomputable def inducedDeficiencyEquiv {A B : H →ₗ.[ℂ] H}
    (hdense : Dense (A.domain : Set H)) (hB : IsSelfAdjoint B) (hAB : A ≤ B) :
    (deficiencySubspacePlus A) ≃ₗᵢ[ℂ] (deficiencySubspaceMinus A) :=
  isometryEquivOfMapEq
    (cayleyEquiv (isFormalAdjoint_self_of_isSelfAdjoint hB)
      (Spectra.YosidaHille.isSelfAdjoint_to_surjective hB).1
      (Spectra.YosidaHille.isSelfAdjoint_to_surjective hB).2)
    (map_cayleyEquiv_deficiencySubspacePlus hdense hAB _ _ _)

/-- The induced deficiency identification acts as `B`'s Cayley transform. -/
@[simp]
lemma inducedDeficiencyEquiv_apply_coe {A B : H →ₗ.[ℂ] H}
    (hdense : Dense (A.domain : Set H)) (hB : IsSelfAdjoint B) (hAB : A ≤ B)
    (η : deficiencySubspacePlus A) :
    ((inducedDeficiencyEquiv hdense hB hAB η : deficiencySubspaceMinus A) : H)
      = cayleyEquiv (isFormalAdjoint_self_of_isSelfAdjoint hB)
          (Spectra.YosidaHille.isSelfAdjoint_to_surjective hB).1
          (Spectra.YosidaHille.isSelfAdjoint_to_surjective hB).2 (η : H) :=
  rfl

/-! ### Von Neumann's extension theorem -/

/-- **Von Neumann's extension theorem, "only if" half.** If a densely-defined operator `A`
admits a self-adjoint extension `B`, then the deficiency subspaces of `A` are isometrically
isomorphic: the Cayley transform of `B` is a unitary of `H` carrying
`N₊(A) = ran(A + i)ᗮ` onto `N₋(A) = ran(A - i)ᗮ`. No symmetry of `A` is needed beyond what
`A ≤ B` already forces. -/
theorem nonempty_deficiencyEquiv_of_le_isSelfAdjoint
    {A B : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hB : IsSelfAdjoint B) (hAB : A ≤ B) :
    Nonempty ((deficiencySubspacePlus A) ≃ₗᵢ[ℂ] (deficiencySubspaceMinus A)) :=
  ⟨inducedDeficiencyEquiv hdense hB hAB⟩

/-- **Von Neumann's extension theorem, "if" half.** A symmetric, densely-defined `A` whose
deficiency subspaces are isometrically isomorphic admits a self-adjoint extension — the
closure of the von Neumann extension `A_V`. No closedness of `A` is required. -/
theorem exists_le_isSelfAdjoint_of_nonempty_deficiencyEquiv (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (h : Nonempty ((deficiencySubspacePlus A) ≃ₗᵢ[ℂ] (deficiencySubspaceMinus A))) :
    ∃ B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ A ≤ B := by
  obtain ⟨V⟩ := h
  exact ⟨(vonNeumannExtension A hsym hdense V).closure,
    vonNeumannExtension_isEssentiallySelfAdjoint A hsym hdense V,
    le_trans (le_vonNeumannExtension A hsym hdense V)
      (vonNeumannExtension A hsym hdense V).le_closure⟩

/-- **Von Neumann's extension theorem.** A symmetric, densely-defined operator admits a
self-adjoint extension iff its deficiency subspaces are isometrically isomorphic. Stated for
arbitrary symmetric `A` — closedness is not needed, since `N±(A) = N±(A.closure)` and the "if"
direction extends by `A_V.closure`. -/
theorem exists_le_isSelfAdjoint_iff_nonempty_deficiencyEquiv (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H)) :
    (∃ B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ A ≤ B) ↔
      Nonempty ((deficiencySubspacePlus A) ≃ₗᵢ[ℂ] (deficiencySubspaceMinus A)) := by
  constructor
  · rintro ⟨B, hB, hAB⟩
    exact nonempty_deficiencyEquiv_of_le_isSelfAdjoint hdense hB hAB
  · exact exists_le_isSelfAdjoint_of_nonempty_deficiencyEquiv A hsym hdense

end Spectra.Operator

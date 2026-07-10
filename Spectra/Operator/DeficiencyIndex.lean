/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.DeficiencySubspace
import Spectra.Operator.EssentialSelfAdjointness
import Spectra.YosidaHille.Helpers

/-!
# Deficiency indices

For a densely-defined operator `A : H →ₗ.[ℂ] H`, the **deficiency indices**
`n₊(A) = dim N₊(A)` and `n₋(A) = dim N₋(A)` are the (cardinal) dimensions of the deficiency
subspaces `N₊(A) = ker(A* - i)` and `N₋(A) = ker(A* + i)` studied in
`Spectra.Operator.DeficiencySubspace`. By von Neumann's theory, a closed symmetric operator is
self-adjoint iff both deficiency indices vanish.

This file defines the indices as cardinal-valued ranks of the deficiency subspaces, and proves
the basic sanity fact that self-adjoint operators have vanishing deficiency indices — the
converse direction of von Neumann's criterion, obtained here from the library's existing full
surjectivity result `Spectra.Operator.isSelfAdjoint_to_surjective`.

## Main definitions

* `deficiencyIndexPlus A` — `n₊(A) = Module.rank ℂ N₊(A)`.
* `deficiencyIndexMinus A` — `n₋(A) = Module.rank ℂ N₋(A)`.

## Main statements

* `deficiencySubspacePlus_eq_bot_of_isSelfAdjoint` / `..Minus..` — a self-adjoint `A` has trivial
  deficiency subspaces.
* `deficiencyIndexPlus_eq_zero_of_isSelfAdjoint` / `..Minus..` — hence vanishing deficiency
  indices.
* `deficiencySubspacesBot_iff_denseRange_addSub` — a cross-lane unification: for densely-defined
  `A`, *both* deficiency subspaces are trivial iff `ran(A + i)` and `ran(A - i)` are each dense —
  precisely the hypotheses `hplus`/`hminus` feeding
  `Spectra.Operator.isEssentiallySelfAdjoint_of_denseRange_addSub`. So "zero deficiency indices"
  (in the topological-closure sense) is exactly von Neumann's essential-self-adjointness
  criterion, on the nose. The proof needs no symmetry hypothesis on `A`, only density of its
  domain — it is the general Hilbert-space fact `Sᗮ = ⊥ ↔ Dense S` for a submodule `S`, chased
  through the orthogonal identification `deficiencySubspacePlus_eq_orthogonal` /
  `..Minus_eq_orthogonal` from `Spectra.Operator.DeficiencySubspace`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **`+i` deficiency index** `n₊(A) = dim N₊(A)`, the cardinal dimension of the `+i`
deficiency subspace `ker(A* - i)`. -/
noncomputable def deficiencyIndexPlus (A : H →ₗ.[ℂ] H) : Cardinal :=
  Module.rank ℂ (deficiencySubspacePlus A)

/-- The **`-i` deficiency index** `n₋(A) = dim N₋(A)`, the cardinal dimension of the `-i`
deficiency subspace `ker(A* + i)`. -/
noncomputable def deficiencyIndexMinus (A : H →ₗ.[ℂ] H) : Cardinal :=
  Module.rank ℂ (deficiencySubspaceMinus A)

/-- **Self-adjoint operators have trivial `+i` deficiency subspace.** If `A` is self-adjoint then
`A + i` is (fully) surjective, so `ran(A + i) = ⊤`, whence `N₊(A) = ran(A + i)ᗮ = ⊤ᗮ = ⊥` by
`deficiencySubspacePlus_eq_orthogonal`. -/
theorem deficiencySubspacePlus_eq_bot_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    deficiencySubspacePlus A = ⊥ := by
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hsurj : ∀ φ : H, ∃ ψ : A.domain, A ψ - (-I) • (ψ : H) = φ := by
    have h := (Spectra.YosidaHille.isSelfAdjoint_to_surjective hA).1
    simpa [neg_smul, sub_neg_eq_add] using h
  have hrange_top : Spectra.Resolvent.rangeSubmodule (A := A) (-I) = ⊤ :=
    Submodule.eq_top_iff'.mpr hsurj
  rw [deficiencySubspacePlus_eq_orthogonal A hdense, hrange_top, Submodule.top_orthogonal_eq_bot]

/-- **Self-adjoint operators have trivial `-i` deficiency subspace.** Mirror of
`deficiencySubspacePlus_eq_bot_of_isSelfAdjoint` for `N₋(A) = ran(A - i)ᗮ`. -/
theorem deficiencySubspaceMinus_eq_bot_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    deficiencySubspaceMinus A = ⊥ := by
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hsurj : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ :=
    (Spectra.YosidaHille.isSelfAdjoint_to_surjective hA).2
  have hrange_top : Spectra.Resolvent.rangeSubmodule (A := A) I = ⊤ :=
    Submodule.eq_top_iff'.mpr hsurj
  rw [deficiencySubspaceMinus_eq_orthogonal A hdense, hrange_top, Submodule.top_orthogonal_eq_bot]

/-- **Self-adjoint operators have vanishing `+i` deficiency index.** -/
theorem deficiencyIndexPlus_eq_zero_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    deficiencyIndexPlus A = 0 :=
  Submodule.rank_eq_zero.mpr (deficiencySubspacePlus_eq_bot_of_isSelfAdjoint hA)

/-- **Self-adjoint operators have vanishing `-i` deficiency index.** -/
theorem deficiencyIndexMinus_eq_zero_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    deficiencyIndexMinus A = 0 :=
  Submodule.rank_eq_zero.mpr (deficiencySubspaceMinus_eq_bot_of_isSelfAdjoint hA)

/-! ### Cross-lane unification with the dense-range essential-self-adjointness criterion -/

/-- **Both deficiency subspaces vanish iff `ran(A ± i)` are each dense.** For densely-defined `A`
(no symmetry required), `N₊(A) = ⊥ ∧ N₋(A) = ⊥` is *exactly* the pair of dense-range hypotheses
`hplus`/`hminus` of `isEssentiallySelfAdjoint_of_denseRange_addSub`. The proof rewrites each
deficiency subspace as an orthogonal complement of a range submodule
(`deficiencySubspacePlus_eq_orthogonal`, `..Minus_eq_orthogonal`) and then applies the general
Hilbert-space fact `Sᗮ = ⊥ ↔ Dense (S : Set H)`, itself the composite of
`Submodule.dense_iff_topologicalClosure_eq_top` and `Submodule.topologicalClosure_eq_top_iff`. -/
theorem deficiencySubspacesBot_iff_denseRange_addSub {A : H →ₗ.[ℂ] H}
    (hdense : Dense (A.domain : Set H)) :
    (deficiencySubspacePlus A = ⊥ ∧ deficiencySubspaceMinus A = ⊥) ↔
      (Dense (Set.range fun x : A.domain => A x + I • (x : H)) ∧
       Dense (Set.range fun x : A.domain => A x - I • (x : H))) := by
  have hPlus : deficiencySubspacePlus A = (Spectra.Resolvent.rangeSubmodule (A := A) (-I))ᗮ :=
    deficiencySubspacePlus_eq_orthogonal A hdense
  have hMinus : deficiencySubspaceMinus A = (Spectra.Resolvent.rangeSubmodule (A := A) I)ᗮ :=
    deficiencySubspaceMinus_eq_orthogonal A hdense
  have hRangePlusEq : (Spectra.Resolvent.rangeSubmodule (A := A) (-I) : Set H)
      = Set.range fun x : A.domain => A x + I • (x : H) := by
    ext y
    simp only [Spectra.Resolvent.rangeSubmodule, Set.mem_range]
    constructor
    · rintro ⟨ψ, rfl⟩; exact ⟨ψ, by simp [neg_smul, sub_neg_eq_add]⟩
    · rintro ⟨ψ, rfl⟩; exact ⟨ψ, by simp [neg_smul, sub_neg_eq_add]⟩
  have hRangeMinusEq : (Spectra.Resolvent.rangeSubmodule (A := A) I : Set H)
      = Set.range fun x : A.domain => A x - I • (x : H) := rfl
  constructor
  · rintro ⟨hP, hM⟩
    constructor
    · rw [← hRangePlusEq, Submodule.dense_iff_topologicalClosure_eq_top,
        Submodule.topologicalClosure_eq_top_iff, ← hPlus]
      exact hP
    · rw [← hRangeMinusEq, Submodule.dense_iff_topologicalClosure_eq_top,
        Submodule.topologicalClosure_eq_top_iff, ← hMinus]
      exact hM
  · rintro ⟨hP, hM⟩
    refine ⟨hPlus ▸ ?_, hMinus ▸ ?_⟩
    · rw [← Submodule.topologicalClosure_eq_top_iff,
        ← Submodule.dense_iff_topologicalClosure_eq_top, hRangePlusEq]
      exact hP
    · rw [← Submodule.topologicalClosure_eq_top_iff,
        ← Submodule.dense_iff_topologicalClosure_eq_top, hRangeMinusEq]
      exact hM

end Spectra.Operator

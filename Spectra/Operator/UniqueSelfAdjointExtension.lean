/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SelfAdjointExtensionClassification
import Spectra.Operator.DeficiencyIndex

/-!
# Essential self-adjointness ⟺ unique self-adjoint extension

The classical characterization closing the loop between the essential-self-adjointness layer
(`Spectra.Operator.EssentialSelfAdjointness`) and von Neumann's classification
(`Spectra.Operator.SelfAdjointExtensionClassification`): a symmetric, densely-defined operator
is essentially self-adjoint **iff** it admits exactly one self-adjoint extension
(`isEssentiallySelfAdjoint_iff_existsUnique_le_isSelfAdjoint`).

*Forward*: if `Ā` is self-adjoint it is an extension, and any self-adjoint `B ≥ A` contains
`Ā` (closures are minimal closed extensions), hence equals it (self-adjoint operators are
maximal, `Spectra.YosidaHille.IsSelfAdjoint.eq_of_le`). No symmetry hypothesis is even needed
for this half.

*Converse*: if the extension is unique, the deficiency subspaces of `Ā` must vanish. Otherwise
pick `η₀ ≠ 0` in `N₊(Ā)` and a deficiency unitary `V` (one exists by the N4 "only if", since an
extension exists); then `V` and `V` followed by `-1` are **distinct** unitaries, so by
injectivity of the von Neumann correspondence `A_V ≠ A_{-V}` — yet uniqueness forces both to
equal the one extension. Vanishing deficiency subspaces give dense ranges
(`deficiencySubspacesBot_iff_denseRange_addSub`), hence `Ā` is self-adjoint
(`isEssentiallySelfAdjoint_of_denseRange_addSub` at `Ā`, whose closure is itself).

Together with the classification this yields the full trichotomy: a closed symmetric operator
has exactly one self-adjoint extension (⟺ it is self-adjoint), none (`N₊ ≇ N₋`), or many —
`exists_ne_of_not_isEssentiallySelfAdjoint` records the "at least two" half.

## Main statements

* `closure_isFormalAdjoint` — the closure of a symmetric densely-defined operator is symmetric.
* `existsUnique_le_isSelfAdjoint_of_isEssentiallySelfAdjoint` — essential self-adjointness
  gives existence and uniqueness of the self-adjoint extension (namely `A.closure`).
* `isEssentiallySelfAdjoint_of_existsUnique_le_isSelfAdjoint` — the converse.
* `isEssentiallySelfAdjoint_iff_existsUnique_le_isSelfAdjoint` — **the characterization**.
* `exists_ne_of_not_isEssentiallySelfAdjoint` — the dichotomy: extendable but not essentially
  self-adjoint means at least two distinct self-adjoint extensions.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Section X.1.
* [Weidmann, *Linear Operators in Hilbert Spaces*][weidmann1980].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The closure of a symmetric operator is symmetric**: `Ā ≤ Ā*` via
`Ā ≤ A* = Ā*`. (Extracted from the opening of
`isEssentiallySelfAdjoint_of_denseRange_addSub`'s proof, where it is derived inline.) -/
theorem closure_isFormalAdjoint {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) :
    A.closure.IsFormalAdjoint A.closure := by
  have hclosable : A.IsClosable := symmetric_isClosable hsym hdense
  have hcl_le_adj : A.closure ≤ A.adjoint := closure_le_adjoint hsym hdense
  have hcl_adj_eq : A.closure.adjoint = A.adjoint := closure_adjoint_eq_adjoint hdense hclosable
  exact isFormalAdjoint_of_le_adjoint (dense_closure_domain hdense) (hcl_adj_eq ▸ hcl_le_adj)

/-- **Essential self-adjointness gives a unique self-adjoint extension** — namely the closure.
Any self-adjoint `B ≥ A` is closed, hence contains `Ā`, hence equals it by maximality of
self-adjoint operators. (This half needs no symmetry hypothesis: it is packaged into
`IsEssentiallySelfAdjoint` itself.) -/
theorem existsUnique_le_isSelfAdjoint_of_isEssentiallySelfAdjoint {A : H →ₗ.[ℂ] H}
    (hA : IsEssentiallySelfAdjoint A) :
    ∃! B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ A ≤ B := by
  refine ⟨A.closure, ⟨hA, A.le_closure⟩, ?_⟩
  rintro B ⟨hB, hAB⟩
  have hcl_le : A.closure ≤ B := by
    have h := hB.isClosed.isClosable.closure_mono hAB
    rwa [IsClosed.closure_eq_self hB.isClosed] at h
  exact (Spectra.YosidaHille.IsSelfAdjoint.eq_of_le hA hB hcl_le).symm

/-- **Uniqueness of the self-adjoint extension forces essential self-adjointness.** If the
deficiency subspaces of `Ā` were nontrivial, composing a deficiency unitary with `-1` would
produce a second, distinct von Neumann extension of `Ā` (injectivity of `V ↦ A_V`),
contradicting uniqueness; so they vanish, the ranges `ran(Ā ± i)` are dense, and the
dense-range criterion makes `Ā` self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_existsUnique_le_isSelfAdjoint {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (h : ∃! B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ A ≤ B) :
    IsEssentiallySelfAdjoint A := by
  obtain ⟨B, ⟨hB, hAB⟩, huniq⟩ := h
  -- the closure `Ā`: symmetric, densely defined, closed
  have hclosable : A.IsClosable := symmetric_isClosable hsym hdense
  have hsymC : A.closure.IsFormalAdjoint A.closure := closure_isFormalAdjoint hsym hdense
  have hdenseC : Dense (A.closure.domain : Set H) := dense_closure_domain hdense
  have hclosedC : A.closure.IsClosed := hclosable.closure_isClosed
  -- `B` extends the closure as well
  have hAB' : A.closure ≤ B := by
    have h := hB.isClosed.isClosable.closure_mono hAB
    rwa [IsClosed.closure_eq_self hB.isClosed] at h
  -- a deficiency unitary for `Ā` exists, since a self-adjoint extension exists
  obtain ⟨V⟩ := nonempty_deficiencyEquiv_of_le_isSelfAdjoint hdenseC hB hAB'
  -- both deficiency subspaces of `Ā` vanish
  have hbotP : deficiencySubspacePlus A.closure = ⊥ := by
    by_contra hne
    obtain ⟨η₀, hη₀mem, hη₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    -- two DISTINCT deficiency unitaries: `V` and `V` followed by `-1`
    set W : deficiencySubspacePlus A.closure ≃ₗᵢ[ℂ] deficiencySubspaceMinus A.closure :=
      V.trans (LinearIsometryEquiv.neg ℂ) with hW
    -- their von Neumann extensions are both self-adjoint extensions of `A`, hence both `= B`
    have hle : ∀ U : deficiencySubspacePlus A.closure ≃ₗᵢ[ℂ] deficiencySubspaceMinus A.closure,
        A ≤ vonNeumannExtension A.closure hsymC hdenseC U := fun U =>
      le_trans A.le_closure (le_vonNeumannExtension A.closure hsymC hdenseC U)
    have hVB : vonNeumannExtension A.closure hsymC hdenseC V = B :=
      huniq _ ⟨vonNeumannExtension_isSelfAdjoint A.closure hsymC hdenseC hclosedC V, hle V⟩
    have hWB : vonNeumannExtension A.closure hsymC hdenseC W = B :=
      huniq _ ⟨vonNeumannExtension_isSelfAdjoint A.closure hsymC hdenseC hclosedC W, hle W⟩
    -- injectivity of the correspondence forces `V = W`, i.e. `Vη₀ = -Vη₀`
    have hVW : V = W :=
      vonNeumannExtension_injective A.closure hsymC hdenseC (hVB.trans hWB.symm)
    have happ : V ⟨η₀, hη₀mem⟩ = -(V ⟨η₀, hη₀mem⟩) := by
      conv_lhs => rw [hVW]
      simp [hW, LinearIsometryEquiv.neg]
    have hzero : V ⟨η₀, hη₀mem⟩ = 0 := by
      have h2 : (2 : ℂ) • V ⟨η₀, hη₀mem⟩ = 0 := by
        rw [two_smul]
        nth_rewrite 1 [happ]
        exact neg_add_cancel _
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    have : (⟨η₀, hη₀mem⟩ : deficiencySubspacePlus A.closure) = 0 :=
      V.injective (by rw [hzero, map_zero])
    exact hη₀ne (by simpa using congrArg Subtype.val this)
  have hbotM : deficiencySubspaceMinus A.closure = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hsymm : V.symm ⟨y, hy⟩ = 0 :=
      Subtype.ext ((Submodule.eq_bot_iff _).mp hbotP _ (V.symm ⟨y, hy⟩).2)
    have := congrArg V hsymm
    rw [V.apply_symm_apply, map_zero] at this
    simpa using congrArg Subtype.val this
  -- vanishing deficiency subspaces ⟹ dense ranges ⟹ `Ā` self-adjoint
  obtain ⟨hplus, hminus⟩ :=
    (deficiencySubspacesBot_iff_denseRange_addSub hdenseC).mp ⟨hbotP, hbotM⟩
  have hCsa : IsSelfAdjoint A.closure.closure :=
    isEssentiallySelfAdjoint_of_denseRange_addSub hsymC hdenseC hplus hminus
  rwa [IsClosed.closure_eq_self hclosedC] at hCsa

/-- **Essential self-adjointness ⟺ unique self-adjoint extension** — the classical
characterization, for a symmetric densely-defined operator. -/
theorem isEssentiallySelfAdjoint_iff_existsUnique_le_isSelfAdjoint {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H)) :
    IsEssentiallySelfAdjoint A ↔ ∃! B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ A ≤ B :=
  ⟨existsUnique_le_isSelfAdjoint_of_isEssentiallySelfAdjoint,
    isEssentiallySelfAdjoint_of_existsUnique_le_isSelfAdjoint hsym hdense⟩

/-- **The extension dichotomy**: a symmetric densely-defined operator that admits some
self-adjoint extension but is not essentially self-adjoint admits at least two distinct
ones. (By the classification there is then a whole unitary family, one for each
`V : N₊(Ā) ≃ₗᵢ N₋(Ā)`.) -/
theorem exists_ne_of_not_isEssentiallySelfAdjoint {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    (hnot : ¬ IsEssentiallySelfAdjoint A)
    (hex : ∃ B : H →ₗ.[ℂ] H, IsSelfAdjoint B ∧ A ≤ B) :
    ∃ B C : H →ₗ.[ℂ] H,
      (IsSelfAdjoint B ∧ A ≤ B) ∧ (IsSelfAdjoint C ∧ A ≤ C) ∧ B ≠ C := by
  obtain ⟨B, hPB⟩ := hex
  by_contra hcon
  push Not at hcon
  exact hnot ((isEssentiallySelfAdjoint_iff_existsUnique_le_isSelfAdjoint hsym hdense).mpr
    ⟨B, hPB, fun C hPC => hcon C B hPC hPB⟩)

end Spectra.Operator

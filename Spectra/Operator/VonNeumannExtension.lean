/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.DeficiencySubspace
import Spectra.Operator.EssentialSelfAdjointness

/-!
# The von Neumann extension `A_V`

For a symmetric, densely-defined `A : H →ₗ.[ℂ] H` and a unitary identification
`V : N₊(A) ≃ₗᵢ[ℂ] N₋(A)` of its deficiency subspaces (`Spectra.Operator.deficiencySubspacePlus`
/ `..Minus`), von Neumann's extension `A_V` is the restriction of the adjoint `A*` to

  `D(A_V) = D(A) ⊔ {η - Vη | η ∈ N₊(A)}`,

so that `A_V (x + η - Vη) = Ax + iη + iVη` (using `A*η = iη` on `N₊` and `A*(Vη) = -iVη` on
`N₋`). This file builds the construction layer: the defect map `η ↦ η - Vη`, the extension
domain, the extension itself as a genuine `LinearPMap`, the extension property `A ≤ A_V`, the
canonical decomposition of domain elements, and the explicit action formula. Symmetry and
(essential) self-adjointness of `A_V` are proved downstream in
`Spectra.Operator.VonNeumannExtensionSelfAdjoint`.

Defining `A_V` as a restriction of `A*` makes well-definedness automatic — no uniqueness of the
decomposition `u = x + η - Vη` is ever needed, because the action is inherited from the single
linear map `A*` rather than assembled from the pieces.

## Main definitions

* `vonNeumannDefectMap A V` — the linear map `N₊(A) →ₗ[ℂ] H`, `η ↦ η - Vη`.
* `vonNeumannDomain A V` — the extension domain `D(A) ⊔ ran(1 - V)`.
* `vonNeumannExtension hsym hdense V` — the extension `A_V`, as `A*` restricted to
  `vonNeumannDomain A V`.

## Main statements

* `le_vonNeumannExtension` — `A ≤ A_V`.
* `vonNeumannExtension_dense_domain` — `D(A_V)` is dense.
* `vonNeumannDomain_cases` — every `u ∈ D(A_V)` is of the form `x + η - Vη`.
* `vonNeumannExtension_apply_add_defect` — `A_V (x + η - Vη) = Ax + iη + iVη`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Theorem X.2.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →ₗ.[ℂ] H)

/-! ### Adjoint-eigenvector access for the deficiency subspaces -/

/-- Membership in `N₊(A)` places a vector in the adjoint domain. -/
theorem mem_adjoint_domain_of_mem_deficiencySubspacePlus {χ : H}
    (hχ : χ ∈ deficiencySubspacePlus A) : χ ∈ A.adjoint.domain := by
  obtain ⟨h, -⟩ := hχ
  exact h

/-- Membership in `N₋(A)` places a vector in the adjoint domain. -/
theorem mem_adjoint_domain_of_mem_deficiencySubspaceMinus {χ : H}
    (hχ : χ ∈ deficiencySubspaceMinus A) : χ ∈ A.adjoint.domain := by
  obtain ⟨h, -⟩ := hχ
  exact h

/-- On `N₊(A)` the adjoint acts as multiplication by `i`: `A*χ = iχ`. -/
theorem adjoint_apply_of_mem_deficiencySubspacePlus {χ : H}
    (hχ : χ ∈ deficiencySubspacePlus A) (h : χ ∈ A.adjoint.domain) :
    A.adjoint ⟨χ, h⟩ = I • χ := by
  obtain ⟨_h', hval⟩ := hχ
  exact hval

/-- On `N₋(A)` the adjoint acts as multiplication by `-i`: `A*χ = -iχ`. -/
theorem adjoint_apply_of_mem_deficiencySubspaceMinus {χ : H}
    (hχ : χ ∈ deficiencySubspaceMinus A) (h : χ ∈ A.adjoint.domain) :
    A.adjoint ⟨χ, h⟩ = (-I) • χ := by
  obtain ⟨_h', hval⟩ := hχ
  exact hval

/-! ### The defect map and the extension domain -/

/-- The **defect map** `1 - V : N₊(A) →ₗ[ℂ] H`, `η ↦ η - Vη`, whose range complements `D(A)`
inside the extension domain. -/
def vonNeumannDefectMap (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    deficiencySubspacePlus A →ₗ[ℂ] H :=
  (deficiencySubspacePlus A).subtype -
    (deficiencySubspaceMinus A).subtype ∘ₗ V.toLinearEquiv.toLinearMap

@[simp]
theorem vonNeumannDefectMap_apply
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (η : deficiencySubspacePlus A) :
    vonNeumannDefectMap A V η = (η : H) - ((V η : deficiencySubspaceMinus A) : H) :=
  rfl

/-- The **von Neumann extension domain** `D(A_V) = D(A) ⊔ {η - Vη | η ∈ N₊(A)}`. -/
def vonNeumannDomain (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    Submodule ℂ H :=
  A.domain ⊔ LinearMap.range (vonNeumannDefectMap A V)

/-- Canonical membership: `x + η - Vη ∈ D(A_V)` for `x ∈ D(A)`, `η ∈ N₊(A)`. -/
theorem mem_vonNeumannDomain
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (x : A.domain) (η : deficiencySubspacePlus A) :
    (x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H) ∈ vonNeumannDomain A V := by
  have h := Submodule.add_mem_sup x.2
    (LinearMap.mem_range_self (vonNeumannDefectMap A V) η)
  simpa [vonNeumannDomain, add_sub_assoc] using h

/-- `D(A) ≤ D(A_V)`. -/
theorem domain_le_vonNeumannDomain
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    A.domain ≤ vonNeumannDomain A V :=
  le_sup_left

/-- Canonical decomposition: every element of `D(A_V)` has the form `x + η - Vη` with
`x ∈ D(A)`, `η ∈ N₊(A)`. (The decomposition need not be unique in this generality; nothing
downstream requires uniqueness.) -/
theorem vonNeumannDomain_cases
    {V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A}
    {u : H} (hu : u ∈ vonNeumannDomain A V) :
    ∃ (x : A.domain) (η : deficiencySubspacePlus A),
      u = (x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
  obtain ⟨η, rfl⟩ := hb
  exact ⟨⟨a, ha⟩, η, by rw [← hab, vonNeumannDefectMap_apply, add_sub_assoc]⟩

/-- The extension domain sits inside the adjoint domain — the fact making the restriction of
`A*` well-typed. Symmetry enters only to place `D(A)` inside `D(A*)`. -/
theorem vonNeumannDomain_le_adjoint_domain (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    vonNeumannDomain A V ≤ A.adjoint.domain := by
  refine sup_le (hsym.le_adjoint hdense).1 ?_
  rintro u ⟨η, rfl⟩
  rw [vonNeumannDefectMap_apply]
  exact A.adjoint.domain.sub_mem
    (mem_adjoint_domain_of_mem_deficiencySubspacePlus A η.2)
    (mem_adjoint_domain_of_mem_deficiencySubspaceMinus A (V η).2)

/-! ### The extension -/

/-- **The von Neumann extension** `A_V`: the adjoint `A*` restricted to
`D(A) ⊔ {η - Vη | η ∈ N₊(A)}`. Well-definedness is inherited from `A*`, so no uniqueness of
the decomposition is needed to define the action. -/
noncomputable def vonNeumannExtension (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) : H →ₗ.[ℂ] H where
  domain := vonNeumannDomain A V
  toFun := A.adjoint.toFun ∘ₗ
    Submodule.inclusion (vonNeumannDomain_le_adjoint_domain A hsym hdense V)

@[simp]
theorem vonNeumannExtension_domain (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    (vonNeumannExtension A hsym hdense V).domain = vonNeumannDomain A V :=
  rfl

/-- `A_V` acts as the adjoint `A*`. -/
theorem vonNeumannExtension_apply (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (u : (vonNeumannExtension A hsym hdense V).domain) :
    vonNeumannExtension A hsym hdense V u
      = A.adjoint ⟨(u : H), vonNeumannDomain_le_adjoint_domain A hsym hdense V u.2⟩ :=
  rfl

/-- **`A_V` extends `A`.** -/
theorem le_vonNeumannExtension (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    A ≤ vonNeumannExtension A hsym hdense V := by
  refine ⟨domain_le_vonNeumannDomain A V, ?_⟩
  intro x y hxy
  have hxadj : (x : H) ∈ A.adjoint.domain := (hsym.le_adjoint hdense).1 x.2
  have hAx : A x = A.adjoint ⟨(x : H), hxadj⟩ :=
    (hsym.le_adjoint hdense).2 (x := x) (y := ⟨(x : H), hxadj⟩) rfl
  rw [hAx, vonNeumannExtension_apply]
  congr 1
  exact Subtype.ext hxy

/-- `D(A_V)` is dense, since it contains the dense `D(A)`. -/
theorem vonNeumannExtension_dense_domain (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    Dense ((vonNeumannExtension A hsym hdense V).domain : Set H) :=
  hdense.mono (SetLike.coe_subset_coe.mpr (domain_le_vonNeumannDomain A V))

/-! ### The action formula -/

/-- **The action formula**: `A_V (x + η - Vη) = Ax + iη + iVη`. The three summands are handled
by `A* ⊇ A` (symmetry), `A*η = iη` on `N₊`, and `A*(Vη) = -iVη` on `N₋`. -/
theorem vonNeumannExtension_apply_add_defect (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (V : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (x : A.domain) (η : deficiencySubspacePlus A)
    (u : (vonNeumannExtension A hsym hdense V).domain)
    (huv : (u : H) = (x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H)) :
    vonNeumannExtension A hsym hdense V u
      = A x + I • (η : H) + I • ((V η : deficiencySubspaceMinus A) : H) := by
  have hxadj : (x : H) ∈ A.adjoint.domain := (hsym.le_adjoint hdense).1 x.2
  have hηadj : (η : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspacePlus A η.2
  have hζadj : ((V η : deficiencySubspaceMinus A) : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspaceMinus A (V η).2
  -- rewrite the argument of `A*` as a sum/difference inside the adjoint domain
  have hsplit : A.adjoint ⟨(u : H), vonNeumannDomain_le_adjoint_domain A hsym hdense V u.2⟩
      = A.adjoint ⟨(x : H), hxadj⟩ + A.adjoint ⟨(η : H), hηadj⟩
        - A.adjoint ⟨((V η : deficiencySubspaceMinus A) : H), hζadj⟩ := by
    have hmem : (x : H) + (η : H) ∈ A.adjoint.domain := A.adjoint.domain.add_mem hxadj hηadj
    have hadd : A.adjoint ⟨(x : H) + (η : H), hmem⟩
        = A.adjoint ⟨(x : H), hxadj⟩ + A.adjoint ⟨(η : H), hηadj⟩ := by
      have := A.adjoint.map_add ⟨(x : H), hxadj⟩ ⟨(η : H), hηadj⟩
      convert this using 2
    have hsub : A.adjoint ⟨(x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H),
        A.adjoint.domain.sub_mem hmem hζadj⟩
        = A.adjoint ⟨(x : H) + (η : H), hmem⟩
          - A.adjoint ⟨((V η : deficiencySubspaceMinus A) : H), hζadj⟩ := by
      have := A.adjoint.map_sub ⟨(x : H) + (η : H), hmem⟩
        ⟨((V η : deficiencySubspaceMinus A) : H), hζadj⟩
      convert this using 2
    have harg : (⟨(u : H), vonNeumannDomain_le_adjoint_domain A hsym hdense V u.2⟩ :
        A.adjoint.domain)
        = ⟨(x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H),
            A.adjoint.domain.sub_mem hmem hζadj⟩ := Subtype.ext huv
    rw [harg, hsub, hadd]
  have hAx : A x = A.adjoint ⟨(x : H), hxadj⟩ :=
    (hsym.le_adjoint hdense).2 (x := x) (y := ⟨(x : H), hxadj⟩) rfl
  rw [vonNeumannExtension_apply, hsplit, ← hAx,
    adjoint_apply_of_mem_deficiencySubspacePlus A η.2 hηadj,
    adjoint_apply_of_mem_deficiencySubspaceMinus A (V η).2 hζadj,
    neg_smul, sub_neg_eq_add]

end Spectra.Operator

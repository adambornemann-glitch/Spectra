/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.VonNeumannFormula

/-!
# The partial von Neumann extension `A_V` and the boundary form

`Spectra.Operator.vonNeumannExtension` builds the extension `A_V` of a symmetric,
densely-defined `A : H →ₗ.[ℂ] H` from a **unitary** deficiency identification
`V : N₊(A) ≃ₗᵢ[ℂ] N₋(A)`, and such `A_V` are exactly the self-adjoint extensions. This file
generalizes the construction to a **partial isometry**: an isometry `V : F →ₗᵢ[ℂ] N₋(A)`
defined on a submodule `F ≤ N₊(A)`, yielding

  `A_V := A*` restricted to `D(A_V) = D(A) ⊔ {η - Vη | η ∈ F}`,

which is a **symmetric** (in general no longer self-adjoint) extension of `A`. The
classification theorem — every symmetric extension of a closed symmetric `A` arises this way,
the *second von Neumann formula* — is proved downstream in
`Spectra.Operator.SymmetricExtensionClassification`.

The engine for symmetry is the **boundary form**: for `u = ψ + η + ξ` and `w = ψ' + η' + ξ'`
in `D(A*)` decomposed by the first von Neumann formula (`Spectra.Operator.vonNeumannFormula`),

  `⟪A*u, w⟫ - ⟪u, A*w⟫ = -2i·(⟪η, η'⟫ - ⟪ξ, ξ'⟫)`,

so the boundary form vanishes on `D(A_V)` exactly because `V` preserves inner products. The
same identity read backwards is what forces every symmetric extension to induce a partial
isometry, so it is stated here once, in full generality.

## Main definitions

* `vonNeumannDefectMapOn hF V` — the defect map `η ↦ η - Vη` on `F ≤ N₊(A)`.
* `vonNeumannDomainOn hF V` — the extension domain `D(A) ⊔ ran(1 - V)`.
* `vonNeumannExtensionOn hsym hdense hF V` — the partial von Neumann extension `A_V`.

## Main statements

* `adjoint_boundaryForm` — the boundary form identity on first-formula decompositions.
* `adjoint_boundaryForm_defect` — its defect-only specialization (`ψ = ψ' = 0`).
* `le_vonNeumannExtensionOn` — `A ≤ A_V`.
* `vonNeumannExtensionOn_apply_add_defect` — the action formula `A_V(x + η - Vη) = Ax + iη + iVη`.
* `vonNeumannExtensionOn_isFormalAdjoint` — **`A_V` is symmetric**, for any partial isometry.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Section X.1.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The boundary form -/

/-- **The boundary form identity.** On first-formula decompositions `u = ψ + η + ξ`,
`w = ψ' + η' + ξ'` of elements of `D(A*)`, the sesquilinear boundary form of `A*` collapses to
the defect components:

  `⟪A*u, w⟫ - ⟪u, A*w⟫ = -2i·(⟪η, η'⟫ - ⟪ξ, ξ'⟫)`.

All `D(A)`-cross terms die against the eigenvalue identities `A*η = iη`, `A*ξ = -iξ` and the
symmetry of `A`. -/
theorem adjoint_boundaryForm (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (ψ ψ' : A.domain) (η η' : deficiencySubspacePlus A) (ξ ξ' : deficiencySubspaceMinus A)
    {u w : H} (hu : u ∈ A.adjoint.domain) (hw : w ∈ A.adjoint.domain)
    (hud : u = (ψ : H) + (η : H) + (ξ : H)) (hwd : w = (ψ' : H) + (η' : H) + (ξ' : H)) :
    ⟪A.adjoint ⟨u, hu⟩, w⟫_ℂ - ⟪u, A.adjoint ⟨w, hw⟩⟫_ℂ
      = -2 * I * (⟪(η : H), (η' : H)⟫_ℂ - ⟪(ξ : H), (ξ' : H)⟫_ℂ) := by
  rw [adjoint_apply_add_deficiency A hsym hdense ψ η ξ hu hud,
    adjoint_apply_add_deficiency A hsym hdense ψ' η' ξ' hw hwd, hud, hwd]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_I]
  rw [hsym ψ ψ',
    inner_apply_deficiencySubspacePlus A hdense η' ψ,
    inner_apply_deficiencySubspaceMinus A hdense ξ' ψ,
    deficiencySubspacePlus_inner_apply A hdense η ψ',
    deficiencySubspaceMinus_inner_apply A hdense ξ ψ']
  ring

/-- **Defect-only boundary form**: for `u = η + ξ`, `w = η' + ξ'` with no `D(A)`-component,
`⟪A*u, w⟫ - ⟪u, A*w⟫ = -2i·(⟪η, η'⟫ - ⟪ξ, ξ'⟫)`. -/
theorem adjoint_boundaryForm_defect (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (η η' : deficiencySubspacePlus A) (ξ ξ' : deficiencySubspaceMinus A)
    {u w : H} (hu : u ∈ A.adjoint.domain) (hw : w ∈ A.adjoint.domain)
    (hud : u = (η : H) + (ξ : H)) (hwd : w = (η' : H) + (ξ' : H)) :
    ⟪A.adjoint ⟨u, hu⟩, w⟫_ℂ - ⟪u, A.adjoint ⟨w, hw⟩⟫_ℂ
      = -2 * I * (⟪(η : H), (η' : H)⟫_ℂ - ⟪(ξ : H), (ξ' : H)⟫_ℂ) :=
  adjoint_boundaryForm A hsym hdense 0 0 η η' ξ ξ' hu hw
    (by simpa using hud) (by simpa using hwd)

/-! ### The partial defect map and extension domain -/

variable (A : H →ₗ.[ℂ] H) {F : Submodule ℂ H}

/-- The **partial defect map** `1 - V : F →ₗ[ℂ] H`, `η ↦ η - Vη`, for an isometry
`V : F →ₗᵢ[ℂ] N₋(A)` on a submodule `F ≤ N₊(A)`. -/
def vonNeumannDefectMapOn (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) : F →ₗ[ℂ] H :=
  F.subtype - (deficiencySubspaceMinus A).subtype ∘ₗ V.toLinearMap

@[simp]
theorem vonNeumannDefectMapOn_apply (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) (η : F) :
    vonNeumannDefectMapOn A V η = (η : H) - ((V η : deficiencySubspaceMinus A) : H) :=
  rfl

/-- The **partial von Neumann extension domain** `D(A_V) = D(A) ⊔ {η - Vη | η ∈ F}`. -/
def vonNeumannDomainOn (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) : Submodule ℂ H :=
  A.domain ⊔ LinearMap.range (vonNeumannDefectMapOn A V)

/-- Canonical membership: `x + η - Vη ∈ D(A_V)` for `x ∈ D(A)`, `η ∈ F`. -/
theorem mem_vonNeumannDomainOn (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) (x : A.domain) (η : F) :
    (x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H)
      ∈ vonNeumannDomainOn A V := by
  have h := Submodule.add_mem_sup x.2
    (LinearMap.mem_range_self (vonNeumannDefectMapOn A V) η)
  simpa [vonNeumannDomainOn, add_sub_assoc] using h

/-- `D(A) ≤ D(A_V)`. -/
theorem domain_le_vonNeumannDomainOn (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    A.domain ≤ vonNeumannDomainOn A V :=
  le_sup_left

/-- Canonical decomposition: every element of `D(A_V)` has the form `x + η - Vη` with
`x ∈ D(A)`, `η ∈ F`. -/
theorem vonNeumannDomainOn_cases {V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A} {u : H}
    (hu : u ∈ vonNeumannDomainOn A V) :
    ∃ (x : A.domain) (η : F),
      u = (x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
  obtain ⟨η, rfl⟩ := hb
  exact ⟨⟨a, ha⟩, η, by rw [← hab, vonNeumannDefectMapOn_apply, add_sub_assoc]⟩

/-- The extension domain sits inside the adjoint domain. -/
theorem vonNeumannDomainOn_le_adjoint_domain (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    vonNeumannDomainOn A V ≤ A.adjoint.domain := by
  refine sup_le (hsym.le_adjoint hdense).1 ?_
  rintro u ⟨η, rfl⟩
  rw [vonNeumannDefectMapOn_apply]
  exact A.adjoint.domain.sub_mem
    (mem_adjoint_domain_of_mem_deficiencySubspacePlus A (hF η.2))
    (mem_adjoint_domain_of_mem_deficiencySubspaceMinus A (V η).2)

/-! ### The extension -/

/-- **The partial von Neumann extension** `A_V`: the adjoint `A*` restricted to
`D(A) ⊔ {η - Vη | η ∈ F}` for an isometry `V : F →ₗᵢ[ℂ] N₋(A)` on `F ≤ N₊(A)`. For a full
unitary this is `Spectra.Operator.vonNeumannExtension`; in general `A_V` is only symmetric. -/
noncomputable def vonNeumannExtensionOn (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) : H →ₗ.[ℂ] H where
  domain := vonNeumannDomainOn A V
  toFun := A.adjoint.toFun ∘ₗ
    Submodule.inclusion (vonNeumannDomainOn_le_adjoint_domain A hsym hdense hF V)

@[simp]
theorem vonNeumannExtensionOn_domain (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    (vonNeumannExtensionOn A hsym hdense hF V).domain = vonNeumannDomainOn A V :=
  rfl

/-- `A_V` acts as the adjoint `A*`. -/
theorem vonNeumannExtensionOn_apply (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (u : (vonNeumannExtensionOn A hsym hdense hF V).domain) :
    vonNeumannExtensionOn A hsym hdense hF V u
      = A.adjoint ⟨(u : H), vonNeumannDomainOn_le_adjoint_domain A hsym hdense hF V u.2⟩ :=
  rfl

/-- **`A_V` extends `A`.** -/
theorem le_vonNeumannExtensionOn (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    A ≤ vonNeumannExtensionOn A hsym hdense hF V := by
  refine ⟨domain_le_vonNeumannDomainOn A V, ?_⟩
  intro x y hxy
  have hxadj : (x : H) ∈ A.adjoint.domain := (hsym.le_adjoint hdense).1 x.2
  have hAx : A x = A.adjoint ⟨(x : H), hxadj⟩ :=
    (hsym.le_adjoint hdense).2 (x := x) (y := ⟨(x : H), hxadj⟩) rfl
  rw [hAx, vonNeumannExtensionOn_apply]
  congr 1
  exact Subtype.ext hxy

/-- `D(A_V)` is dense, since it contains the dense `D(A)`. -/
theorem vonNeumannExtensionOn_dense_domain (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    Dense ((vonNeumannExtensionOn A hsym hdense hF V).domain : Set H) :=
  hdense.mono (SetLike.coe_subset_coe.mpr (domain_le_vonNeumannDomainOn A V))

/-- **The action formula**: `A_V (x + η - Vη) = Ax + iη + iVη`, via `A* ⊇ A`, `A*η = iη` on
`N₊ ⊇ F`, and `A*(Vη) = -iVη` on `N₋`. -/
theorem vonNeumannExtensionOn_apply_add_defect (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (x : A.domain) (η : F) (u : (vonNeumannExtensionOn A hsym hdense hF V).domain)
    (huv : (u : H) = (x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H)) :
    vonNeumannExtensionOn A hsym hdense hF V u
      = A x + I • (η : H) + I • ((V η : deficiencySubspaceMinus A) : H) := by
  have hxadj : (x : H) ∈ A.adjoint.domain := (hsym.le_adjoint hdense).1 x.2
  have hηadj : (η : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspacePlus A (hF η.2)
  have hζadj : ((V η : deficiencySubspaceMinus A) : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspaceMinus A (V η).2
  have hsplit : A.adjoint
      ⟨(u : H), vonNeumannDomainOn_le_adjoint_domain A hsym hdense hF V u.2⟩
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
    have harg : (⟨(u : H), vonNeumannDomainOn_le_adjoint_domain A hsym hdense hF V u.2⟩ :
        A.adjoint.domain)
        = ⟨(x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H),
            A.adjoint.domain.sub_mem hmem hζadj⟩ := Subtype.ext huv
    rw [harg, hsub, hadd]
  have hAx : A x = A.adjoint ⟨(x : H), hxadj⟩ :=
    (hsym.le_adjoint hdense).2 (x := x) (y := ⟨(x : H), hxadj⟩) rfl
  rw [vonNeumannExtensionOn_apply, hsplit, ← hAx,
    adjoint_apply_of_mem_deficiencySubspacePlus A (hF η.2) hηadj,
    adjoint_apply_of_mem_deficiencySubspaceMinus A (V η).2 hζadj,
    neg_smul, sub_neg_eq_add]

/-! ### Symmetry -/

/-- The partial isometry `V` preserves ambient inner products. -/
theorem inner_coe_map_map_on (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) (η ξ : F) :
    ⟪((V η : deficiencySubspaceMinus A) : H), ((V ξ : deficiencySubspaceMinus A) : H)⟫_ℂ
      = ⟪(η : H), (ξ : H)⟫_ℂ := by
  have h := V.inner_map_map η ξ
  rwa [Submodule.coe_inner, Submodule.coe_inner] at h

/-- **The partial von Neumann extension is symmetric.** The boundary form on
`u = x + η - Vη`, `w = y + η' - Vη'` is `-2i(⟪η, η'⟫ - ⟪Vη, Vη'⟫)`, which vanishes because
`V` is an isometry. -/
theorem vonNeumannExtensionOn_isFormalAdjoint (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hF : F ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    (vonNeumannExtensionOn A hsym hdense hF V).IsFormalAdjoint
      (vonNeumannExtensionOn A hsym hdense hF V) := by
  intro u w
  obtain ⟨x, η, hu⟩ := vonNeumannDomainOn_cases A u.2
  obtain ⟨y, η', hw⟩ := vonNeumannDomainOn_cases A w.2
  have huadj : (u : H) ∈ A.adjoint.domain :=
    vonNeumannDomainOn_le_adjoint_domain A hsym hdense hF V u.2
  have hwadj : (w : H) ∈ A.adjoint.domain :=
    vonNeumannDomainOn_le_adjoint_domain A hsym hdense hF V w.2
  have hbf := adjoint_boundaryForm A hsym hdense x y
    ⟨(η : H), hF η.2⟩ ⟨(η' : H), hF η'.2⟩
    (-(V η)) (-(V η')) huadj hwadj
    (by simpa [sub_eq_add_neg] using hu) (by simpa [sub_eq_add_neg] using hw)
  have hVinner : ⟪(((-(V η) : deficiencySubspaceMinus A)) : H),
      (((-(V η') : deficiencySubspaceMinus A)) : H)⟫_ℂ = ⟪(η : H), (η' : H)⟫_ℂ := by
    rw [Submodule.coe_neg, Submodule.coe_neg, inner_neg_neg]
    exact inner_coe_map_map_on A V η η'
  rw [hVinner, sub_self, mul_zero] at hbf
  have hval : vonNeumannExtensionOn A hsym hdense hF V u = A.adjoint ⟨(u : H), huadj⟩ :=
    vonNeumannExtensionOn_apply A hsym hdense hF V u
  have hval' : vonNeumannExtensionOn A hsym hdense hF V w = A.adjoint ⟨(w : H), hwadj⟩ :=
    vonNeumannExtensionOn_apply A hsym hdense hF V w
  rw [hval, hval']
  exact sub_eq_zero.mp hbf

/-! ### Compatibility with the full von Neumann extension -/

/-- **The partial construction subsumes the original**: at `F = N₊(A)` with a full unitary
`W : N₊(A) ≃ₗᵢ[ℂ] N₋(A)`, the partial von Neumann extension is *definitionally* the original
`Spectra.Operator.vonNeumannExtension` — same domain, same restriction of `A*`. -/
theorem vonNeumannExtensionOn_toLinearIsometry (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (W : deficiencySubspacePlus A ≃ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    vonNeumannExtensionOn A hsym hdense le_rfl W.toLinearIsometry
      = vonNeumannExtension A hsym hdense W :=
  rfl

end Spectra.Operator

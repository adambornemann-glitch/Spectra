/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SymmetricExtension

/-!
# The second von Neumann formula: classification of symmetric extensions

For a **closed**, symmetric, densely-defined `A : H →ₗ.[ℂ] H`, every symmetric extension
`B ≥ A` is a partial von Neumann extension: there are a submodule `F ≤ N₊(A)` and an isometry
`V : F →ₗᵢ[ℂ] N₋(A)` with

  `D(B) = D(A) ⊔ {η - Vη | η ∈ F}`   and   `B = A*|_{D(B)}`,

i.e. `B = vonNeumannExtensionOn A hsym hdense hF V` (`exists_eq_vonNeumannExtensionOn`). This
is the *second von Neumann formula*, completing the extension-theory picture: unitary `V` on
all of `N₊(A)` ⟺ self-adjoint extensions (`Spectra.Operator.SelfAdjointExtensionClassification`),
partial isometries ⟺ symmetric extensions.

## The route

A symmetric extension `B` satisfies `B ≤ B* ≤ A*` (`le_adjoint_of_le_of_isFormalAdjoint`), so
every `u ∈ D(B)` decomposes through the **first** von Neumann formula
(`Spectra.Operator.adjoint_domain_cases`) as `u = ψ + η + ξ`. The induced data are read off
from `D(B)` directly:

* `inducedDefectDomain A B` — the `F`: all `η ∈ N₊(A)` admitting a partner `ξ ∈ N₋(A)` with
  `η + ξ ∈ D(B)`. A submodule with no choice functions needed.
* The partner is **unique** (`defect_partner_unique`): two partners differ by an element of
  `D(B) ∩ N₋(A)`, which vanishes because the boundary form of the symmetric `B` against itself
  is `2i‖ξ‖²` (`eq_zero_of_mem_domain_of_mem_deficiencySubspaceMinus`).
* `inducedPartnerₗ` — the partner as a linear map (linearity from uniqueness), and
  `inducedDefectIsometry` — `V : η ↦ -ξ(η)`, an isometry into `N₋(A)` by the defect boundary
  form `⟪η, η'⟫ = ⟪ξ, ξ'⟫` (`adjoint_boundaryForm_defect` + symmetry of `B`).

The domain identity `D(B) = D(A_V)` (`domain_eq_vonNeumannDomainOn_induced`) then forces
`B = A_V`, since both are restrictions of `A*` (`eq_of_le_of_le_of_domain_eq`).

## Main statements

* `eq_zero_of_mem_domain_of_mem_deficiencySubspaceMinus` — `D(B) ∩ N₋(A) = 0` for symmetric
  `B ≥ A`.
* `defect_partner_unique` — the defect partner is unique.
* `eq_vonNeumannExtensionOn_induced` — `B = A_V` at the induced `(F, V)`.
* `exists_eq_vonNeumannExtensionOn` — **the second von Neumann formula** (existence form).
* `inducedDefectDomain_vonNeumannExtensionOn` — recovery: the induced `F` of `A_V` is `V`'s
  domain (the correspondence is injective in `F`).
* `vonNeumannExtensionOn_inj_apply` — recovery of `V`: pointwise injectivity.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Section X.1.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993], Section 80.
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Symmetric extensions live inside the adjoint -/

/-- A symmetric extension of a densely-defined operator is a restriction of its adjoint:
`A ≤ B` with `B` symmetric gives `B ≤ B* ≤ A*`. -/
theorem le_adjoint_of_le_of_isFormalAdjoint {A B : H →ₗ.[ℂ] H}
    (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B) :
    B ≤ A.adjoint :=
  le_trans (hsymB.le_adjoint (hdense.mono (SetLike.coe_subset_coe.mpr hAB.1)))
    (adjoint_le_adjoint_of_le hdense hAB)

omit [CompleteSpace H] in
/-- Two restrictions of a common operator with equal domains are equal. -/
theorem eq_of_le_of_le_of_domain_eq {B C T : H →ₗ.[ℂ] H} (hB : B ≤ T) (hC : C ≤ T)
    (hdom : B.domain = C.domain) : B = C := by
  have hBC : B ≤ C := by
    refine ⟨hdom.le, fun x y hxy => ?_⟩
    have h1 : B x = T ⟨(x : H), hB.1 x.2⟩ := hB.2 (x := x) (y := ⟨(x : H), hB.1 x.2⟩) rfl
    have h2 : C y = T ⟨(y : H), hC.1 y.2⟩ := hC.2 (x := y) (y := ⟨(y : H), hC.1 y.2⟩) rfl
    rw [h1, h2]
    congr 1
    exact Subtype.ext hxy
  have hCB : C ≤ B := by
    refine ⟨hdom.ge, fun x y hxy => ?_⟩
    have h1 : C x = T ⟨(x : H), hC.1 x.2⟩ := hC.2 (x := x) (y := ⟨(x : H), hC.1 x.2⟩) rfl
    have h2 : B y = T ⟨(y : H), hB.1 y.2⟩ := hB.2 (x := y) (y := ⟨(y : H), hB.1 y.2⟩) rfl
    rw [h1, h2]
    congr 1
    exact Subtype.ext hxy
  exact le_antisymm hBC hCB

/-- The partial von Neumann extension is a restriction of the adjoint. -/
theorem vonNeumannExtensionOn_le_adjoint (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) {F : Submodule ℂ H}
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    vonNeumannExtensionOn A hsym hdense hF V ≤ A.adjoint := by
  refine ⟨vonNeumannDomainOn_le_adjoint_domain A hsym hdense hF V, fun x y hxy => ?_⟩
  rw [vonNeumannExtensionOn_apply]
  congr 1
  exact Subtype.ext hxy

/-! ### The kernel of the correspondence: `D(B) ∩ N₋(A) = 0` -/

/-- For a symmetric extension `B ≥ A`, no nonzero vector of `N₋(A)` lies in `D(B)`: on such a
vector `B` acts as `-i`, and the boundary form of `B` against itself gives `2i‖ξ‖² = 0`. -/
theorem eq_zero_of_mem_domain_of_mem_deficiencySubspaceMinus {A B : H →ₗ.[ℂ] H}
    (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B)
    {ξ : H} (hξB : ξ ∈ B.domain) (hξN : ξ ∈ deficiencySubspaceMinus A) : ξ = 0 := by
  have hBadj : B ≤ A.adjoint := le_adjoint_of_le_of_isFormalAdjoint hdense hAB hsymB
  have hmem : ξ ∈ A.adjoint.domain := hBadj.1 hξB
  have hBval : B ⟨ξ, hξB⟩ = A.adjoint ⟨ξ, hmem⟩ :=
    hBadj.2 (x := ⟨ξ, hξB⟩) (y := ⟨ξ, hmem⟩) rfl
  have hAval : A.adjoint ⟨ξ, hmem⟩ = (-I) • ξ :=
    adjoint_apply_of_mem_deficiencySubspaceMinus A hξN hmem
  have hs := hsymB ⟨ξ, hξB⟩ ⟨ξ, hξB⟩
  rw [hBval, hAval, inner_smul_left, inner_smul_right, map_neg, Complex.conj_I, neg_neg] at hs
  -- hs : I * ⟪ξ, ξ⟫ = -I * ⟪ξ, ξ⟫
  have h2 : (2 * I) * ⟪ξ, ξ⟫_ℂ = 0 := by linear_combination hs
  have hc : ⟪ξ, ξ⟫_ℂ = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    · exact h
  exact inner_self_eq_zero.mp hc

/-- **Uniqueness of the defect partner**: if `η + ξ` and `η + ξ'` both lie in `D(B)` with
`ξ, ξ' ∈ N₋(A)`, then `ξ = ξ'`. -/
theorem defect_partner_unique {A B : H →ₗ.[ℂ] H}
    (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B)
    {η ξ ξ' : H} (hξN : ξ ∈ deficiencySubspaceMinus A) (hξB : η + ξ ∈ B.domain)
    (hξ'N : ξ' ∈ deficiencySubspaceMinus A) (hξ'B : η + ξ' ∈ B.domain) : ξ = ξ' := by
  have hd : ξ - ξ' ∈ B.domain := by
    have h := B.domain.sub_mem hξB hξ'B
    have heq : η + ξ - (η + ξ') = ξ - ξ' := by abel
    rwa [heq] at h
  have hdN : ξ - ξ' ∈ deficiencySubspaceMinus A :=
    (deficiencySubspaceMinus A).sub_mem hξN hξ'N
  exact sub_eq_zero.mp
    (eq_zero_of_mem_domain_of_mem_deficiencySubspaceMinus hdense hAB hsymB hd hdN)

/-! ### The induced defect domain `F` -/

variable (A B : H →ₗ.[ℂ] H)

/-- The **induced defect domain** `F ≤ N₊(A)` of an extension `B`: all `η ∈ N₊(A)` admitting a
partner `ξ ∈ N₋(A)` with `η + ξ ∈ D(B)`. -/
def inducedDefectDomain : Submodule ℂ H where
  carrier := {η : H | η ∈ deficiencySubspacePlus A ∧
    ∃ ξ ∈ deficiencySubspaceMinus A, η + ξ ∈ B.domain}
  add_mem' := by
    rintro a b ⟨haN, ξa, hξaN, haB⟩ ⟨hbN, ξb, hξbN, hbB⟩
    refine ⟨(deficiencySubspacePlus A).add_mem haN hbN, ξa + ξb,
      (deficiencySubspaceMinus A).add_mem hξaN hξbN, ?_⟩
    have h := B.domain.add_mem haB hbB
    have heq : a + ξa + (b + ξb) = a + b + (ξa + ξb) := by abel
    rwa [heq] at h
  zero_mem' := ⟨(deficiencySubspacePlus A).zero_mem, 0,
    (deficiencySubspaceMinus A).zero_mem, by simp⟩
  smul_mem' := by
    rintro c a ⟨haN, ξa, hξaN, haB⟩
    refine ⟨(deficiencySubspacePlus A).smul_mem c haN, c • ξa,
      (deficiencySubspaceMinus A).smul_mem c hξaN, ?_⟩
    have h := B.domain.smul_mem c haB
    have heq : c • (a + ξa) = c • a + c • ξa := smul_add c a ξa
    rwa [heq] at h

/-- Membership in the induced defect domain, unfolded. -/
theorem mem_inducedDefectDomain {η : H} :
    η ∈ inducedDefectDomain A B ↔ η ∈ deficiencySubspacePlus A ∧
      ∃ ξ ∈ deficiencySubspaceMinus A, η + ξ ∈ B.domain :=
  Iff.rfl

/-- The induced defect domain sits inside `N₊(A)`. -/
theorem inducedDefectDomain_le : inducedDefectDomain A B ≤ deficiencySubspacePlus A :=
  fun _ hη => hη.1

/-! ### The induced partner and partial isometry `V` -/

/-- The **defect partner**: for `η` in the induced defect domain, a choice of `ξ ∈ N₋(A)` with
`η + ξ ∈ D(B)` (unique when `B` is a symmetric extension, by `defect_partner_unique`). -/
noncomputable def inducedPartner (η : inducedDefectDomain A B) : H :=
  ((mem_inducedDefectDomain A B).mp η.2).2.choose

theorem inducedPartner_mem_minus (η : inducedDefectDomain A B) :
    inducedPartner A B η ∈ deficiencySubspaceMinus A :=
  ((mem_inducedDefectDomain A B).mp η.2).2.choose_spec.1

theorem add_inducedPartner_mem (η : inducedDefectDomain A B) :
    (η : H) + inducedPartner A B η ∈ B.domain :=
  ((mem_inducedDefectDomain A B).mp η.2).2.choose_spec.2

variable {A B}

/-- Anything satisfying the partner property is *the* partner. -/
theorem inducedPartner_eq (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B)
    (hsymB : B.IsFormalAdjoint B) (η : inducedDefectDomain A B) {ξ : H}
    (hξN : ξ ∈ deficiencySubspaceMinus A) (hξB : (η : H) + ξ ∈ B.domain) :
    inducedPartner A B η = ξ :=
  defect_partner_unique hdense hAB hsymB (inducedPartner_mem_minus A B η)
    (add_inducedPartner_mem A B η) hξN hξB

/-- The defect partner is linear (by uniqueness), bundled. -/
noncomputable def inducedPartnerₗ (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B)
    (hsymB : B.IsFormalAdjoint B) : inducedDefectDomain A B →ₗ[ℂ] H where
  toFun := inducedPartner A B
  map_add' η η' := by
    refine inducedPartner_eq hdense hAB hsymB (η + η')
      ((deficiencySubspaceMinus A).add_mem (inducedPartner_mem_minus A B η)
        (inducedPartner_mem_minus A B η')) ?_
    have h := B.domain.add_mem (add_inducedPartner_mem A B η) (add_inducedPartner_mem A B η')
    have heq : (η : H) + inducedPartner A B η + ((η' : H) + inducedPartner A B η')
        = ((η + η' : inducedDefectDomain A B) : H)
          + (inducedPartner A B η + inducedPartner A B η') := by
      rw [Submodule.coe_add]
      abel
    rwa [heq] at h
  map_smul' c η := by
    simp only [RingHom.id_apply]
    refine inducedPartner_eq hdense hAB hsymB (c • η)
      ((deficiencySubspaceMinus A).smul_mem c (inducedPartner_mem_minus A B η)) ?_
    have h := B.domain.smul_mem c (add_inducedPartner_mem A B η)
    have heq : c • ((η : H) + inducedPartner A B η)
        = ((c • η : inducedDefectDomain A B) : H) + c • inducedPartner A B η := by
      rw [Submodule.coe_smul, smul_add]
    rwa [heq] at h

@[simp]
theorem inducedPartnerₗ_apply (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B)
    (hsymB : B.IsFormalAdjoint B) (η : inducedDefectDomain A B) :
    inducedPartnerₗ hdense hAB hsymB η = inducedPartner A B η :=
  rfl

/-- **The partner preserves inner products**: `⟪ξ(η), ξ(η')⟫ = ⟪η, η'⟫`, by the defect-only
boundary form of the symmetric `B`. -/
theorem inner_inducedPartner (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B)
    (η η' : inducedDefectDomain A B) :
    ⟪inducedPartner A B η, inducedPartner A B η'⟫_ℂ = ⟪(η : H), (η' : H)⟫_ℂ := by
  have hBadj : B ≤ A.adjoint := le_adjoint_of_le_of_isFormalAdjoint hdense hAB hsymB
  set u : H := (η : H) + inducedPartner A B η with _hu_def
  set w : H := (η' : H) + inducedPartner A B η' with _hw_def
  have huB : u ∈ B.domain := add_inducedPartner_mem A B η
  have hwB : w ∈ B.domain := add_inducedPartner_mem A B η'
  have huadj : u ∈ A.adjoint.domain := hBadj.1 huB
  have hwadj : w ∈ A.adjoint.domain := hBadj.1 hwB
  -- boundary form of `A*` on the defect decompositions
  have hbf := adjoint_boundaryForm_defect A hsym hdense
    ⟨(η : H), inducedDefectDomain_le A B η.2⟩ ⟨(η' : H), inducedDefectDomain_le A B η'.2⟩
    ⟨inducedPartner A B η, inducedPartner_mem_minus A B η⟩
    ⟨inducedPartner A B η', inducedPartner_mem_minus A B η'⟩
    huadj hwadj rfl rfl
  -- symmetry of `B` kills the left side
  have hBu : B ⟨u, huB⟩ = A.adjoint ⟨u, huadj⟩ :=
    hBadj.2 (x := ⟨u, huB⟩) (y := ⟨u, huadj⟩) rfl
  have hBw : B ⟨w, hwB⟩ = A.adjoint ⟨w, hwadj⟩ :=
    hBadj.2 (x := ⟨w, hwB⟩) (y := ⟨w, hwadj⟩) rfl
  have hs := hsymB ⟨u, huB⟩ ⟨w, hwB⟩
  rw [hBu, hBw] at hs
  rw [sub_eq_zero.mpr hs] at hbf
  -- 0 = -2i(⟪η,η'⟫ - ⟪ξ,ξ'⟫) forces the inner products to agree
  have hfac : ⟪(η : H), (η' : H)⟫_ℂ - ⟪inducedPartner A B η, inducedPartner A B η'⟫_ℂ = 0 := by
    rcases mul_eq_zero.mp hbf.symm with h | h
    · exact absurd h (by
        intro h0
        have : (2 : ℂ) * I = 0 := by linear_combination -h0
        exact mul_ne_zero two_ne_zero Complex.I_ne_zero this)
    · exact h
  have := sub_eq_zero.mp hfac
  exact this.symm

/-- The **induced partial isometry** `V : F →ₗᵢ[ℂ] N₋(A)`, `η ↦ -ξ(η)`, of a symmetric
extension `B ≥ A`. -/
noncomputable def inducedDefectIsometry (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B) :
    inducedDefectDomain A B →ₗᵢ[ℂ] deficiencySubspaceMinus A :=
  LinearMap.isometryOfInner
    (LinearMap.codRestrict (deficiencySubspaceMinus A) (-(inducedPartnerₗ hdense hAB hsymB))
      fun η => by
        simpa using (deficiencySubspaceMinus A).neg_mem (inducedPartner_mem_minus A B η))
    (fun η η' => by
      rw [Submodule.coe_inner, LinearMap.codRestrict_apply, LinearMap.codRestrict_apply,
        LinearMap.neg_apply, LinearMap.neg_apply, inducedPartnerₗ_apply, inducedPartnerₗ_apply,
        inner_neg_neg, inner_inducedPartner hsym hdense hAB hsymB, Submodule.coe_inner])

/-- The induced isometry acts as minus the partner. -/
theorem inducedDefectIsometry_apply_coe (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B)
    (η : inducedDefectDomain A B) :
    ((inducedDefectIsometry hsym hdense hAB hsymB η : deficiencySubspaceMinus A) : H)
      = -(inducedPartner A B η) :=
  rfl

/-! ### The second von Neumann formula -/

/-- **Domain identity**: `D(B) = D(A) ⊔ {η - V_Bη | η ∈ F_B}` at the induced data, for closed
`A`. The forward inclusion decomposes `u ∈ D(B)` by the first von Neumann formula and
identifies the `N₋`-component with the partner of the `N₊`-component. -/
theorem domain_eq_vonNeumannDomainOn_induced (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B) :
    B.domain = vonNeumannDomainOn A (inducedDefectIsometry hsym hdense hAB hsymB) := by
  have hBadj : B ≤ A.adjoint := le_adjoint_of_le_of_isFormalAdjoint hdense hAB hsymB
  apply le_antisymm
  · intro u huB
    have huadj : u ∈ A.adjoint.domain := hBadj.1 huB
    obtain ⟨ψ, η, ξ, hdecomp⟩ := adjoint_domain_cases A hsym hdense hclosed huadj
    -- the defect part `η + ξ = u - ψ` lies in `D(B)`
    have hηξB : (η : H) + (ξ : H) ∈ B.domain := by
      have h := B.domain.sub_mem huB (hAB.1 ψ.2)
      have heq : u - (ψ : H) = (η : H) + (ξ : H) := by rw [hdecomp]; abel
      rwa [heq] at h
    have hηF : (η : H) ∈ inducedDefectDomain A B := ⟨η.2, (ξ : H), ξ.2, hηξB⟩
    have hpart : inducedPartner A B ⟨(η : H), hηF⟩ = (ξ : H) :=
      inducedPartner_eq hdense hAB hsymB ⟨(η : H), hηF⟩ ξ.2 hηξB
    have hmem := mem_vonNeumannDomainOn A (inducedDefectIsometry hsym hdense hAB hsymB)
      ψ ⟨(η : H), hηF⟩
    rw [inducedDefectIsometry_apply_coe, hpart] at hmem
    have heq : (ψ : H) + (η : H) - -(ξ : H) = u := by rw [hdecomp]; abel
    rwa [heq] at hmem
  · refine sup_le hAB.1 ?_
    rintro u ⟨η, rfl⟩
    rw [vonNeumannDefectMapOn_apply, inducedDefectIsometry_apply_coe, sub_neg_eq_add]
    exact add_inducedPartner_mem A B η

/-- **`B` is the partial von Neumann extension at its induced data** (closed `A`): both are
restrictions of `A*` with the same domain. -/
theorem eq_vonNeumannExtensionOn_induced (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B) :
    B = vonNeumannExtensionOn A hsym hdense (inducedDefectDomain_le A B)
      (inducedDefectIsometry hsym hdense hAB hsymB) :=
  eq_of_le_of_le_of_domain_eq
    (le_adjoint_of_le_of_isFormalAdjoint hdense hAB hsymB)
    (vonNeumannExtensionOn_le_adjoint A hsym hdense _ _)
    (domain_eq_vonNeumannDomainOn_induced hsym hdense hclosed hAB hsymB)

/-- **The second von Neumann formula.** Every symmetric extension `B` of a closed, symmetric,
densely-defined `A` is a partial von Neumann extension: there are `F ≤ N₊(A)` and an isometry
`V : F →ₗᵢ[ℂ] N₋(A)` with `B = A*|_{D(A) ⊔ (1-V)F}`. Together with
`vonNeumannExtensionOn_isFormalAdjoint` (every such restriction *is* a symmetric extension)
this classifies the symmetric extensions of `A`. -/
theorem exists_eq_vonNeumannExtensionOn (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hAB : A ≤ B) (hsymB : B.IsFormalAdjoint B) :
    ∃ (F : Submodule ℂ H) (hF : F ≤ deficiencySubspacePlus A)
      (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A),
        B = vonNeumannExtensionOn A hsym hdense hF V :=
  ⟨inducedDefectDomain A B, inducedDefectDomain_le A B,
    inducedDefectIsometry hsym hdense hAB hsymB,
    eq_vonNeumannExtensionOn_induced hsym hdense hclosed hAB hsymB⟩

/-! ### Recovery: the correspondence is injective -/

variable {F : Submodule ℂ H}

/-- **Recovery of `F`**: the induced defect domain of `A_V` is exactly `V`'s domain `F`, for
closed `A`. The forward inclusion pins both decompositions of a defect vector against the
uniqueness half of the first von Neumann formula. -/
theorem inducedDefectDomain_vonNeumannExtensionOn (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    (hF : F ≤ deficiencySubspacePlus A) (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) :
    inducedDefectDomain A (vonNeumannExtensionOn A hsym hdense hF V) = F := by
  apply le_antisymm
  · rintro η' ⟨hη'N, ξ, hξN, hmem⟩
    rw [vonNeumannExtensionOn_domain] at hmem
    obtain ⟨x, η, hcases⟩ := vonNeumannDomainOn_cases A hmem
    -- two first-formula decompositions of `η' + ξ` must agree componentwise
    have huadj : η' + ξ ∈ A.adjoint.domain := A.adjoint.domain.add_mem
      (mem_adjoint_domain_of_mem_deficiencySubspacePlus A hη'N)
      (mem_adjoint_domain_of_mem_deficiencySubspaceMinus A hξN)
    have huniq := existsUnique_deficiency_decomposition A hsym hdense hclosed huadj
    have h1 : η' + ξ = ((0 : A.domain) : H) + ((⟨η', hη'N⟩ :
        deficiencySubspacePlus A) : H) + ((⟨ξ, hξN⟩ : deficiencySubspaceMinus A) : H) := by
      change η' + ξ = 0 + η' + ξ
      rw [zero_add]
    have h2 : η' + ξ = ((x : H)) + ((⟨(η : H), hF η.2⟩ : deficiencySubspacePlus A) : H)
        + ((-(V η) : deficiencySubspaceMinus A) : H) := by
      calc η' + ξ = (x : H) + (η : H) - ((V η : deficiencySubspaceMinus A) : H) := hcases
        _ = ((x : H)) + ((⟨(η : H), hF η.2⟩ : deficiencySubspacePlus A) : H)
            + ((-(V η) : deficiencySubspaceMinus A) : H) := by
          rw [Submodule.coe_neg, sub_eq_add_neg]
    have hcomp := huniq.unique
      (y₁ := ⟨0, ⟨η', hη'N⟩, ⟨ξ, hξN⟩⟩) (y₂ := ⟨x, ⟨(η : H), hF η.2⟩, -(V η)⟩) h1 h2
    have hplus : (⟨η', hη'N⟩ : deficiencySubspacePlus A)
        = ⟨(η : H), hF η.2⟩ := congrArg (fun p => p.2.1) hcomp
    have : η' = (η : H) := Subtype.ext_iff.mp hplus
    rw [this]
    exact η.2
  · intro η hη
    refine ⟨hF hη, -((V ⟨η, hη⟩ : deficiencySubspaceMinus A) : H),
      (deficiencySubspaceMinus A).neg_mem (V ⟨η, hη⟩).2, ?_⟩
    rw [vonNeumannExtensionOn_domain]
    have hmem := mem_vonNeumannDomainOn A V 0 ⟨η, hη⟩
    simpa [sub_eq_add_neg] using hmem

/-- **Recovery of `V`** (pointwise): if two partial von Neumann extensions of a closed `A`
coincide, their isometries agree wherever both are defined. With
`inducedDefectDomain_vonNeumannExtensionOn` (which recovers `F` from the operator), this makes
the correspondence `(F, V) ↦ A_V` injective. -/
theorem vonNeumannExtensionOn_inj_apply (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) {F' : Submodule ℂ H}
    (hF : F ≤ deficiencySubspacePlus A) (hF' : F' ≤ deficiencySubspacePlus A)
    (V : F →ₗᵢ[ℂ] deficiencySubspaceMinus A) (V' : F' →ₗᵢ[ℂ] deficiencySubspaceMinus A)
    (heq : vonNeumannExtensionOn A hsym hdense hF V = vonNeumannExtensionOn A hsym hdense hF' V')
    {η : H} (hη : η ∈ F) (hη' : η ∈ F') :
    ((V ⟨η, hη⟩ : deficiencySubspaceMinus A) : H)
      = ((V' ⟨η, hη'⟩ : deficiencySubspaceMinus A) : H) := by
  have hdom : vonNeumannDomainOn A V = vonNeumannDomainOn A V' := by
    have := congrArg LinearPMap.domain heq
    rwa [vonNeumannExtensionOn_domain, vonNeumannExtensionOn_domain] at this
  -- both `η - Vη` and `η - V'η` lie in the common domain, with partners `-Vη`, `-V'η`
  have hsymExt := vonNeumannExtensionOn_isFormalAdjoint A hsym hdense hF V
  have hle := le_vonNeumannExtensionOn A hsym hdense hF V
  have hmemV : η + -((V ⟨η, hη⟩ : deficiencySubspaceMinus A) : H)
      ∈ (vonNeumannExtensionOn A hsym hdense hF V).domain := by
    rw [vonNeumannExtensionOn_domain]
    have hmem := mem_vonNeumannDomainOn A V 0 ⟨η, hη⟩
    simpa [sub_eq_add_neg] using hmem
  have hmemV' : η + -((V' ⟨η, hη'⟩ : deficiencySubspaceMinus A) : H)
      ∈ (vonNeumannExtensionOn A hsym hdense hF V).domain := by
    rw [vonNeumannExtensionOn_domain, hdom]
    have hmem := mem_vonNeumannDomainOn A V' 0 ⟨η, hη'⟩
    simpa [sub_eq_add_neg] using hmem
  have huniq := defect_partner_unique hdense hle hsymExt
    ((deficiencySubspaceMinus A).neg_mem (V ⟨η, hη⟩).2) hmemV
    ((deficiencySubspaceMinus A).neg_mem (V' ⟨η, hη'⟩).2) hmemV'
  exact neg_injective huniq

end Spectra.Operator

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Range.Surjectivity

/-!
# Deficiency subspaces

For a densely-defined operator `A : H →ₗ.[ℂ] H`, the **deficiency subspaces**
`N₊(A) = ker(A* - i)` and `N₋(A) = ker(A* + i)` measure the failure of `A` to be (essentially)
self-adjoint: by von Neumann's theory (Reed–Simon, Section VIII.3), a symmetric closed operator
is self-adjoint iff both deficiency subspaces are trivial, and its deficiency *indices*
`(dim N₊, dim N₋)` classify all self-adjoint extensions when they agree.

This file establishes the basic algebraic theory of the deficiency subspaces for a general
densely-defined `A` (no symmetry assumed) and proves the fundamental orthogonality
identification

  `N₊(A) = ran(A + i)ᗮ`   and   `N₋(A) = ran(A - i)ᗮ`.

Both inclusions turn out to depend only on `Dense (A.domain : Set H)`, not on `A` being
symmetric: the forward inclusion is a direct computation from the defining property of the
adjoint (`LinearPMap.adjoint_isFormalAdjoint`), and the reverse inclusion is the same
continuity-then-adjoint-domain-membership argument used in
`Spectra.YosidaHille.op_range_dense` to place an orthogonal vector into `A.adjoint.domain`.
Consequently no `A.IsFormalAdjoint A` hypothesis appears anywhere in this file.

## Main definitions

* `deficiencySubspacePlus A` — `N₊(A) = ker(A* - i) = {χ ∈ D(A*) | A*χ = iχ}`.
* `deficiencySubspaceMinus A` — `N₋(A) = ker(A* + i) = {χ ∈ D(A*) | A*χ = -iχ}`.

## Main statements

* `deficiencySubspacePlus_eq_orthogonal` — `N₊(A) = (ran(A + i))ᗮ`.
* `deficiencySubspaceMinus_eq_orthogonal` — `N₋(A) = (ran(A - i))ᗮ`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **`+i` deficiency subspace** `N₊(A) = ker(A* - i)`: vectors `χ` in the adjoint domain
with `A*χ = iχ`. -/
def deficiencySubspacePlus (A : H →ₗ.[ℂ] H) : Submodule ℂ H where
  carrier := {χ : H | ∃ h : χ ∈ A.adjoint.domain, A.adjoint ⟨χ, h⟩ = I • χ}
  zero_mem' := ⟨A.adjoint.domain.zero_mem, by
    have h := A.adjoint.map_zero
    simp only [smul_zero]
    convert h using 2⟩
  add_mem' := by
    rintro a b ⟨ha, hAa⟩ ⟨hb, hAb⟩
    refine ⟨A.adjoint.domain.add_mem ha hb, ?_⟩
    have hop : A.adjoint ⟨a + b, A.adjoint.domain.add_mem ha hb⟩
        = A.adjoint ⟨a, ha⟩ + A.adjoint ⟨b, hb⟩ := by
      have := A.adjoint.map_add ⟨a, ha⟩ ⟨b, hb⟩
      convert this using 2
    rw [hop, hAa, hAb, smul_add]
  smul_mem' := by
    rintro c a ⟨ha, hAa⟩
    refine ⟨A.adjoint.domain.smul_mem c ha, ?_⟩
    have hop : A.adjoint ⟨c • a, A.adjoint.domain.smul_mem c ha⟩ = c • A.adjoint ⟨a, ha⟩ := by
      have := A.adjoint.map_smul c ⟨a, ha⟩
      convert this using 2
    rw [hop, hAa, smul_comm]

/-- The **`-i` deficiency subspace** `N₋(A) = ker(A* + i)`: vectors `χ` in the adjoint domain
with `A*χ = -iχ`. -/
def deficiencySubspaceMinus (A : H →ₗ.[ℂ] H) : Submodule ℂ H where
  carrier := {χ : H | ∃ h : χ ∈ A.adjoint.domain, A.adjoint ⟨χ, h⟩ = (-I) • χ}
  zero_mem' := ⟨A.adjoint.domain.zero_mem, by
    have h := A.adjoint.map_zero
    simp only [smul_zero]
    convert h using 2⟩
  add_mem' := by
    rintro a b ⟨ha, hAa⟩ ⟨hb, hAb⟩
    refine ⟨A.adjoint.domain.add_mem ha hb, ?_⟩
    have hop : A.adjoint ⟨a + b, A.adjoint.domain.add_mem ha hb⟩
        = A.adjoint ⟨a, ha⟩ + A.adjoint ⟨b, hb⟩ := by
      have := A.adjoint.map_add ⟨a, ha⟩ ⟨b, hb⟩
      convert this using 2
    rw [hop, hAa, hAb, smul_add]
  smul_mem' := by
    rintro c a ⟨ha, hAa⟩
    refine ⟨A.adjoint.domain.smul_mem c ha, ?_⟩
    have hop : A.adjoint ⟨c • a, A.adjoint.domain.smul_mem c ha⟩ = c • A.adjoint ⟨a, ha⟩ := by
      have := A.adjoint.map_smul c ⟨a, ha⟩
      convert this using 2
    rw [hop, hAa, smul_comm]

/-- **Direction 1 (algebraic).** `N₊(A) ⊆ ran(A + i)ᗮ`: if `A*χ = iχ` then `χ` is orthogonal to
`Aψ + iψ` for every `ψ ∈ D(A)`, by the defining property of the adjoint together with
`conj I = -I`. No symmetry hypothesis on `A` is needed. -/
theorem deficiencySubspacePlus_le_orthogonal (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) :
    deficiencySubspacePlus A ≤ (Spectra.Resolvent.rangeSubmodule (A := A) (-I))ᗮ := by
  rintro χ ⟨hχ, hAχ⟩
  rw [Submodule.mem_orthogonal]
  rintro y ⟨ψ, rfl⟩
  have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨χ, hχ⟩ ψ
  -- hfa : ⟪A.adjoint ⟨χ, hχ⟩, ↑ψ⟫ = ⟪χ, A ψ⟫
  have h1 : ⟪χ, A ψ⟫_ℂ = (-I) * ⟪χ, (ψ : H)⟫_ℂ := by
    rw [← hfa, hAχ, inner_smul_left]; simp
  have hstep : ⟪A ψ, χ⟫_ℂ = I * ⟪(ψ : H), χ⟫_ℂ := by
    have h2 := congrArg (starRingEnd ℂ) h1
    rw [inner_conj_symm, map_mul, inner_conj_symm] at h2
    rw [h2]; simp
  have hgoal : ⟪A ψ - (-I) • (ψ : H), χ⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_smul_left, hstep]; simp
  simpa using hgoal

/-- **Direction 2 (analytic).** `ran(A + i)ᗮ ⊆ N₊(A)`: an orthogonal vector `χ` is placed in
`A.adjoint.domain` via continuity of `ψ ↦ ⟪χ, Aψ⟫` on the dense set `D(A)`
(`LinearPMap.mem_adjoint_domain_iff`), and the adjoint relation is pinned down by continuity of
the functional `w ↦ ⟪A.adjoint χ - iχ, w⟫` vanishing on a dense set. Only `Dense (A.domain : Set
H)` is needed — this is fundamentally a statement about `A`'s own adjoint, not about `A` being
symmetric. -/
theorem orthogonal_le_deficiencySubspacePlus (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) :
    (Spectra.Resolvent.rangeSubmodule (A := A) (-I))ᗮ ≤ deficiencySubspacePlus A := by
  intro χ hχ
  rw [Submodule.mem_orthogonal] at hχ
  have horth : ∀ ψ : A.domain, ⟪A ψ - (-I) • (ψ : H), χ⟫_ℂ = 0 :=
    fun ψ => hχ _ ⟨ψ, rfl⟩
  -- from orthogonality: ⟪χ, Aψ⟫ = -I * ⟪χ, ψ⟫ for every ψ ∈ D(A)
  have hval : ∀ ψ : A.domain, ⟪χ, A ψ⟫_ℂ = (-I) * ⟪χ, (ψ : H)⟫_ℂ := by
    intro ψ
    have h0 := horth ψ
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
    have hc := congrArg (starRingEnd ℂ) h0
    rw [inner_conj_symm, map_mul, inner_conj_symm] at hc
    simpa using hc
  -- χ lies in the adjoint domain: ψ ↦ ⟪χ, Aψ⟫ is continuous
  have hcont : Continuous fun ψ : A.domain => ⟪χ, A ψ⟫_ℂ := by
    have hfun : (fun ψ : A.domain => ⟪χ, A ψ⟫_ℂ)
        = fun ψ : A.domain => (-I) * ⟪χ, (ψ : H)⟫_ℂ := funext hval
    rw [hfun]
    exact continuous_const.mul (continuous_const.inner A.domain.subtypeL.continuous)
  have hχdom : χ ∈ A.adjoint.domain := (LinearPMap.mem_adjoint_domain_iff A χ).mpr hcont
  refine ⟨hχdom, ?_⟩
  -- pin down the value of the adjoint via orthogonality to a dense set
  have hkey : ∀ ψ : A.domain, ⟪A.adjoint ⟨χ, hχdom⟩ - I • χ, (ψ : H)⟫_ℂ = 0 := by
    intro ψ
    have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨χ, hχdom⟩ ψ
    rw [inner_sub_left, hfa, hval ψ, inner_smul_left]
    simp
  set d := A.adjoint ⟨χ, hχdom⟩ - I • χ with hd
  have hd0 : d = 0 := by
    have hg : Continuous fun w => ⟪d, w⟫_ℂ := continuous_const.inner continuous_id
    have hg0 : (fun w => ⟪d, w⟫_ℂ) = fun _ => (0 : ℂ) :=
      Continuous.ext_on hdense hg continuous_const fun w hw => by
        simpa using hkey ⟨w, hw⟩
    have : ⟪d, d⟫_ℂ = 0 := by have := congrFun hg0 d; simpa using this
    exact inner_self_eq_zero.mp this
  rwa [hd, sub_eq_zero] at hd0

/-- **The `+i` deficiency subspace equals the orthogonal complement of `ran(A + i)`.**
`N₊(A) = ker(A* - i) = ran(A + i)ᗮ`. -/
theorem deficiencySubspacePlus_eq_orthogonal (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) :
    deficiencySubspacePlus A = (Spectra.Resolvent.rangeSubmodule (A := A) (-I))ᗮ :=
  le_antisymm (deficiencySubspacePlus_le_orthogonal A hdense)
    (orthogonal_le_deficiencySubspacePlus A hdense)

/-- **Direction 1 (algebraic), `-i` case.** `N₋(A) ⊆ ran(A - i)ᗮ`. -/
theorem deficiencySubspaceMinus_le_orthogonal (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) :
    deficiencySubspaceMinus A ≤ (Spectra.Resolvent.rangeSubmodule (A := A) I)ᗮ := by
  rintro χ ⟨hχ, hAχ⟩
  rw [Submodule.mem_orthogonal]
  rintro y ⟨ψ, rfl⟩
  have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨χ, hχ⟩ ψ
  have h1 : ⟪χ, A ψ⟫_ℂ = I * ⟪χ, (ψ : H)⟫_ℂ := by
    rw [← hfa, hAχ, inner_smul_left]; simp
  have hstep : ⟪A ψ, χ⟫_ℂ = (-I) * ⟪(ψ : H), χ⟫_ℂ := by
    have h2 := congrArg (starRingEnd ℂ) h1
    rw [inner_conj_symm, map_mul, inner_conj_symm] at h2
    rw [h2]; simp
  have hgoal : ⟪A ψ - I • (ψ : H), χ⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_smul_left, hstep]; simp
  simpa using hgoal

/-- **Direction 2 (analytic), `-i` case.** `ran(A - i)ᗮ ⊆ N₋(A)`. -/
theorem orthogonal_le_deficiencySubspaceMinus (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) :
    (Spectra.Resolvent.rangeSubmodule (A := A) I)ᗮ ≤ deficiencySubspaceMinus A := by
  intro χ hχ
  rw [Submodule.mem_orthogonal] at hχ
  have horth : ∀ ψ : A.domain, ⟪A ψ - I • (ψ : H), χ⟫_ℂ = 0 :=
    fun ψ => hχ _ ⟨ψ, rfl⟩
  -- from orthogonality: ⟪χ, Aψ⟫ = I * ⟪χ, ψ⟫ for every ψ ∈ D(A)
  have hval : ∀ ψ : A.domain, ⟪χ, A ψ⟫_ℂ = I * ⟪χ, (ψ : H)⟫_ℂ := by
    intro ψ
    have h0 := horth ψ
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
    have hc := congrArg (starRingEnd ℂ) h0
    rw [inner_conj_symm, map_mul, inner_conj_symm] at hc
    simpa using hc
  have hcont : Continuous fun ψ : A.domain => ⟪χ, A ψ⟫_ℂ := by
    have hfun : (fun ψ : A.domain => ⟪χ, A ψ⟫_ℂ)
        = fun ψ : A.domain => I * ⟪χ, (ψ : H)⟫_ℂ := funext hval
    rw [hfun]
    exact continuous_const.mul (continuous_const.inner A.domain.subtypeL.continuous)
  have hχdom : χ ∈ A.adjoint.domain := (LinearPMap.mem_adjoint_domain_iff A χ).mpr hcont
  refine ⟨hχdom, ?_⟩
  have hkey : ∀ ψ : A.domain, ⟪A.adjoint ⟨χ, hχdom⟩ - (-I) • χ, (ψ : H)⟫_ℂ = 0 := by
    intro ψ
    have hfa := LinearPMap.adjoint_isFormalAdjoint hdense ⟨χ, hχdom⟩ ψ
    rw [inner_sub_left, hfa, hval ψ, inner_smul_left]
    simp
  set d := A.adjoint ⟨χ, hχdom⟩ - (-I) • χ with hd
  have hd0 : d = 0 := by
    have hg : Continuous fun w => ⟪d, w⟫_ℂ := continuous_const.inner continuous_id
    have hg0 : (fun w => ⟪d, w⟫_ℂ) = fun _ => (0 : ℂ) :=
      Continuous.ext_on hdense hg continuous_const fun w hw => by
        simpa using hkey ⟨w, hw⟩
    have : ⟪d, d⟫_ℂ = 0 := by have := congrFun hg0 d; simpa using this
    exact inner_self_eq_zero.mp this
  rwa [hd, sub_eq_zero] at hd0

/-- **The `-i` deficiency subspace equals the orthogonal complement of `ran(A - i)`.**
`N₋(A) = ker(A* + i) = ran(A - i)ᗮ`. -/
theorem deficiencySubspaceMinus_eq_orthogonal (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) :
    deficiencySubspaceMinus A = (Spectra.Resolvent.rangeSubmodule (A := A) I)ᗮ :=
  le_antisymm (deficiencySubspaceMinus_le_orthogonal A hdense)
    (orthogonal_le_deficiencySubspaceMinus A hdense)

end Spectra.Operator

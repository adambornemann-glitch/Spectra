/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.VonNeumannExtensionSelfAdjoint
import Spectra.Operator.UniqueSelfAdjointExtension

/-!
# The first von Neumann formula

For a closed, symmetric, densely-defined `A : H →ₗ.[ℂ] H`, the domain of the adjoint splits as

  `D(A*) = D(A) ⊕_g N₊(A) ⊕_g N₋(A)`,

where `N±(A)` are the deficiency subspaces (`Spectra.Operator.deficiencySubspacePlus`/`..Minus`)
and `⊕_g` means the sum is direct and orthogonal for the **graph inner product** of `A*`,
`⟪u, v⟫_* := ⟪u, v⟫ + ⟪A*u, A*v⟫`. This file proves each layer of that statement separately:

* **Existence** (`adjoint_domain_cases`): every `u ∈ D(A*)` is `ψ + η + ξ` with `ψ ∈ D(A)`,
  `η ∈ N₊(A)`, `ξ ∈ N₋(A)` — split `A*u + iu` over `H = ran(A + i) ⊕ ran(A + i)ᗮ` (the range is
  closed by `Spectra.YosidaHille.op_range_isClosed`, its complement is `N₊(A)` by
  `orthogonal_le_deficiencySubspacePlus`), pull the `N₊` part back through `(A* + i)|_{N₊} = 2i`,
  and check the remainder is killed by `A* + i`. As a submodule identity:
  `vonNeumannFormula : D(A*) = D(A) ⊔ N₊(A) ⊔ N₋(A)`.
* **Uniqueness** (`eq_zero_of_add_deficiency_eq_zero`, no closedness needed): a vanishing sum
  has vanishing parts — apply the action formula at `u = 0` to get `(Aψ + iψ) + 2iη = 0`, whose
  summands lie in `ran(A + i)` and `ran(A + i)ᗮ` respectively, so both die; the lower bound
  `Spectra.YosidaHille.op_lower_bound` then kills `ψ`. Packaged with existence as
  `existsUnique_deficiency_decomposition` (`∃!`).
* **Graph orthogonality** (`graphInner_domain_deficiencySubspacePlus`/`..Minus`,
  `graphInner_deficiencySubspaces`): the three summands are mutually orthogonal for `⟪·,·⟫_*`,
  stated with the adjoint's action written out (`A*ψ = Aψ`, `A*η = iη`, `A*ξ = -iξ`) — direct
  consequences of the cross-term identities from
  `Spectra.Operator.VonNeumannExtensionSelfAdjoint` and `i·i = -1`.
* **Action formula** (`adjoint_apply_add_deficiency`, no closedness needed):
  `A*(ψ + η + ξ) = Aψ + iη - iξ` — the generalization of
  `vonNeumannExtension_apply_add_defect` from `D(A_V)` to all of `D(A*)`.
* **General case** (`vonNeumannFormula_closure`): without closedness,
  `D(A*) = D(Ā) ⊔ N₊(A) ⊔ N₋(A)` — apply the closed case to `Ā` and transport along
  `A* = (Ā)*` (`closure_adjoint_eq_adjoint`) and `N±(Ā) = N±(A)`
  (`deficiencySubspacePlus_closure`/`..Minus..`, proved here); uniqueness transports too
  (`eq_zero_of_mem_closure_add_deficiency_eq_zero`).

This is the "first von Neumann formula" of extension theory: it exhibits `D(A*)` as `D(A)`
enlarged by exactly the two deficiency subspaces, and is the domain-side counterpart of the
extension construction `A_V` (`Spectra.Operator.VonNeumannExtension`, whose domain
`D(A) ⊔ (1 - V)N₊` selects the graph of `A_V` inside this decomposition). It is the standing
prerequisite for classifying the *symmetric* (not necessarily self-adjoint) extensions of `A`
by partial isometries `N₊ ⊇ dom V → N₋`.

## Main statements

* `deficiencySubspacePlus_closure` / `deficiencySubspaceMinus_closure` — `N±(Ā) = N±(A)`.
* `adjoint_domain_cases` — existence of the decomposition (closed case).
* `vonNeumannFormula` — **the first von Neumann formula**, closed case:
  `D(A*) = D(A) ⊔ N₊(A) ⊔ N₋(A)`.
* `adjoint_apply_add_deficiency` — the action formula `A*(ψ + η + ξ) = Aψ + iη - iξ`.
* `eq_zero_of_add_deficiency_eq_zero` — uniqueness (zero form), no closedness.
* `existsUnique_deficiency_decomposition` — existence + uniqueness as an `∃!` (closed case).
* `graphInner_domain_deficiencySubspacePlus` / `..Minus` / `graphInner_deficiencySubspaces` —
  mutual graph-orthogonality of the three summands.
* `vonNeumannFormula_closure` — the general case: `D(A*) = D(Ā) ⊔ N₊(A) ⊔ N₋(A)`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975], Section X.1.
* [Akhiezer, Glazman, *Theory of Linear Operators in Hilbert Space*][akhiezer1993].
-/

open Complex
open scoped InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The deficiency subspaces only see the closure -/

/-- `N₊(Ā) = N₊(A)`: the deficiency subspaces are defined through the adjoint, and the adjoint
only sees the closure (`closure_adjoint_eq_adjoint`). -/
theorem deficiencySubspacePlus_closure {A : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hclosable : A.IsClosable) :
    deficiencySubspacePlus A.closure = deficiencySubspacePlus A := by
  have h : A.closure.adjoint = A.adjoint := closure_adjoint_eq_adjoint hdense hclosable
  ext χ
  change (∃ hm : χ ∈ A.closure.adjoint.domain, A.closure.adjoint ⟨χ, hm⟩ = I • χ) ↔
      (∃ hm : χ ∈ A.adjoint.domain, A.adjoint ⟨χ, hm⟩ = I • χ)
  rw [h]

/-- `N₋(Ā) = N₋(A)`. -/
theorem deficiencySubspaceMinus_closure {A : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hclosable : A.IsClosable) :
    deficiencySubspaceMinus A.closure = deficiencySubspaceMinus A := by
  have h : A.closure.adjoint = A.adjoint := closure_adjoint_eq_adjoint hdense hclosable
  ext χ
  change (∃ hm : χ ∈ A.closure.adjoint.domain, A.closure.adjoint ⟨χ, hm⟩ = (-I) • χ) ↔
      (∃ hm : χ ∈ A.adjoint.domain, A.adjoint ⟨χ, hm⟩ = (-I) • χ)
  rw [h]

/-! ### Graph orthogonality

The graph inner product of `A*` is `⟪u, v⟫_* = ⟪u, v⟫ + ⟪A*u, A*v⟫`. On the three summands the
adjoint acts explicitly (`A*ψ = Aψ` on `D(A)`, `A*η = iη` on `N₊`, `A*ξ = -iξ` on `N₋`), so the
orthogonality relations below are stated with those actions written out. -/

/-- `D(A) ⊥_g N₊(A)`: `⟪ψ, η⟫ + ⟪A*ψ, A*η⟫ = 0`, with `A*ψ = Aψ` and `A*η = iη` written out. -/
theorem graphInner_domain_deficiencySubspacePlus (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) (x : A.domain) (η : deficiencySubspacePlus A) :
    ⟪(x : H), (η : H)⟫_ℂ + ⟪A x, I • (η : H)⟫_ℂ = 0 := by
  rw [inner_smul_right, inner_apply_deficiencySubspacePlus A hdense η x]
  linear_combination ⟪(x : H), (η : H)⟫_ℂ * Complex.I_mul_I

/-- `D(A) ⊥_g N₋(A)`: `⟪ψ, ξ⟫ + ⟪A*ψ, A*ξ⟫ = 0`, with `A*ψ = Aψ` and `A*ξ = -iξ` written
out. -/
theorem graphInner_domain_deficiencySubspaceMinus (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H)) (x : A.domain) (ξ : deficiencySubspaceMinus A) :
    ⟪(x : H), (ξ : H)⟫_ℂ + ⟪A x, (-I) • (ξ : H)⟫_ℂ = 0 := by
  rw [inner_smul_right, inner_apply_deficiencySubspaceMinus A hdense ξ x]
  linear_combination ⟪(x : H), (ξ : H)⟫_ℂ * Complex.I_mul_I

/-- `N₊(A) ⊥_g N₋(A)`: `⟪η, ξ⟫ + ⟪A*η, A*ξ⟫ = 0`, with `A*η = iη` and `A*ξ = -iξ` written
out. No density or symmetry hypothesis at all. -/
theorem graphInner_deficiencySubspaces (A : H →ₗ.[ℂ] H)
    (η : deficiencySubspacePlus A) (ξ : deficiencySubspaceMinus A) :
    ⟪(η : H), (ξ : H)⟫_ℂ + ⟪I • (η : H), (-I) • (ξ : H)⟫_ℂ = 0 := by
  rw [inner_smul_left, inner_smul_right, Complex.conj_I]
  linear_combination ⟪(η : H), (ξ : H)⟫_ℂ * Complex.I_mul_I

/-! ### Existence of the decomposition (closed case) -/

/-- **Existence half of the first von Neumann formula.** For closed, symmetric, densely-defined
`A`, every `u ∈ D(A*)` decomposes as `u = ψ + η + ξ` with `ψ ∈ D(A)`, `η ∈ N₊(A)`,
`ξ ∈ N₋(A)`: split `A*u + iu` over `H = ran(A + i) ⊕ ran(A + i)ᗮ`, recover the `N₊(A)` part as
`(A* + i)η` with `η := -(i/2)·n`, and check that `A* + i` kills the remainder `u - ψ - η`. -/
theorem adjoint_domain_cases (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    {u : H} (hu : u ∈ A.adjoint.domain) :
    ∃ (ψ : A.domain) (η : deficiencySubspacePlus A) (ξ : deficiencySubspaceMinus A),
      u = (ψ : H) + (η : H) + (ξ : H) := by
  -- split `A*u + iu` over the orthogonal decomposition `H = ran(A + i) ⊕ ran(A + i)ᗮ`
  have hMclosed : IsClosed ((Spectra.Resolvent.rangeSubmodule (A := A) (-I)) : Set H) :=
    Spectra.YosidaHille.op_range_isClosed hsym hclosed (-I) (by simp)
  haveI : CompleteSpace (Spectra.Resolvent.rangeSubmodule (A := A) (-I)) :=
    hMclosed.isComplete.completeSpace_coe
  obtain ⟨m, hm, n, hn, hmn⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := Spectra.Resolvent.rangeSubmodule (A := A) (-I)) (A.adjoint ⟨u, hu⟩ + I • u)
  obtain ⟨ψ, hψ⟩ := hm
  have hψm : A ψ - (-I) • (ψ : H) = m := hψ
  have hnN : n ∈ deficiencySubspacePlus A := orthogonal_le_deficiencySubspacePlus A hdense hn
  -- `η := -(i/2)·n` satisfies `(A* + i)η = n`
  set η : deficiencySubspacePlus A := (-(I / 2)) • (⟨n, hnN⟩ : deficiencySubspacePlus A)
    with hηdef
  have hηcoe : (η : H) = (-(I / 2)) • n := by rw [hηdef]; exact Submodule.coe_smul _ _
  -- memberships in the adjoint domain
  have hψadj : (ψ : H) ∈ A.adjoint.domain := (hsym.le_adjoint hdense).1 ψ.2
  have hηadj : (η : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspacePlus A η.2
  have hξadj : u - (ψ : H) - (η : H) ∈ A.adjoint.domain :=
    A.adjoint.domain.sub_mem (A.adjoint.domain.sub_mem hu hψadj) hηadj
  -- the adjoint of the remainder, expanded
  have hsub1 : A.adjoint ⟨u - (ψ : H), A.adjoint.domain.sub_mem hu hψadj⟩
      = A.adjoint ⟨u, hu⟩ - A.adjoint ⟨(ψ : H), hψadj⟩ := by
    have := A.adjoint.map_sub ⟨u, hu⟩ ⟨(ψ : H), hψadj⟩
    convert this using 2
  have hsub2 : A.adjoint ⟨u - (ψ : H) - (η : H), hξadj⟩
      = A.adjoint ⟨u - (ψ : H), A.adjoint.domain.sub_mem hu hψadj⟩
        - A.adjoint ⟨(η : H), hηadj⟩ := by
    have := A.adjoint.map_sub ⟨u - (ψ : H), A.adjoint.domain.sub_mem hu hψadj⟩
      ⟨(η : H), hηadj⟩
    convert this using 2
  have hAψ : A ψ = A.adjoint ⟨(ψ : H), hψadj⟩ :=
    (hsym.le_adjoint hdense).2 (x := ψ) (y := ⟨(ψ : H), hψadj⟩) rfl
  have hAη : A.adjoint ⟨(η : H), hηadj⟩ = I • (η : H) :=
    adjoint_apply_of_mem_deficiencySubspacePlus A η.2 hηadj
  have hAu : A.adjoint ⟨u, hu⟩ = m + n - I • u := eq_sub_of_add_eq hmn
  -- `ξ := u - ψ - η` is an eigenvector: `A*ξ = -iξ`
  have hcollapse : I • (η : H) + I • (η : H) = n := by
    rw [hηcoe, smul_smul, ← add_smul]
    have h2 : I * -(I / 2) + I * -(I / 2) = 1 := by
      have h3 : I * -(I / 2) + I * -(I / 2) = -(I * I) := by ring
      rw [h3, Complex.I_mul_I, neg_neg]
    rw [h2, one_smul]
  have hξval : A.adjoint ⟨u - (ψ : H) - (η : H), hξadj⟩
      = (-I) • (u - (ψ : H) - (η : H)) := by
    rw [hsub2, hsub1, ← hAψ, hAη, hAu, ← hψm, ← hcollapse]
    simp only [smul_sub, neg_smul, sub_neg_eq_add]
    abel
  have hξN : u - (ψ : H) - (η : H) ∈ deficiencySubspaceMinus A := ⟨hξadj, hξval⟩
  refine ⟨ψ, η, ⟨u - (ψ : H) - (η : H), hξN⟩, ?_⟩
  change u = (ψ : H) + (η : H) + (u - (ψ : H) - (η : H))
  abel

/-- **The first von Neumann formula** (closed case): for closed, symmetric, densely-defined
`A`,

  `D(A*) = D(A) ⊔ N₊(A) ⊔ N₋(A)`.

The sum is in fact direct (`existsUnique_deficiency_decomposition`) and orthogonal for the
graph inner product of `A*` (`graphInner_domain_deficiencySubspacePlus` and companions), so
this is the textbook `D(A*) = D(A) ⊕_g N₊(A) ⊕_g N₋(A)`. -/
theorem vonNeumannFormula (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H))) :
    A.adjoint.domain
      = A.domain ⊔ deficiencySubspacePlus A ⊔ deficiencySubspaceMinus A := by
  refine le_antisymm ?_ (sup_le (sup_le (hsym.le_adjoint hdense).1 ?_) ?_)
  · intro u hu
    obtain ⟨ψ, η, ξ, rfl⟩ := adjoint_domain_cases A hsym hdense hclosed hu
    exact Submodule.add_mem_sup (Submodule.add_mem_sup ψ.2 η.2) ξ.2
  · exact fun χ hχ => mem_adjoint_domain_of_mem_deficiencySubspacePlus A hχ
  · exact fun χ hχ => mem_adjoint_domain_of_mem_deficiencySubspaceMinus A hχ

/-! ### The action formula -/

/-- **The action formula**: on a decomposition `u = ψ + η + ξ` over
`D(A) + N₊(A) + N₋(A)`, the adjoint acts as `A*u = Aψ + iη - iξ`. No closedness is needed.
(This generalizes `vonNeumannExtension_apply_add_defect` from `D(A_V)` to all of `D(A*)`.) -/
theorem adjoint_apply_add_deficiency (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (ψ : A.domain) (η : deficiencySubspacePlus A) (ξ : deficiencySubspaceMinus A)
    {u : H} (hu : u ∈ A.adjoint.domain)
    (hdecomp : u = (ψ : H) + (η : H) + (ξ : H)) :
    A.adjoint ⟨u, hu⟩ = A ψ + I • (η : H) - I • (ξ : H) := by
  have hψadj : (ψ : H) ∈ A.adjoint.domain := (hsym.le_adjoint hdense).1 ψ.2
  have hηadj : (η : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspacePlus A η.2
  have hξadj : (ξ : H) ∈ A.adjoint.domain :=
    mem_adjoint_domain_of_mem_deficiencySubspaceMinus A ξ.2
  have hmem2 : (ψ : H) + (η : H) ∈ A.adjoint.domain := A.adjoint.domain.add_mem hψadj hηadj
  have hadd1 : A.adjoint ⟨(ψ : H) + (η : H), hmem2⟩
      = A.adjoint ⟨(ψ : H), hψadj⟩ + A.adjoint ⟨(η : H), hηadj⟩ := by
    have := A.adjoint.map_add ⟨(ψ : H), hψadj⟩ ⟨(η : H), hηadj⟩
    convert this using 2
  have hadd2 : A.adjoint ⟨(ψ : H) + (η : H) + (ξ : H), A.adjoint.domain.add_mem hmem2 hξadj⟩
      = A.adjoint ⟨(ψ : H) + (η : H), hmem2⟩ + A.adjoint ⟨(ξ : H), hξadj⟩ := by
    have := A.adjoint.map_add ⟨(ψ : H) + (η : H), hmem2⟩ ⟨(ξ : H), hξadj⟩
    convert this using 2
  have harg : (⟨u, hu⟩ : A.adjoint.domain)
      = ⟨(ψ : H) + (η : H) + (ξ : H), A.adjoint.domain.add_mem hmem2 hξadj⟩ :=
    Subtype.ext hdecomp
  have hAψ : A ψ = A.adjoint ⟨(ψ : H), hψadj⟩ :=
    (hsym.le_adjoint hdense).2 (x := ψ) (y := ⟨(ψ : H), hψadj⟩) rfl
  rw [harg, hadd2, hadd1, ← hAψ,
    adjoint_apply_of_mem_deficiencySubspacePlus A η.2 hηadj,
    adjoint_apply_of_mem_deficiencySubspaceMinus A ξ.2 hξadj,
    neg_smul, ← sub_eq_add_neg]

/-! ### Uniqueness -/

/-- **Uniqueness half of the first von Neumann formula** (zero form): if `ψ + η + ξ = 0` with
`ψ ∈ D(A)`, `η ∈ N₊(A)`, `ξ ∈ N₋(A)`, then all three summands vanish. No closedness is
needed: the action formula at `u = 0` gives `(Aψ + iψ) + 2iη = 0` whose summands lie in
`ran(A + i)` and `ran(A + i)ᗮ` respectively, and the off-axis lower bound
`Spectra.YosidaHille.op_lower_bound` then kills `ψ`. -/
theorem eq_zero_of_add_deficiency_eq_zero (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H))
    (ψ : A.domain) (η : deficiencySubspacePlus A) (ξ : deficiencySubspaceMinus A)
    (hsum : (ψ : H) + (η : H) + (ξ : H) = 0) :
    (ψ : H) = 0 ∧ (η : H) = 0 ∧ (ξ : H) = 0 := by
  -- the action formula at `u = 0`: `Aψ + iη - iξ = 0`
  have h0dom : (0 : H) ∈ A.adjoint.domain := A.adjoint.domain.zero_mem
  have hact : A.adjoint ⟨0, h0dom⟩ = A ψ + I • (η : H) - I • (ξ : H) :=
    adjoint_apply_add_deficiency A hsym hdense ψ η ξ h0dom hsum.symm
  have hAzero : A.adjoint ⟨0, h0dom⟩ = 0 := by
    have h := A.adjoint.map_zero
    convert h using 2
  have heq : (0 : H) = A ψ + I • (η : H) - I • (ξ : H) := hAzero.symm.trans hact
  -- substitute `ξ = -(ψ + η)`: `(Aψ + iψ) + 2iη = 0`
  have hξc : (ξ : H) = -((ψ : H) + (η : H)) := eq_neg_of_add_eq_zero_right hsum
  have hkey : (A ψ - (-I) • (ψ : H)) + ((2 : ℂ) * I) • (η : H) = 0 := by
    have h2 : ((2 : ℂ) * I) • (η : H) = I • (η : H) + I • (η : H) := by
      rw [mul_smul, two_smul]
    rw [h2, neg_smul, sub_neg_eq_add]
    rw [hξc] at heq
    simp only [smul_neg, smul_add, sub_neg_eq_add] at heq
    rw [eq_comm] at heq
    calc A ψ + I • (ψ : H) + (I • (η : H) + I • (η : H))
        = A ψ + I • (η : H) + (I • (ψ : H) + I • (η : H)) := by abel
      _ = 0 := heq
  -- the two summands are orthogonal, so both vanish
  have hmK : A ψ - (-I) • (ψ : H) ∈ Spectra.Resolvent.rangeSubmodule (A := A) (-I) := ⟨ψ, rfl⟩
  have hwN : ((2 : ℂ) * I) • (η : H) ∈ deficiencySubspacePlus A :=
    (deficiencySubspacePlus A).smul_mem _ η.2
  have hwOrth : ((2 : ℂ) * I) • (η : H)
      ∈ (Spectra.Resolvent.rangeSubmodule (A := A) (-I))ᗮ :=
    deficiencySubspacePlus_le_orthogonal A hdense hwN
  have hweq : ((2 : ℂ) * I) • (η : H) = -(A ψ - (-I) • (ψ : H)) :=
    eq_neg_of_add_eq_zero_right hkey
  have hwK : ((2 : ℂ) * I) • (η : H) ∈ Spectra.Resolvent.rangeSubmodule (A := A) (-I) := by
    rw [hweq]
    exact (Spectra.Resolvent.rangeSubmodule (A := A) (-I)).neg_mem hmK
  have hw0 : ((2 : ℂ) * I) • (η : H) = 0 :=
    inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hwK hwOrth)
  have hη0 : (η : H) = 0 := by
    rcases smul_eq_zero.mp hw0 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    · exact h
  -- the lower bound kills `ψ`
  have hm0 : A ψ - (-I) • (ψ : H) = 0 := by
    have h := hkey
    rw [hη0, smul_zero, add_zero] at h
    exact h
  have hψ0 : (ψ : H) = 0 := by
    have hlb := Spectra.YosidaHille.op_lower_bound hsym (-I) ψ
    rw [hm0, norm_zero] at hlb
    have him : |(-I).im| = 1 := by simp
    rw [him, one_mul] at hlb
    exact norm_le_zero_iff.mp hlb
  refine ⟨hψ0, hη0, ?_⟩
  rw [hξc, hψ0, hη0, add_zero, neg_zero]

/-- **The first von Neumann formula, unique-decomposition form** (closed case): every
`u ∈ D(A*)` decomposes **uniquely** as `u = ψ + η + ξ` over `D(A) ⊕ N₊(A) ⊕ N₋(A)`. -/
theorem existsUnique_deficiency_decomposition (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) (hclosed : IsClosed (A.graph : Set (H × H)))
    {u : H} (hu : u ∈ A.adjoint.domain) :
    ∃! p : A.domain × deficiencySubspacePlus A × deficiencySubspaceMinus A,
      u = (p.1 : H) + (p.2.1 : H) + (p.2.2 : H) := by
  obtain ⟨ψ, η, ξ, hdecomp⟩ := adjoint_domain_cases A hsym hdense hclosed hu
  refine ⟨⟨ψ, η, ξ⟩, hdecomp, ?_⟩
  rintro ⟨ψ', η', ξ'⟩ hdecomp'
  rw [hdecomp] at hdecomp'
  -- the componentwise differences decompose zero
  have hzero : ((ψ' - ψ : A.domain) : H) + ((η' - η : deficiencySubspacePlus A) : H)
      + ((ξ' - ξ : deficiencySubspaceMinus A) : H) = 0 := by
    push_cast
    calc ((ψ' : H) - (ψ : H)) + ((η' : H) - (η : H)) + ((ξ' : H) - (ξ : H))
        = ((ψ' : H) + (η' : H) + (ξ' : H)) - ((ψ : H) + (η : H) + (ξ : H)) := by abel
      _ = 0 := by rw [← hdecomp', sub_self]
  obtain ⟨h1, h2, h3⟩ := eq_zero_of_add_deficiency_eq_zero A hsym hdense _ _ _ hzero
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · exact sub_eq_zero.mp (by exact_mod_cast h1)
  · exact sub_eq_zero.mp (by exact_mod_cast h2)
  · exact sub_eq_zero.mp (by exact_mod_cast h3)

/-- **Graph-Pythagoras for the first von Neumann decomposition**: the graph norm of
`u = ψ + η + ξ` splits over the three graph-orthogonal summands,

  `‖u‖² + ‖A*u‖² = (‖ψ‖² + ‖Aψ‖²) + 2‖η‖² + 2‖ξ‖²`

(with `A*u = Aψ + iη - iξ` written out via the action formula, and `‖η‖²_graph = 2‖η‖²`
since `A*η = iη`). The `ψ`-cross terms die against the graph-orthogonality lemmas above; the
`η`-`ξ` cross terms cancel identically. No symmetry hypothesis is needed — only density (for
the cross-term identities). -/
theorem norm_sq_add_deficiency_decomposition (A : H →ₗ.[ℂ] H)
    (hdense : Dense (A.domain : Set H))
    (ψ : A.domain) (η : deficiencySubspacePlus A) (ξ : deficiencySubspaceMinus A) :
    ‖(ψ : H) + (η : H) + (ξ : H)‖ ^ 2 + ‖A ψ + I • (η : H) - I • (ξ : H)‖ ^ 2
      = ‖(ψ : H)‖ ^ 2 + ‖A ψ‖ ^ 2 + 2 * ‖(η : H)‖ ^ 2 + 2 * ‖(ξ : H)‖ ^ 2 := by
  have h1 := graphInner_domain_deficiencySubspacePlus A hdense ψ η
  have h2 := graphInner_domain_deficiencySubspaceMinus A hdense ψ ξ
  have h1c := congrArg (starRingEnd ℂ) h1
  have h2c := congrArg (starRingEnd ℂ) h2
  simp only [map_add, map_zero, inner_conj_symm] at h1c h2c
  have hC : ⟪(ψ : H) + (η : H) + (ξ : H), (ψ : H) + (η : H) + (ξ : H)⟫_ℂ
      + ⟪A ψ + I • (η : H) - I • (ξ : H), A ψ + I • (η : H) - I • (ξ : H)⟫_ℂ
      = ⟪(ψ : H), (ψ : H)⟫_ℂ + ⟪A ψ, A ψ⟫_ℂ
        + (⟪(η : H), (η : H)⟫_ℂ + ⟪(η : H), (η : H)⟫_ℂ)
        + (⟪(ξ : H), (ξ : H)⟫_ℂ + ⟪(ξ : H), (ξ : H)⟫_ℂ) := by
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, map_neg, neg_neg, Complex.conj_I] at h1 h2 h1c h2c ⊢
    linear_combination h1 + h1c + h2 + h2c
      + (⟪(η : H), (ξ : H)⟫_ℂ + ⟪(ξ : H), (η : H)⟫_ℂ - ⟪(η : H), (η : H)⟫_ℂ
          - ⟪(ξ : H), (ξ : H)⟫_ℂ) * Complex.I_mul_I
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hC
  have hR : ‖(ψ : H) + (η : H) + (ξ : H)‖ ^ 2 + ‖A ψ + I • (η : H) - I • (ξ : H)‖ ^ 2
      = ‖(ψ : H)‖ ^ 2 + ‖A ψ‖ ^ 2 + (‖(η : H)‖ ^ 2 + ‖(η : H)‖ ^ 2)
        + (‖(ξ : H)‖ ^ 2 + ‖(ξ : H)‖ ^ 2) := by exact_mod_cast hC
  linarith [hR]

/-! ### The general (non-closed) formula -/

/-- **The first von Neumann formula** (general case): for symmetric, densely-defined `A`,

  `D(A*) = D(Ā) ⊔ N₊(A) ⊔ N₋(A)`.

Apply the closed case to `Ā` and transport along `A* = (Ā)*` and `N±(Ā) = N±(A)`. -/
theorem vonNeumannFormula_closure (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (hdense : Dense (A.domain : Set H)) :
    A.adjoint.domain
      = A.closure.domain ⊔ deficiencySubspacePlus A ⊔ deficiencySubspaceMinus A := by
  have hclosable : A.IsClosable := symmetric_isClosable hsym hdense
  have h := vonNeumannFormula A.closure (closure_isFormalAdjoint hsym hdense)
    (dense_closure_domain hdense) hclosable.closure_isClosed
  rwa [closure_adjoint_eq_adjoint hdense hclosable,
    deficiencySubspacePlus_closure hdense hclosable,
    deficiencySubspaceMinus_closure hdense hclosable] at h

/-- Uniqueness in the general formula: a vanishing sum over `D(Ā) + N₊(A) + N₋(A)` has
vanishing parts. Stated in membership form so the deficiency memberships transport freely
between `A` and `Ā`. -/
theorem eq_zero_of_mem_closure_add_deficiency_eq_zero (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (hdense : Dense (A.domain : Set H))
    {x η ξ : H} (hx : x ∈ A.closure.domain) (hη : η ∈ deficiencySubspacePlus A)
    (hξ : ξ ∈ deficiencySubspaceMinus A) (hsum : x + η + ξ = 0) :
    x = 0 ∧ η = 0 ∧ ξ = 0 := by
  have hclosable : A.IsClosable := symmetric_isClosable hsym hdense
  have hη' : η ∈ deficiencySubspacePlus A.closure := by
    rw [deficiencySubspacePlus_closure hdense hclosable]; exact hη
  have hξ' : ξ ∈ deficiencySubspaceMinus A.closure := by
    rw [deficiencySubspaceMinus_closure hdense hclosable]; exact hξ
  exact eq_zero_of_add_deficiency_eq_zero A.closure (closure_isFormalAdjoint hsym hdense)
    (dense_closure_domain hdense) ⟨x, hx⟩ ⟨η, hη'⟩ ⟨ξ, hξ'⟩ hsum

end Spectra.Operator

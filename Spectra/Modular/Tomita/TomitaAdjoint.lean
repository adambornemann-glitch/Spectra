/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.PolarIsometry
/-!
# The adjoint of the Tomita closure: `S̄⋆ = S₀⋆`

For a von Neumann algebra `M` on `H` with cyclic separating vector `Ω`, the second Tomita
operator `F` is the adjoint of the *unclosed* Tomita operator `S₀ = tomitaOp M Ω`, while the
modular calculus (polar decomposition `S = JΔ^{½}`, `Δ = S⋆S`) runs through the *closure*
`S = tomitaClosure M Ω`. This file closes that gap: the adjoint cannot distinguish a
densely-defined closable operator from its closure, so

  `tomitaClosure_adjoint_eq : (tomitaClosure M Ω).adjoint = (tomitaOp M Ω).adjoint`.

Consequently the known action of `F` on the commutant orbit transfers to `S̄⋆`
(`tomitaClosure_adjoint_apply_commutant : S̄⋆ (toConj (b Ω)) = b⋆ Ω` for `b ∈ M'`).

This is an **engine for the base-`M` Tomita theorem build** — fields 6/7/8 of `ModularData`
(`Δ^{it} M Δ^{-it} = M`, `J M J = M'`, `J Ω = Ω` as *theorems* about the concrete modular
objects): the standard proofs manipulate `F = S⋆` on commutant vectors while `S` itself is the
closed operator, and this identification is used silently throughout the literature
(Bratteli–Robinson I, Section 2.5.2). The existing UOT layer
(`Spectra.Operator.closure_adjoint_eq_adjoint`) proves this for `H →ₗ.[ℂ] H` only; the Tomita
operator lives in `H →ₗ.[ℂ] Conj H`, so we give a self-contained two-Hilbert-space proof by
antisymmetry: `S₀ ≤ S̄` forces `S̄⋆ ≤ S₀⋆` (adjoint antitonicity), and `S₀⋆` is a formal adjoint
of `S̄` (graph-limit continuity), hence `S₀⋆ ≤ S̄⋆` by adjoint maximality.

See the vault plan (Projects/Modular Theory) and
`Spectra/Modular/TomitaTakesaki/ROADMAP.md`.
-/

open scoped InnerProductSpace
open Spectra.Conj

namespace Spectra.TomitaTakesaki

/-! ## Generic two-Hilbert-space `LinearPMap` adjoint lemmas

Mathlib's `LinearPMap.adjoint` API has no antitonicity lemma, and the Spectra UOT layer
(`Spectra/Operator/AdjointClosure.lean`) states its closure/adjoint results for `H →ₗ.[ℂ] H`
only. The two private lemmas here are the `E →ₗ.[ℂ] F` versions needed for the Tomita operator
`H →ₗ.[ℂ] Conj H`; they are analytic (no graph `Submodule.adjoint`), so they need nothing beyond
completeness of the domain space. -/

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E]

/-- The adjoint identity of `B⋆` restricts along any sub-operator `A ≤ B`:
`⟪B⋆ y, v⟫ = ⟪y, A v⟫` for `y ∈ D(B⋆)` and `v ∈ D(A)`. -/
private theorem adjoint_inner_restrict {A B : E →ₗ.[ℂ] F} (hdenseB : Dense (B.domain : Set E))
    (hAB : A ≤ B) (y : B.adjoint.domain) (v : A.domain) :
    ⟪B.adjoint y, (v : E)⟫_ℂ = ⟪(y : F), A v⟫_ℂ := by
  have hvB : (v : E) ∈ B.domain := hAB.1 v.2
  have h1 : ⟪B.adjoint y, ((⟨(v : E), hvB⟩ : B.domain) : E)⟫_ℂ
      = ⟪(y : F), B ⟨(v : E), hvB⟩⟫_ℂ :=
    LinearPMap.adjoint_isFormalAdjoint hdenseB y ⟨(v : E), hvB⟩
  rwa [← hAB.2 (rfl : (v : E) = ((⟨(v : E), hvB⟩ : B.domain) : E))] at h1

/-- **The adjoint reverses extension** (two-space version): if `A ≤ B` with `A` densely defined,
then `B⋆ ≤ A⋆`. Membership via `mem_adjoint_domain_of_exists` (witness `B⋆ y`), values via
`adjoint_apply_eq`. -/
private theorem adjoint_antitone {A B : E →ₗ.[ℂ] F} (hdenseA : Dense (A.domain : Set E))
    (hAB : A ≤ B) : B.adjoint ≤ A.adjoint := by
  have hdenseB : Dense (B.domain : Set E) := hdenseA.mono (SetLike.coe_subset_coe.mpr hAB.1)
  refine ⟨fun y hy => LinearPMap.mem_adjoint_domain_of_exists _
    ⟨B.adjoint ⟨y, hy⟩, fun v => adjoint_inner_restrict hdenseB hAB ⟨y, hy⟩ v⟩, ?_⟩
  intro x y hxy
  refine (LinearPMap.adjoint_apply_eq hdenseA y fun v => ?_).symm
  rw [show ((y : F) : F) = (x : F) from hxy.symm]
  exact adjoint_inner_restrict hdenseB hAB x v

/-- **The adjoint of `A` is a formal adjoint of the closure `Ā`**: for `x ∈ D(Ā)` and
`y ∈ D(A⋆)`, `⟪Ā x, y⟫ = ⟪x, A⋆ y⟫`. The pairs `(x, Ā x)` are graph-limits of pairs from `A`,
on which the identity is `adjoint_isFormalAdjoint`; the identity survives the limit because the
defect `p ↦ ⟪p.2, y⟫ - ⟪p.1, A⋆ y⟫` is continuous. -/
private theorem closure_isFormalAdjoint {A : E →ₗ.[ℂ] F} (hdense : Dense (A.domain : Set E))
    (hclosable : A.IsClosable) : A.closure.IsFormalAdjoint A.adjoint := by
  intro x y
  -- the locus of the adjoint identity is closed …
  have hclosed : IsClosed {p : E × F | ⟪p.2, (y : F)⟫_ℂ = ⟪p.1, A.adjoint y⟫_ℂ} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  -- … and contains the graph of `A`
  have hsub : (A.graph : Set (E × F)) ⊆ {p | ⟪p.2, (y : F)⟫_ℂ = ⟪p.1, A.adjoint y⟫_ℂ} := by
    intro p hp
    obtain ⟨z, hz1, hz2⟩ := A.mem_graph_iff.mp hp
    simp only [Set.mem_setOf_eq, ← hz1, ← hz2]
    calc ⟪A z, (y : F)⟫_ℂ
        = starRingEnd ℂ ⟪(y : F), A z⟫_ℂ := (inner_conj_symm _ _).symm
      _ = starRingEnd ℂ ⟪A.adjoint y, (z : E)⟫_ℂ := by
          rw [LinearPMap.adjoint_isFormalAdjoint hdense y z]
      _ = ⟪(z : E), A.adjoint y⟫_ℂ := inner_conj_symm _ _
  -- each `(x, Ā x)` lies in the closure of the graph of `A`
  have hgraph : ((x : E), A.closure x) ∈ closure (A.graph : Set (E × F)) := by
    have hx : ((x : E), A.closure x) ∈ A.closure.graph := A.closure.mem_graph x
    rw [← hclosable.graph_closure_eq_closure_graph] at hx
    rw [← Submodule.topologicalClosure_coe, SetLike.mem_coe]
    exact hx
  exact closure_minimal hsub hclosed hgraph

end Generic

/-! ## The Tomita specialization: `S̄⋆ = F` -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-- **The adjoint of the Tomita closure is the second Tomita operator**:
`(S̄)⋆ = S₀⋆ (= F)`. Antisymmetry: `S₀ ≤ S̄` gives `S̄⋆ ≤ S₀⋆` (antitonicity), and `S₀⋆` is a
formal adjoint of `S̄` (graph-limit continuity), so `S₀⋆ ≤ S̄⋆` by adjoint maximality. -/
theorem tomitaClosure_adjoint_eq (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    (tomitaClosure M Ω).adjoint = (tomitaOp M Ω).adjoint := by
  have hdense : Dense ((tomitaOp M Ω).domain : Set H) := tomitaOp_domain_dense M Ω hcyc
  have hclosable : (tomitaOp M Ω).IsClosable := tomitaOp_isClosable hcyc hsep
  have hdenseC : Dense (((tomitaOp M Ω).closure.domain : Submodule ℂ H) : Set H) :=
    hdense.mono (SetLike.coe_subset_coe.mpr (tomitaOp M Ω).le_closure.1)
  exact le_antisymm (adjoint_antitone hdense (tomitaOp M Ω).le_closure)
    ((closure_isFormalAdjoint hdense hclosable).le_adjoint hdenseC)

/-- For `b ∈ M'`, the vector `toConj (b Ω)` lies in the domain of `S̄⋆` — the domain of the
adjoint of the *closure*, not merely of `S₀⋆` (`toConj_mem_adjoint_domain`). -/
theorem toConj_mem_tomitaClosure_adjoint_domain (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    {b : H →L[ℂ] H} (hb : b ∈ M.commutant) :
    toConj (b Ω) ∈ (tomitaClosure M Ω).adjoint.domain := by
  rw [tomitaClosure_adjoint_eq hcyc hsep]
  exact toConj_mem_adjoint_domain hsep hb

/-- The value of `S̄⋆` on the commutant orbit: `S̄⋆ (toConj (b Ω)) = b⋆ Ω` for `b ∈ M'` —
`tomitaAdjoint_apply_commutant` transported through `tomitaClosure_adjoint_eq`. -/
theorem tomitaClosure_adjoint_apply_commutant (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    {b : H →L[ℂ] H} (hb : b ∈ M.commutant) :
    (tomitaClosure M Ω).adjoint
      ⟨toConj (b Ω), toConj_mem_tomitaClosure_adjoint_domain hcyc hsep hb⟩ = (star b) Ω :=
  ((tomitaClosure_adjoint_eq hcyc hsep).le.2 rfl).trans
    (tomitaAdjoint_apply_commutant hcyc hsep hb)

end Spectra.TomitaTakesaki

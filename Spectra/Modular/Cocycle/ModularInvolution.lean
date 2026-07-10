/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularVacuum
/-!
# The Tomita involution `S̃² = 1` — foundation for `J² = 1` (R4a, field 3)

This file assembles the genuine content behind the remaining structural `ModularData` field
`J_involutive : ∀ x, J (J x) = x` (`J² = 1`, the modular conjugation is an involution).

## What is proved here (route-independent, sorry-free)

The antilinear Tomita operator `S̃ = ofConj ∘ S : H ⊇ D(S) → H` (where `S = tomitaClosure M Ω`) is
an **involution on the core** `M Ω`: for `a ∈ M`, `S̃ (a Ω) = (star a) Ω`  (`sTilde_core`), hence
`S̃ (S̃ (a Ω)) = (star (star a)) Ω = a Ω` (`sTilde_involutive_core`). This is the `S² ⊆ 1` seed of
Tomita–Takesaki, and it needs **no** `Δ`, `Δ^{½}`, `J`, or adjoint theory — only `tomitaOp_apply`
(`S₀ (a Ω) = toConj ((star a) Ω)`) and `star_star`. Together with the polar helpers
`modularConjugation_apply` (`J y = ofConj (W y)`) and `modularConjugation_apply_modularSqrt`
(`J (Δ^{½} x) = ofConj (S x)`), these are the building blocks of the field-3 proof.

## The Tomita involution on all of `D(S)` (closure level)

`sTilde_involutive_core` gives `S̃²=1` only on the core `M Ω`. This is upgraded here to the whole
domain `D(S)` of the closure — `sTilde_closure_involutive` (`S̃ (S̃ y) = y` for `y ∈ D(S)`) — by a
graph-closure argument: the continuous conjugate-linear swap `σ(u,v) = (ofConj v, toConj u)` sends
the core graph generator at `T` to the generator at `star T`, so it preserves `Γ(S₀)`, hence its
closure `Γ(S)`; applied to `(y, S y)` it yields `(S̃ y, toConj y) ∈ Γ(S)`, i.e. `S̃ y ∈ D(S)` and
`S̃(S̃ y)=y`. This is the genuine closed-operator `S² = 1`, proved with **no** `Δ`/`Δ^{½}`/adjoint
calculus.

## The remaining node (`J² = 1`, not closed here)

Closing `J (J (Δ^{½} x)) = Δ^{½} x` needs `W (S̃ x)`, whose only handle is `range (Δ^{½}|_{D(Δ)})`
(via the polar relation `W (Δ^{½} x') = S x'`). The involution `sTilde_closure_involutive` gives
`S̃ x ∈ D(S) = D(Δ^{½})`, but that is a *strictly larger* set than `range (Δ^{½}|_{D(Δ)})`. Bridging
the two is exactly extending the polar relation `S = J Δ^{½}` from `D(Δ)` to the full `D(Δ^{½})` —
which is what `Δ^{½}` self-adjointness `(Δ^{½})² = Δ` plus polar-decomposition uniqueness deliver
(Route B; see the vault plan `Field 3 - J Involution Plan.md`). That step is deferred; this file
supplies the involution it will build on.
-/

open scoped InnerProductSpace
open Spectra.Conj

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ## The modular conjugation, unfolded -/

/-- `J y = ofConj (W y)`: the modular conjugation is `ofConj` after the polar isometry `W`. -/
theorem modularConjugation_apply (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (y : H) :
    modularConjugation hcyc hsep y = ofConj (modularW hcyc hsep y) := by
  rw [modularConjugation, LinearIsometryEquiv.trans_apply, Conj.coe_toConjₗᵢ_symm]

/-- `J (Δ^{½} x) = ofConj (S x)` for `x ∈ D(Δ)`: the polar decomposition `S = J Δ^{½}` in `H`. -/
theorem modularConjugation_apply_modularSqrt (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (modularOp M Ω).domain) :
    modularConjugation hcyc hsep (modularSqrtOnModularDomain hcyc hsep x)
      = ofConj (tomitaOnModularDomain M Ω x) := by
  rw [modularConjugation_apply, modularW_apply_modularSqrt]

/-! ## The Tomita operator on the core, and its involution -/

/-- `(star a) Ω ∈ D(S)` for `a ∈ M`: the involution stays inside the domain of the Tomita operator
(both `a Ω` and `(star a) Ω` lie in the core `M Ω ⊆ D(S)`). -/
theorem star_smul_vacuum_mem_domain {a : H →L[ℂ] H} (ha : a ∈ M) :
    (star a) Ω ∈ (tomitaClosure M Ω).domain := by
  have h : (star a) Ω ∈ (tomitaOp M Ω).domain := by
    rw [tomitaOp_domain_eq_span]
    exact Submodule.subset_span ⟨star a, star_mem ha, rfl⟩
  exact (LinearPMap.le_closure (tomitaOp M Ω)).1 h

/-- `S (a Ω) = toConj ((star a) Ω)` for `a ∈ M`: the Tomita operator on the core, transported to the
closure (mirrors `tomitaClosure_vacuum`). -/
theorem tomitaClosure_apply_core (hsep : IsSeparating M Ω) {a : H →L[ℂ] H} (ha : a ∈ M)
    (h : a Ω ∈ (tomitaClosure M Ω).domain) :
    tomitaClosure M Ω ⟨a Ω, h⟩ = toConj ((star a) Ω) := by
  have hΩop : a Ω ∈ (tomitaOp M Ω).domain := by
    rw [tomitaOp_domain_eq_span]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  have hagree : tomitaOp M Ω ⟨a Ω, hΩop⟩ = tomitaClosure M Ω ⟨a Ω, h⟩ :=
    (LinearPMap.le_closure (tomitaOp M Ω)).2 rfl
  have hop : tomitaOp M Ω ⟨a Ω, hΩop⟩ = toConj ((star a) Ω) :=
    tomitaOp_apply M Ω hsep ha hΩop
  rw [← hagree, hop]

/-- **`S̃ (a Ω) = (star a) Ω`** for `a ∈ M`: the antilinear Tomita operator `S̃ = ofConj ∘ S` on the
core. -/
theorem sTilde_core (hsep : IsSeparating M Ω) {a : H →L[ℂ] H} (ha : a ∈ M)
    (h : a Ω ∈ (tomitaClosure M Ω).domain) :
    ofConj (tomitaClosure M Ω ⟨a Ω, h⟩) = (star a) Ω := by
  rw [tomitaClosure_apply_core hsep ha h, Conj.ofConj_toConj]

/-- **The Tomita involution on the core: `S̃ (S̃ (a Ω)) = a Ω`.**  Since `S̃ (a Ω) = (star a) Ω`
(`sTilde_core`), applying `S̃` again gives `(star (star a)) Ω = a Ω`.  This is the `S² ⊆ 1` seed of
Tomita–Takesaki, proved with no `Δ`/`J`/adjoint theory. -/
theorem sTilde_involutive_core (hsep : IsSeparating M Ω) {a : H →L[ℂ] H} (ha : a ∈ M)
    (h1 : a Ω ∈ (tomitaClosure M Ω).domain)
    (h2 : ofConj (tomitaClosure M Ω ⟨a Ω, h1⟩) ∈ (tomitaClosure M Ω).domain) :
    ofConj (tomitaClosure M Ω ⟨ofConj (tomitaClosure M Ω ⟨a Ω, h1⟩), h2⟩) = a Ω := by
  -- The inner `S̃ (a Ω)` equals `(star a) Ω`; recast the outer subtype, then apply
  -- `S̃` at `star a`.
  have hval : ofConj (tomitaClosure M Ω ⟨a Ω, h1⟩) = (star a) Ω := sTilde_core hsep ha h1
  have hcast : (⟨ofConj (tomitaClosure M Ω ⟨a Ω, h1⟩), h2⟩ : (tomitaClosure M Ω).domain)
      = ⟨(star a) Ω, star_smul_vacuum_mem_domain ha⟩ := Subtype.ext hval
  rw [hcast, sTilde_core hsep (star_mem ha) (star_smul_vacuum_mem_domain ha), star_star]

/-! ## The Tomita involution on all of `D(S)`

The continuous conjugate-linear swap `σ(u,v) = (ofConj v, toConj u)` preserves the core graph, hence
its closure, upgrading `S̃²=1` from `M Ω` to the whole domain of the closure. -/

/-- The continuous conjugate-linear swap `σ(u,v) = (ofConj v, toConj u)` on `H × Conj H`. -/
private def swapConj : (H × Conj H) → (H × Conj H) := fun p => (ofConj p.2, toConj p.1)

omit [CompleteSpace H] in
private lemma continuous_swapConj : Continuous (swapConj : H × Conj H → H × Conj H) := by
  have hct : Continuous (toConj : H → Conj H) := by
    rw [← Conj.coe_toConjₗᵢ (E := H)]; exact (Conj.toConjₗᵢ H).continuous
  have hco : Continuous (ofConj : Conj H → H) := by
    rw [← Conj.coe_toConjₗᵢ_symm (E := H)]; exact (Conj.toConjₗᵢ H).symm.continuous
  exact (hco.comp continuous_snd).prodMk (hct.comp continuous_fst)

/-- `σ` sends the core graph `Γ(S₀)` into itself: the generator at `T` goes to the generator at
`star T` (using `star T ∈ M` and `star (star T) = T`). -/
private lemma swapConj_mem_tomitaGraph {v : H × Conj H} (hv : v ∈ tomitaGraph M Ω) :
    swapConj v ∈ tomitaGraph M Ω := by
  rw [tomitaGraph, Submodule.mem_map] at hv ⊢
  obtain ⟨T, hT, rfl⟩ := hv
  refine ⟨star T, mem_toSubmodule.mpr (star_mem (mem_toSubmodule.mp hT)), ?_⟩
  have e1 : (evalAt Ω).prod (tomitaPre Ω) (star T)
      = (evalAt Ω (star T), tomitaPre Ω (star T)) := rfl
  have e2 : swapConj ((evalAt Ω).prod (tomitaPre Ω) T)
      = (ofConj (tomitaPre Ω T), toConj (evalAt Ω T)) := rfl
  rw [e1, e2, evalAt_apply, evalAt_apply, tomitaPre_apply, tomitaPre_apply, ofConj_toConj,
    star_star]

/-- The swapped pair `(S̃ y, toConj y)` lands in the closed graph `Γ(S)` for `y ∈ D(S)`. -/
theorem swapConj_tomitaClosure_graph (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (y : (tomitaClosure M Ω).domain) :
    (ofConj (tomitaClosure M Ω y), toConj (y : H)) ∈ (tomitaClosure M Ω).graph := by
  have hcl : (tomitaOp M Ω).IsClosable := tomitaOp_isClosable hcyc hsep
  have hopgraph : (tomitaOp M Ω).graph = tomitaGraph M Ω :=
    Submodule.toLinearPMap_graph_eq (tomitaGraph M Ω) (tomitaGraph_functional M Ω hsep)
  have hclgraph : (tomitaClosure M Ω).graph = (tomitaGraph M Ω).topologicalClosure := by
    rw [tomitaClosure, ← hcl.graph_closure_eq_closure_graph, hopgraph]
  have hmem : ((y : H), tomitaClosure M Ω y) ∈ closure (↑(tomitaGraph M Ω) : Set (H × Conj H)) := by
    have h := LinearPMap.mem_graph (tomitaClosure M Ω) y
    rw [hclgraph, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h
    exact h
  have himg : swapConj '' (↑(tomitaGraph M Ω) : Set (H × Conj H))
      ⊆ (↑(tomitaGraph M Ω) : Set (H × Conj H)) := by
    rintro _ ⟨v, hv, rfl⟩; exact swapConj_mem_tomitaGraph hv
  have key : swapConj ((y : H), tomitaClosure M Ω y)
      ∈ closure (↑(tomitaGraph M Ω) : Set (H × Conj H)) :=
    ((image_closure_subset_closure_image continuous_swapConj).trans (closure_mono himg))
      ⟨_, hmem, rfl⟩
  rw [hclgraph, ← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact key

/-- `S̃ y ∈ D(S)` for every `y ∈ D(S)`: the closure's domain is `S̃`-invariant. -/
theorem sTilde_closure_mem_domain (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (y : (tomitaClosure M Ω).domain) :
    ofConj (tomitaClosure M Ω y) ∈ (tomitaClosure M Ω).domain := by
  obtain ⟨z, hz1, _⟩ := (LinearPMap.mem_graph_iff _).mp (swapConj_tomitaClosure_graph hcyc hsep y)
  have hz1' : (z : H) = ofConj (tomitaClosure M Ω y) := hz1
  exact hz1' ▸ z.2

/-- **The Tomita involution on `D(S)`: `S̃ (S̃ y) = y`.** The genuine closed-operator `S² = 1`,
upgraded from the core `M Ω` (`sTilde_involutive_core`) to the whole domain of the closure, via the
continuous conjugate-linear graph-symmetry `swapConj`. No `Δ`/`Δ^{½}`/adjoint calculus is used. -/
theorem sTilde_closure_involutive (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (y : (tomitaClosure M Ω).domain) :
    ofConj (tomitaClosure M Ω
        ⟨ofConj (tomitaClosure M Ω y), sTilde_closure_mem_domain hcyc hsep y⟩) = (y : H) := by
  obtain ⟨z, hz1, hz2⟩ := (LinearPMap.mem_graph_iff _).mp (swapConj_tomitaClosure_graph hcyc hsep y)
  have hz1' : (z : H) = ofConj (tomitaClosure M Ω y) := hz1
  have hz2' : tomitaClosure M Ω z = toConj (y : H) := hz2
  have hzeq : (⟨ofConj (tomitaClosure M Ω y), sTilde_closure_mem_domain hcyc hsep y⟩ :
      (tomitaClosure M Ω).domain) = z := Subtype.ext hz1'.symm
  rw [hzeq, hz2', Conj.ofConj_toConj]

end Spectra.TomitaTakesaki

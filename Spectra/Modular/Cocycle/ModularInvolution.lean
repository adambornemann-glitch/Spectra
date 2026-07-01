/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularVacuum
/-!
# The Tomita involution `S̃² = 1` — foundation for `J² = 1` (R4a, field 3)

This file assembles the genuine content behind the remaining structural `ModularData` field
`J_involutive : ∀ x, J (J x) = x` (`J² = 1`, the modular conjugation is an involution).

## What is proved here (route-independent, sorry-free)

The antilinear Tomita operator `S̃ = ofConj ∘ S : H ⊇ D(S) → H` (where `S = tomitaClosure M Ω`) is an
**involution on the core** `M Ω`: for `a ∈ M`,
`S̃ (a Ω) = (star a) Ω`  (`sTilde_core`), hence `S̃ (S̃ (a Ω)) = (star (star a)) Ω = a Ω`
(`sTilde_involutive_core`). This is the `S² ⊆ 1` seed of Tomita–Takesaki, and it needs **no**
`Δ`, `Δ^{½}`, `J`, or adjoint theory — only `tomitaOp_apply` (`S₀ (a Ω) = toConj ((star a) Ω)`) and
`star_star`. Together with the polar helpers `modularConjugation_apply` (`J y = ofConj (W y)`) and
`modularConjugation_apply_modularSqrt` (`J (Δ^{½} x) = ofConj (S x)`), these are the building blocks
of the field-3 proof.

## The remaining node (`J² = 1`, not yet closed here)

Closing `J (J (Δ^{½} x)) = Δ^{½} x` requires knowing `S̃ x ∈ range Δ^{½}` (so the polar relation
`W (Δ^{½} x') = S x'` fires on the outer `J`). The core `M Ω` carries the involution but is not
contained in `D(Δ)` where the polar relation lives, while `range Δ^{½}` carries the polar relation but
not (yet) the involution: the two dense sets do not line up. Bridging them needs either the
closed-operator inclusion `S̃² ⊆ 1` with `S̃ (D(Δ)) ⊆ D(S)`, or `Δ^{½}` self-adjointness `(Δ^{½})² = Δ`
(an open R2 nicety) plus polar-decomposition uniqueness. That step is deferred; this file supplies the
verified foundation it will build on.
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
  -- The inner `S̃ (a Ω)` equals `(star a) Ω`; recast the outer subtype, then apply `S̃` at `star a`.
  have hval : ofConj (tomitaClosure M Ω ⟨a Ω, h1⟩) = (star a) Ω := sTilde_core hsep ha h1
  have hcast : (⟨ofConj (tomitaClosure M Ω ⟨a Ω, h1⟩), h2⟩ : (tomitaClosure M Ω).domain)
      = ⟨(star a) Ω, star_smul_vacuum_mem_domain ha⟩ := Subtype.ext hval
  rw [hcast, sTilde_core hsep (star_mem ha) (star_smul_vacuum_mem_domain ha), star_star]

end Spectra.TomitaTakesaki

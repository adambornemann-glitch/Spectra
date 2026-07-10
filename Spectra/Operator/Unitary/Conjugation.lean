/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Helpers
/-!
# Unitary conjugation of unbounded self-adjoint operators

Transport of an unbounded operator `A : H →ₗ.[ℂ] H` across a **unitary** `U : H ≃ₗᵢ[ℂ] H'` to the
operator `U A U⁻¹ : H' →ₗ.[ℂ] H'`, together with the theorem that this transport **preserves
self-adjointness** (and energy nonnegativity). Unitary equivalence is the workhorse for moving a
concretely diagonalised operator — e.g. `−Δ` on `L²(ℝᵈ)`, self-adjoint via the Fourier transform —
onto a unitarily isomorphic model — e.g. the antisymmetric `L²` of many-body quantum mechanics. The
abstract statement here is what makes such a transport a one-liner instead of a re-proof; it is the
linchpin for carrying the kinetic operator `−½Δ` onto the `N`-electron coordinate space of Density
Functional Theory (Stage SB).

This is the honest `ℂ`-linear twin of the antiunitary `TomitaTakesaki.conjPMap`
(`Modular/Cocycle/ModularPolarUniqueness.lean`): where the antiunitary version carries an inner
identity hypothesis `⟪e u, e v⟫ = ⟪v, u⟫` and swaps the deficiency signs, the unitary version needs
neither — `⟪U u, U v⟫ = ⟪u, v⟫` is automatic (`LinearIsometryEquiv.inner_map_map`) and the `(· ± i)`
surjectivities transfer without a swap.

## Main definitions

* `Spectra.Operator.unitaryConj` — the conjugated operator `U A U⁻¹ : H' →ₗ.[ℂ] H'`, with domain
  `U(D(A))`.

## Main results

* `Spectra.Operator.unitaryConj_isSelfAdjoint` — **self-adjointness transfers**: `IsSelfAdjoint A ⟹
  IsSelfAdjoint (U A U⁻¹)`, via the von Neumann deficiency criterion (symmetry, density, and both
  `(· ± i)` surjectivities transfer through `U`).
* `Spectra.Operator.unitaryConj_re_inner_nonneg` — **energy nonnegativity transfers**:
  `0 ≤ Re⟪x, A x⟫` on `D(A)` gives `0 ≤ Re⟪y, (U A U⁻¹) y⟫` on `D(U A U⁻¹)` (the form-positivity
  half of `T ≥ 0`).

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII (von Neumann's
  self-adjointness criterion; unitary invariance of self-adjointness).
-/
open Complex
open scoped InnerProductSpace
open Spectra.YosidaHille Spectra.OneParameterUnitaryGroup

namespace Spectra.Operator

variable {H H' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

section UnitaryConj

variable (U : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H)

/-- **Conjugation `A ↦ U A U⁻¹` of an unbounded operator by a unitary** `U : H ≃ₗᵢ[ℂ] H'`, as a
`LinearPMap` on `H'` with domain `U(D(A)) = (U⁻¹)⁻¹(D(A))` and action `y ↦ U (A (U⁻¹ y))`. Both `U`
and `U⁻¹` are `ℂ`-linear, so the result is honestly `ℂ`-linear (no conjugation appears). -/
noncomputable def unitaryConj : H' →ₗ.[ℂ] H' where
  domain := A.domain.comap (U.symm.toLinearEquiv : H' →ₗ[ℂ] H)
  toFun :=
    { toFun := fun x => U (A ⟨U.symm (x : H'), x.2⟩)
      map_add' := fun x y => by
        have hsub : (⟨U.symm ((x : H') + (y : H')), (x + y).2⟩ : A.domain)
            = ⟨U.symm (x : H'), x.2⟩ + ⟨U.symm (y : H'), y.2⟩ :=
          Subtype.ext (by simp)
        simp only [Submodule.coe_add]
        rw [hsub, A.map_add, map_add]
      map_smul' := fun c x => by
        have hsub : (⟨U.symm (c • (x : H')), (c • x).2⟩ : A.domain)
            = c • ⟨U.symm (x : H'), x.2⟩ :=
          Subtype.ext (by
            change U.symm (c • (x : H')) = c • U.symm (x : H')
            exact map_smul U.symm c (x : H'))
        simp only [Submodule.coe_smul]
        rw [hsub, A.map_smul, map_smul]
        rfl }

omit [CompleteSpace H] [CompleteSpace H'] in
/-- Membership in the conjugated domain is definitional: `x ∈ D(U A U⁻¹) ↔ U⁻¹ x ∈ D(A)`. -/
lemma mem_unitaryConj_domain_iff {x : H'} :
    x ∈ (unitaryConj U A).domain ↔ U.symm x ∈ A.domain := Iff.rfl

omit [CompleteSpace H] [CompleteSpace H'] in
/-- The defining formula `(U A U⁻¹) x = U (A (U⁻¹ x))`. -/
lemma unitaryConj_apply (x : (unitaryConj U A).domain) :
    unitaryConj U A x = U (A ⟨U.symm (x : H'), x.2⟩) := rfl

omit [CompleteSpace H] [CompleteSpace H'] in
/-- `U` maps `D(A)` into `D(U A U⁻¹)`. -/
lemma map_mem_unitaryConj_domain (y : A.domain) : U (y : H) ∈ (unitaryConj U A).domain := by
  rw [mem_unitaryConj_domain_iff, U.symm_apply_apply]
  exact y.2

omit [CompleteSpace H] [CompleteSpace H'] in
/-- `(U A U⁻¹)(U y) = U (A y)` on `D(A)`. -/
lemma unitaryConj_apply_map (y : A.domain) :
    unitaryConj U A ⟨U (y : H), map_mem_unitaryConj_domain U A y⟩ = U (A y) := by
  rw [unitaryConj_apply]
  congr 1
  exact congrArg A (Subtype.ext (U.symm_apply_apply (y : H)))

variable {U A}

omit [CompleteSpace H] [CompleteSpace H'] in
/-- **Symmetry transfers through the conjugation**: if `A` is symmetric then so is `U A U⁻¹`. Unlike
the antiunitary case, the inner identity `⟪U u, U v⟫ = ⟪u, v⟫` is automatic. -/
theorem unitaryConj_isFormalAdjoint_self (hsym : A.IsFormalAdjoint A) :
    (unitaryConj U A).IsFormalAdjoint (unitaryConj U A) := by
  intro x y
  rw [unitaryConj_apply, unitaryConj_apply]
  calc ⟪U (A ⟨U.symm (x : H'), x.2⟩), (y : H')⟫_ℂ
      = ⟪U (A ⟨U.symm (x : H'), x.2⟩), U (U.symm (y : H'))⟫_ℂ := by rw [U.apply_symm_apply]
    _ = ⟪A ⟨U.symm (x : H'), x.2⟩, U.symm (y : H')⟫_ℂ := U.inner_map_map _ _
    _ = ⟪U.symm (x : H'), A ⟨U.symm (y : H'), y.2⟩⟫_ℂ :=
        hsym ⟨U.symm (x : H'), x.2⟩ ⟨U.symm (y : H'), y.2⟩
    _ = ⟪U (U.symm (x : H')), U (A ⟨U.symm (y : H'), y.2⟩)⟫_ℂ := (U.inner_map_map _ _).symm
    _ = ⟪(x : H'), U (A ⟨U.symm (y : H'), y.2⟩)⟫_ℂ := by rw [U.apply_symm_apply]

omit [CompleteSpace H] [CompleteSpace H'] in
/-- **Density transfers through the conjugation**: `D(U A U⁻¹) = (U⁻¹)⁻¹(D(A))` is dense when `D(A)`
is (preimage of a dense set under a homeomorphism). -/
theorem unitaryConj_dense_domain (hdense : Dense (A.domain : Set H)) :
    Dense ((unitaryConj U A).domain : Set H') := by
  have hset : ((unitaryConj U A).domain : Set H')
      = (U.symm.toHomeomorph) ⁻¹' (A.domain : Set H) := rfl
  rw [hset, dense_iff_closure_eq, ← Homeomorph.preimage_closure, hdense.closure_eq,
    Set.preimage_univ]

omit [CompleteSpace H] [CompleteSpace H'] in
/-- **Surjectivity of `U A U⁻¹ + i` from surjectivity of `A + i`** — no sign swap (the map is
linear). -/
theorem unitaryConj_add_I_surjective
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    ∀ φ : H', ∃ ψ : (unitaryConj U A).domain, unitaryConj U A ψ + I • (ψ : H') = φ := by
  intro φ
  obtain ⟨w, hw⟩ := hplus (U.symm φ)
  refine ⟨⟨U (w : H), map_mem_unitaryConj_domain U A w⟩, ?_⟩
  rw [unitaryConj_apply_map]
  have hIsmul : I • U (w : H) = U (I • (w : H)) := (map_smul U I (w : H)).symm
  rw [hIsmul, ← map_add, hw, U.apply_symm_apply]

omit [CompleteSpace H] [CompleteSpace H'] in
/-- **Surjectivity of `U A U⁻¹ − i` from surjectivity of `A − i`** — no sign swap (mirror). -/
theorem unitaryConj_sub_I_surjective
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    ∀ φ : H', ∃ ψ : (unitaryConj U A).domain, unitaryConj U A ψ - I • (ψ : H') = φ := by
  intro φ
  obtain ⟨w, hw⟩ := hminus (U.symm φ)
  refine ⟨⟨U (w : H), map_mem_unitaryConj_domain U A w⟩, ?_⟩
  rw [unitaryConj_apply_map]
  have hIsmul : I • U (w : H) = U (I • (w : H)) := (map_smul U I (w : H)).symm
  rw [hIsmul, ← map_sub, hw, U.apply_symm_apply]

variable (U) in
/-- **Unitary conjugation preserves self-adjointness.** If `A` is a (possibly unbounded)
self-adjoint operator on `H` and `U : H ≃ₗᵢ[ℂ] H'` is unitary, then `U A U⁻¹` is self-adjoint on
`H'`. Symmetry, density and both deficiency surjectivities transfer through `U`, so von Neumann's
criterion closes it. -/
theorem unitaryConj_isSelfAdjoint (hA : IsSelfAdjoint A) : IsSelfAdjoint (unitaryConj U A) := by
  have hsym : A.IsFormalAdjoint A := by
    have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  obtain ⟨hplus, hminus⟩ := isSelfAdjoint_to_surjective hA
  exact isSelfAdjoint_of_surjective_addSub (unitaryConj U A)
    (unitaryConj_isFormalAdjoint_self hsym)
    (unitaryConj_dense_domain hA.dense_domain)
    (unitaryConj_add_I_surjective hplus)
    (unitaryConj_sub_I_surjective hminus)

variable (U) in
omit [CompleteSpace H] [CompleteSpace H'] in
/-- **Energy nonnegativity transfers through the conjugation**: `⟪y, (U A U⁻¹) y⟫ = ⟪U⁻¹y, A(U⁻¹y)⟫`
(no conjugation, since `U` is linear), so `0 ≤ Re⟪·, A ·⟫` on `D(A)` gives `0 ≤ Re⟪·, (U A U⁻¹) ·⟫`
on `D(U A U⁻¹)`. This is the form-positivity half of "`T ≥ 0`". -/
theorem unitaryConj_re_inner_nonneg
    (hApos : ∀ x : A.domain, 0 ≤ (⟪(x : H), A x⟫_ℂ).re) :
    ∀ x : (unitaryConj U A).domain, 0 ≤ (⟪(x : H'), unitaryConj U A x⟫_ℂ).re := by
  intro x
  rw [unitaryConj_apply]
  have h1 : ⟪(x : H'), U (A ⟨U.symm (x : H'), x.2⟩)⟫_ℂ
      = ⟪U.symm (x : H'), A ⟨U.symm (x : H'), x.2⟩⟫_ℂ := by
    rw [← U.inner_map_map (U.symm (x : H')) (A ⟨U.symm (x : H'), x.2⟩), U.apply_symm_apply]
  rw [h1]
  exact hApos ⟨U.symm (x : H'), x.2⟩

end UnitaryConj

end Spectra.Operator

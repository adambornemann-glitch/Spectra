/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Spectra.OneParameterUnitaryGroup.Basic
/-!
# Tomita–Takesaki Modular Theory — Foundations

This file seeds the **concrete** (Hilbert-space / von Neumann algebra) side of Tomita–Takesaki
modular theory, complementing the abstract C\*-algebraic side already developed in
`Spectra.KMS` (`Spectra/Modular/KMS/`).

## The theory in one paragraph

Let `M ⊆ B(H)` be a von Neumann algebra with a **cyclic and separating** vector `Ω`. The
antilinear operator `S₀ : M Ω → M Ω`, `S₀ (x Ω) = x⋆ Ω`, is closable; its closure `S` has a polar
decomposition `S = J Δ^{1/2}`, where

* `Δ = S⋆ S` is a positive (generally unbounded) self-adjoint operator, the **modular operator**;
* `J` is an antiunitary involution, the **modular conjugation**.

The two fundamental theorems of the subject are then

* **Tomita's theorem (modular automorphism group):** `Δ^{it} M Δ^{-it} = M` for all `t ∈ ℝ`, so
  conjugation by `Δ^{it}` is a one-parameter automorphism group `σ^ω_t` of `M` — the *modular
  flow*; and
* **The commutation theorem:** `J M J = M'` (the commutant), and `J Ω = Ω`, `Δ Ω = Ω`.

Specialized to the vector state `ω(x) = ⟪Ω, x Ω⟫`, `ω` satisfies the KMS condition at inverse
temperature `β = 1` with respect to `σ^ω` — this is the bridge to `Spectra.KMS`.

## What is proved here vs. bundled

The *full* construction is genuinely research-level and is blocked on infrastructure that is
**absent from Mathlib** (polar decomposition of closed operators; a Borel functional calculus for
unbounded self-adjoint operators that would produce `Δ^{it}` from an unbounded `Δ`; an unbounded
antilinear-operator theory). See `ROADMAP.md` in this directory for the verified inventory and the
tiered path.

Accordingly, following the project idiom (cf. `Spectra.KMS.ModularTheoryData`, which bundles the
abstract modular flow), this file delivers two layers:

1. **Proved, `sorry`-free foundations** — `IsCyclic`, `IsSeparating`, and the foundational
   *duality theorem* relating them through the commutant. These notions are themselves missing
   from Mathlib.
2. **An axiomatized output bundle** — `ModularData M Ω` packages the modular conjugation `J`, the
   modular flow `Δ^{it}` (as a `OneParameterUnitaryGroup`), and the two fundamental theorems as
   *fields* (the defining properties a concrete construction would discharge). It is uninhabited
   until such a construction exists — exactly the status of `ModularTheoryData` on the C\*-side.

## Relation to the abstract C\*-side

`Spectra.KMS.ModularTheoryData A ω` keys the modular flow on a *faithful normal state* and presents
it as an abstract `Dynamics A`. The `ModularData M Ω` here keys it on a *cyclic separating vector*
of a concrete von Neumann algebra and presents `Δ^{it}` as an actual `OneParameterUnitaryGroup H`.
The GNS construction is the bridge: a faithful normal state produces `(M, Ω)` with `Ω` cyclic and
separating (a `medium`-tier roadmap target).

## References

* M. Tomita, "Quasi-standard von Neumann algebras" (1967, unpublished)
* M. Takesaki, "Tomita's theory of modular Hilbert algebras and its applications" (1970)
* M. Takesaki, "Theory of Operator Algebras II", Ch. VI–VIII
* O. Bratteli, D.W. Robinson, "Operator Algebras and Quantum Statistical Mechanics 2"
* A. Connes, "Noncommutative Geometry" (1994)
* S.J. Summers, "Tomita–Takesaki Modular Theory" (arXiv:math-ph/0511034)
-/

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Cyclic and separating vectors

These are the two hypotheses on the pair `(M, Ω)` under which the whole theory runs. Neither is
present in Mathlib for operator algebras, so we define them here. Throughout, an element of a
`VonNeumannAlgebra H` *is* a bounded operator `T : H →L[ℂ] H` together with a membership proof, and
acts on a vector by application `T Ω`. -/

/-- The set `M Ω = {T Ω | T ∈ M}` of vectors obtained by applying operators of `M` to `Ω`. -/
def cyclicSet (M : VonNeumannAlgebra H) (Ω : H) : Set H :=
  (fun T : H →L[ℂ] H => T Ω) '' (M : Set (H →L[ℂ] H))

/-- `Ω` is **cyclic** for `M` if the linear span of `M Ω` is dense in `H` (equivalently, no
nonzero vector is orthogonal to every `T Ω`). Phrased via the span so it feeds
`ContinuousLinearMap.ext_on` directly. -/
def IsCyclic (M : VonNeumannAlgebra H) (Ω : H) : Prop :=
  Dense (Submodule.span ℂ (cyclicSet M Ω) : Set H)

/-- `Ω` is **separating** for `M` if no nonzero operator of `M` annihilates it:
`T ∈ M` and `T Ω = 0` force `T = 0`. -/
def IsSeparating (M : VonNeumannAlgebra H) (Ω : H) : Prop :=
  ∀ T ∈ M, T Ω = 0 → T = 0

/-! ## The cyclic ↔ separating duality

The foundational fact of the subject: cyclicity for `M` and separation for the commutant `M'` are
two sides of the same coin. This is the (fully proved) seed result of the development. -/

/-- **Duality (easy direction): a vector cyclic for `M` is separating for the commutant `M'`.**

If `T' ∈ M'` kills `Ω`, then for every `S ∈ M` it kills `S Ω` as well — because `T'` commutes with
`S`, `T' (S Ω) = (T' S) Ω = (S T') Ω = S (T' Ω) = 0`. So `T'` vanishes on the dense span of `M Ω`,
and being continuous and linear it is `0`. -/
theorem isSeparating_commutant_of_isCyclic {M : VonNeumannAlgebra H} {Ω : H}
    (h : IsCyclic M Ω) : IsSeparating M.commutant Ω := by
  intro T' hT' hT'Ω
  have hzero : Set.EqOn T' (0 : H →L[ℂ] H) (cyclicSet M Ω) := by
    rintro _ ⟨S, hS, rfl⟩
    have hcomm : S * T' = T' * S := VonNeumannAlgebra.mem_commutant_iff.mp hT' S hS
    simp only [ContinuousLinearMap.zero_apply]
    calc T' (S Ω) = (T' * S) Ω := (ContinuousLinearMap.mul_apply T' S Ω).symm
      _ = (S * T') Ω := by rw [hcomm]
      _ = S (T' Ω) := ContinuousLinearMap.mul_apply S T' Ω
      _ = S 0 := by rw [hT'Ω]
      _ = 0 := map_zero S
  exact ContinuousLinearMap.ext_on h hzero

/-- **Duality (corollary): a vector cyclic for the commutant `M'` is separating for `M`.**
Immediate from `isSeparating_commutant_of_isCyclic` applied to `M'`, using `M'' = M`. -/
theorem isSeparating_of_isCyclic_commutant {M : VonNeumannAlgebra H} {Ω : H}
    (h : IsCyclic M.commutant Ω) : IsSeparating M Ω := by
  have h' := isSeparating_commutant_of_isCyclic h
  rwa [VonNeumannAlgebra.commutant_commutant] at h'

/-! ## Conjugation by the modular conjugation

The modular conjugation `J` is **antilinear** (`H ≃ₗᵢ⋆[ℂ] H`), so `J x J⁻¹` for a bounded operator
`x` is *linear* — antilinear ∘ linear ∘ antilinear. We package this conjugation as `jConj`, which
lands in `H →L[ℂ] H`; the type-checking relies on the composition triple
`RingHomCompTriple (starRingEnd ℂ) (starRingEnd ℂ) (RingHom.id ℂ)` (from the involutivity of
complex conjugation), found automatically by instance resolution. -/

/-- Conjugation of a bounded operator `x` by an antiunitary `J`: `jConj J x = J ∘ x ∘ J⁻¹`. The
result is a genuine ℂ-linear bounded operator. -/
def jConj (J : H ≃ₗᵢ⋆[ℂ] H) (x : H →L[ℂ] H) : H →L[ℂ] H :=
  -- `∘L` is pinned to the fully-linear case; the antilinear composition needs the general
  -- `ContinuousLinearMap.comp`, whose `RingHomCompTriple (starRingEnd ℂ) (starRingEnd ℂ) (id)`
  -- (from the involutivity of conjugation) makes antilinear ∘ linear ∘ antilinear land in
  -- `H →L[ℂ] H`.
  (J.toLinearIsometry.toContinuousLinearMap).comp
    (x.comp J.symm.toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace H] in
/-- Pointwise action of `jConj`: `(jConj J x) y = J (x (J⁻¹ y))`. -/
@[simp] lemma jConj_apply (J : H ≃ₗᵢ⋆[ℂ] H) (x : H →L[ℂ] H) (y : H) :
    jConj J x y = J (x (J.symm y)) := by
  simp only [jConj, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]

/-! ## The modular data bundle

`ModularData M Ω` is the *output* of the Tomita–Takesaki construction for a cyclic separating
vector `Ω`: the modular conjugation `J`, the modular flow `Δ^{it}` (as a one-parameter unitary
group), and the two fundamental theorems as fields.

**Honesty.** This bundle is the concrete-side analogue of `Spectra.KMS.ModularTheoryData`. The
operators `Δ` and `J` are *not* constructed here; the fields below are the **defining properties**
that a genuine construction (`S = J Δ^{1/2}`, etc.) would have to discharge. The structure is
therefore uninhabited until that construction exists (see `ROADMAP.md`). Downstream developments may
nevertheless take a `ModularData` as a hypothesis and reason from it. -/

/-- Bundled output of Tomita–Takesaki modular theory for a cyclic separating vector `Ω` of a von
Neumann algebra `M`. See the section docstring for the honesty caveats. -/
structure ModularData (M : VonNeumannAlgebra H) (Ω : H) where
  /-- The modular conjugation `J`: an antiunitary involution of `H`. -/
  J : H ≃ₗᵢ⋆[ℂ] H
  /-- The modular flow `t ↦ Δ^{it}`, a strongly continuous one-parameter unitary group. -/
  modularFlow : Spectra.OneParameterUnitaryGroup H
  /-- `J` is an involution: `J² = 1`. -/
  J_involutive : ∀ x : H, J (J x) = x
  /-- The modular conjugation fixes the vacuum: `J Ω = Ω`. -/
  J_fixes_vacuum : J Ω = Ω
  /-- The modular flow fixes the vacuum: `Δ^{it} Ω = Ω`. -/
  modularFlow_fixes_vacuum : ∀ t : ℝ, modularFlow.U t Ω = Ω
  /-- **Tomita's theorem (into):** `Δ^{it} M Δ^{-it} ⊆ M`. -/
  modularFlow_maps_into :
    ∀ (t : ℝ) (x : H →L[ℂ] H), x ∈ M → modularFlow.U t * x * modularFlow.U (-t) ∈ M
  /-- **Tomita's theorem (onto):** `Δ^{-it} M Δ^{it} ⊆ M`, i.e. `σ_t` is *onto* `M`. Together with
  `modularFlow_maps_into` this gives `Δ^{it} M Δ^{-it} = M`. -/
  modularFlow_maps_onto :
    ∀ (t : ℝ) (x : H →L[ℂ] H), x ∈ M → modularFlow.U (-t) * x * modularFlow.U t ∈ M
  /-- **The commutation theorem:** `J M J = M'`, in membership form
  `x ∈ M ↔ J x J ∈ M'`. -/
  modularConjugation_eq_commutant :
    ∀ x : H →L[ℂ] H, x ∈ M ↔ jConj J x ∈ M.commutant

namespace ModularData

variable {M : VonNeumannAlgebra H} {Ω : H}

/-- The **modular automorphism group** `σ_t(x) = Δ^{it} x Δ^{-it}` maps `M` into itself. -/
lemma modularAutomorphism_mem (D : ModularData M Ω) (t : ℝ) {x : H →L[ℂ] H} (hx : x ∈ M) :
    D.modularFlow.U t * x * D.modularFlow.U (-t) ∈ M :=
  D.modularFlow_maps_into t x hx

/-- The modular conjugation is its own inverse: `J⁻¹ = J` (from `J² = 1`). -/
@[simp] lemma symm_J (D : ModularData M Ω) : D.J.symm = D.J := by
  ext x
  apply D.J.injective
  rw [D.J.apply_symm_apply, D.J_involutive]

/-- The commutation theorem, read for the commutant: `J M' J = M`. Conjugating an element of `M'`
by `J` lands back in `M`. -/
lemma jConj_commutant_mem (D : ModularData M Ω) {x : H →L[ℂ] H}
    (hx : x ∈ M.commutant) : jConj D.J x ∈ M := by
  -- `x ∈ M' = M''`, so by the commutation theorem applied at `M'`... we instead invert directly:
  -- it suffices to exhibit `x` as `jConj J y` for some `y ∈ M`, but the cleanest route is the
  -- equivalence: `jConj J x ∈ M ↔ jConj J (jConj J x) ∈ M'`. Since `jConj J ∘ jConj J = id`
  -- (J involutive), the right side is `x ∈ M'`, which holds.
  rw [D.modularConjugation_eq_commutant]
  have hxx : jConj D.J (jConj D.J x) = x := by
    ext y
    simp only [jConj_apply, symm_J, D.J_involutive]
  rw [hxx]
  exact hx

end ModularData

end Spectra.TomitaTakesaki

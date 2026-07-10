/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularSqrtSelfAdjoint
import Spectra.Modular.Cocycle.PolarIsometry
/-!
# The conjugated modular square root `J Δ^{½} J⁻¹`  (Route B Stage 4 seed / kill-spike KS2)

The Stage-4/5 endgame of the Field-3 build feeds the pair `P = J Δ^{½} J⁻¹`, `Q = Δ^{-½}` to the
positive-square-root uniqueness theorem `posSqrt_unique`, whose inputs are: self-adjointness of `P`
and the *spectral-measure* positivity `∀ ξ, μ^P_ξ((-∞,0)) = 0`.  This file confirms both inputs are
**stateable and provable** for the conjugated operator:

* `conjPMap e A` — the conjugation `e A e⁻¹` of an unbounded operator by an **antiunitary**
  `e : H ≃ₗᵢ⋆[ℂ] H`, with domain `e(D(A))` (realized as `comap e⁻¹`, so membership is
  definitional).  The two conjugations cancel, so `e A e⁻¹` is again `ℂ`-linear.
* `inner_modularConjugation` — the antiunitary inner-product identity `⟪Ju, Jv⟫ = ⟪v, u⟫`
  (from `J = ofConj ∘ W` with `W` unitary and the `Conj`-space inner convention).
* `conjModularSqrt_isSelfAdjoint` — **`J Δ^{½} J⁻¹` is self-adjoint**: symmetry and the
  deficiency-surjectivity of `A ± i` transfer through the conjugation (an antiunitary swaps
  `+i ↔ −i`), so von Neumann's criterion applies.
* `conjModularSqrt_borelMeasure_Iio_zero` — its spectral measure charges no negative reals, for
  **every** vector — the exact `posSqrt_unique` input shape.

The conjugation is *spectrum-preserving* — this construction cannot smuggle the `λ ↦ 1/λ`
inversion; per the Stage-4 plan the inversion enters only through the involution `S̃² = 1`.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel
open Spectra.Conj

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Conjugation of an unbounded operator by an antiunitary -/

section ConjPMap

variable (e : H ≃ₗᵢ⋆[ℂ] H) (A : H →ₗ.[ℂ] H)

/-- **Conjugation `A ↦ e A e⁻¹` of an unbounded operator by an antiunitary** `e : H ≃ₗᵢ⋆[ℂ] H`,
as a `LinearPMap` with domain `e(D(A)) = (e⁻¹)⁻¹(D(A))`.  The two conjugations cancel, so the
result is honestly `ℂ`-linear. -/
noncomputable def conjPMap : H →ₗ.[ℂ] H where
  domain := A.domain.comap (e.symm.toLinearEquiv : H →ₛₗ[starRingEnd ℂ] H)
  toFun :=
    { toFun := fun x => e (A ⟨e.symm (x : H), x.2⟩)
      map_add' := fun x y => by
        have hsub : (⟨e.symm ((x : H) + (y : H)), (x + y).2⟩ : A.domain)
            = ⟨e.symm (x : H), x.2⟩ + ⟨e.symm (y : H), y.2⟩ :=
          Subtype.ext (by simp)
        simp only [Submodule.coe_add]
        rw [hsub, A.map_add, map_add]
      map_smul' := fun c x => by
        have hsub : (⟨e.symm (c • (x : H)), (c • x).2⟩ : A.domain)
            = (starRingEnd ℂ) c • ⟨e.symm (x : H), x.2⟩ :=
          Subtype.ext (by
            change e.symm (c • (x : H)) = (starRingEnd ℂ) c • e.symm (x : H)
            exact map_smulₛₗ e.symm c (x : H))
        simp only [Submodule.coe_smul]
        rw [hsub, A.map_smul, map_smulₛₗ]
        simp }

omit [CompleteSpace H] in
/-- Membership in the conjugated domain is definitional: `x ∈ D(eAe⁻¹) ↔ e⁻¹x ∈ D(A)`. -/
lemma mem_conjPMap_domain_iff {x : H} :
    x ∈ (conjPMap e A).domain ↔ e.symm x ∈ A.domain := Iff.rfl

omit [CompleteSpace H] in
/-- The defining formula `(eAe⁻¹) x = e (A (e⁻¹ x))`. -/
lemma conjPMap_apply (x : (conjPMap e A).domain) :
    conjPMap e A x = e (A ⟨e.symm (x : H), x.2⟩) := rfl

omit [CompleteSpace H] in
/-- `e` maps `D(A)` into `D(eAe⁻¹)`. -/
lemma map_mem_conjPMap_domain (y : A.domain) : e (y : H) ∈ (conjPMap e A).domain := by
  rw [mem_conjPMap_domain_iff, e.symm_apply_apply]
  exact y.2

omit [CompleteSpace H] in
/-- `(eAe⁻¹)(e y) = e (A y)` on `D(A)`. -/
lemma conjPMap_apply_map (y : A.domain) :
    conjPMap e A ⟨e (y : H), map_mem_conjPMap_domain e A y⟩ = e (A y) := by
  rw [conjPMap_apply]
  congr 1
  exact congrArg A (Subtype.ext (e.symm_apply_apply (y : H)))

variable {e A}

omit [CompleteSpace H] in
/-- **Symmetry transfers through the conjugation**: if `A` is symmetric and `e` satisfies the
antiunitary inner identity `⟪eu, ev⟫ = ⟪v, u⟫`, then `eAe⁻¹` is symmetric. -/
theorem conjPMap_isFormalAdjoint_self
    (hinner : ∀ u v : H, ⟪e u, e v⟫_ℂ = ⟪v, u⟫_ℂ)
    (hsym : A.IsFormalAdjoint A) : (conjPMap e A).IsFormalAdjoint (conjPMap e A) := by
  intro x y
  rw [conjPMap_apply, conjPMap_apply]
  calc ⟪e (A ⟨e.symm (x : H), x.2⟩), (y : H)⟫_ℂ
      = ⟪e (A ⟨e.symm (x : H), x.2⟩), e (e.symm (y : H))⟫_ℂ := by rw [e.apply_symm_apply]
    _ = ⟪e.symm (y : H), A ⟨e.symm (x : H), x.2⟩⟫_ℂ := hinner _ _
    _ = ⟪A ⟨e.symm (y : H), y.2⟩, e.symm (x : H)⟫_ℂ :=
        (hsym ⟨e.symm (y : H), y.2⟩ ⟨e.symm (x : H), x.2⟩).symm
    _ = ⟪e (e.symm (x : H)), e (A ⟨e.symm (y : H), y.2⟩)⟫_ℂ := (hinner _ _).symm
    _ = ⟪(x : H), e (A ⟨e.symm (y : H), y.2⟩)⟫_ℂ := by rw [e.apply_symm_apply]

omit [CompleteSpace H] in
/-- **Density transfers through the conjugation**: `D(eAe⁻¹) = (e⁻¹)⁻¹(D(A))` is dense when
`D(A)` is (preimage of a dense set under a homeomorphism). -/
theorem conjPMap_dense_domain (hdense : Dense (A.domain : Set H)) :
    Dense (((conjPMap e A).domain : Submodule ℂ H) : Set H) := by
  have hset : (((conjPMap e A).domain : Submodule ℂ H) : Set H)
      = (e.symm.toHomeomorph) ⁻¹' (A.domain : Set H) := rfl
  rw [hset, dense_iff_closure_eq, ← Homeomorph.preimage_closure, hdense.closure_eq,
    Set.preimage_univ]

omit [CompleteSpace H] in
/-- **Surjectivity of `eAe⁻¹ + i` from surjectivity of `A − i`** (the antiunitary swaps the
deficiency signs). -/
theorem conjPMap_add_I_surjective
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    ∀ φ : H, ∃ ψ : (conjPMap e A).domain, conjPMap e A ψ + I • (ψ : H) = φ := by
  intro φ
  obtain ⟨w, hw⟩ := hminus (e.symm φ)
  refine ⟨⟨e (w : H), map_mem_conjPMap_domain e A w⟩, ?_⟩
  rw [conjPMap_apply_map]
  have hIsmul : I • e (w : H) = e ((-I) • (w : H)) := by
    rw [LinearIsometryEquiv.map_smulₛₗ]
    simp
  rw [hIsmul, ← map_add, show A w + (-I) • (w : H) = A w - I • (w : H) by
    rw [neg_smul, ← sub_eq_add_neg], hw, e.apply_symm_apply]

omit [CompleteSpace H] in
/-- **Surjectivity of `eAe⁻¹ − i` from surjectivity of `A + i`** (mirror). -/
theorem conjPMap_sub_I_surjective
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    ∀ φ : H, ∃ ψ : (conjPMap e A).domain, conjPMap e A ψ - I • (ψ : H) = φ := by
  intro φ
  obtain ⟨w, hw⟩ := hplus (e.symm φ)
  refine ⟨⟨e (w : H), map_mem_conjPMap_domain e A w⟩, ?_⟩
  rw [conjPMap_apply_map]
  have _hIsmul : I • e (w : H) = e ((-I) • (w : H)) := by
    rw [LinearIsometryEquiv.map_smulₛₗ]
    simp
  rw [sub_eq_add_neg, ← neg_smul, show (-I) • e (w : H) = e (I • (w : H)) by
    rw [LinearIsometryEquiv.map_smulₛₗ]; simp, ← map_add, hw, e.apply_symm_apply]

/-- **Von Neumann's criterion for the conjugated operator**: `eAe⁻¹` is self-adjoint whenever `A`
is (symmetry, density, and both deficiency surjectivities transfer). -/
theorem conjPMap_isSelfAdjoint
    (hinner : ∀ u v : H, ⟪e u, e v⟫_ℂ = ⟪v, u⟫_ℂ) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (conjPMap e A) := by
  have hsym : A.IsFormalAdjoint A := by
    have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at h
  obtain ⟨hplus, hminus⟩ := isSelfAdjoint_to_surjective hA
  exact isSelfAdjoint_of_surjective_addSub (conjPMap e A)
    (conjPMap_isFormalAdjoint_self hinner hsym)
    (conjPMap_dense_domain hA.dense_domain)
    (conjPMap_add_I_surjective hminus)
    (conjPMap_sub_I_surjective hplus)

omit [CompleteSpace H] in
/-- **Non-negativity transfers through the conjugation**: `⟪x, (eAe⁻¹)x⟫ = conj ⟪e⁻¹x, A(e⁻¹x)⟫`,
so the real parts agree. -/
theorem conjPMap_re_inner_nonneg
    (hinner : ∀ u v : H, ⟪e u, e v⟫_ℂ = ⟪v, u⟫_ℂ)
    (hApos : ∀ x : A.domain, 0 ≤ (⟪(x : H), A x⟫_ℂ).re) :
    ∀ x : (conjPMap e A).domain, 0 ≤ (⟪(x : H), conjPMap e A x⟫_ℂ).re := by
  intro x
  rw [conjPMap_apply]
  have h1 := hinner (e.symm (x : H)) (A ⟨e.symm (x : H), x.2⟩)
  rw [e.apply_symm_apply] at h1
  rw [h1, ← inner_conj_symm, Complex.conj_re]
  exact hApos ⟨e.symm (x : H), x.2⟩

end ConjPMap

/-! ### The antiunitary inner identity for the modular conjugation -/

variable {M : VonNeumannAlgebra H} {Ω : H}
variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-- **The antiunitary inner identity** `⟪Ju, Jv⟫ = ⟪v, u⟫` for the modular conjugation
`J = ofConj ∘ W`: the unitary `W` preserves inner products, and the `Conj`-space inner product is
the swapped one. -/
theorem inner_modularConjugation (u v : H) :
    ⟪modularConjugation hcyc hsep u, modularConjugation hcyc hsep v⟫_ℂ = ⟪v, u⟫_ℂ := by
  have h1 : ∀ w : H, modularConjugation hcyc hsep w = ofConj (modularW hcyc hsep w) := fun w => by
    rw [modularConjugation, LinearIsometryEquiv.trans_apply, coe_toConjₗᵢ_symm]
  rw [h1 u, h1 v, ← inner_def, LinearIsometryEquiv.inner_map_map]

/-! ### KS2: the `posSqrt_unique` inputs for `J Δ^{½} J⁻¹` -/

/-- **The conjugated modular square root** `J Δ^{½} J⁻¹` — the `P` of the Stage-4/5 endgame pair
`(P, Q) = (JΔ^{½}J⁻¹, Δ^{-½})`. -/
noncomputable def conjModularSqrt : H →ₗ.[ℂ] H :=
  conjPMap (modularConjugation hcyc hsep) (modularSqrt hcyc hsep)

/-- **KS2 (self-adjointness): `J Δ^{½} J⁻¹` is self-adjoint.** -/
theorem conjModularSqrt_isSelfAdjoint : IsSelfAdjoint (conjModularSqrt hcyc hsep) :=
  conjPMap_isSelfAdjoint (inner_modularConjugation hcyc hsep)
    (modularSqrt_isSelfAdjoint hcyc hsep)

/-- The quadratic form of `Δ^{½}` is non-negative (the symbol `√` is non-negative). -/
private theorem modularSqrt_re_inner_nonneg :
    ∀ x : (modularSqrt hcyc hsep).domain, 0 ≤ (⟪(x : H), modularSqrt hcyc hsep x⟫_ℂ).re :=
  fun x =>
    re_inner_self_pmapOfPVM_nonneg (genToGroup (modularOp_isSelfAdjoint hcyc hsep))
      (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC
      (fun s => by rw [Complex.ofReal_re]; exact Real.sqrt_nonneg s)
      ((ProjValMeasure.mem_pmapDomain _).mp x.2)

/-- **KS2 (positivity, in the `posSqrt_unique` input shape): the spectral measure of
`J Δ^{½} J⁻¹` charges no negative reals, for every vector.**  The quadratic form is non-negative
(conjugation preserves it), the domain is dense, and the `∀`-vector support lemma applies. -/
theorem conjModularSqrt_borelMeasure_Iio_zero (ξ : H) :
    borelMeasure (genToGroup (conjModularSqrt_isSelfAdjoint hcyc hsep)) ξ
      (Set.Iio (0 : ℝ)) = 0 := by
  have hgen : generator (genToGroup (conjModularSqrt_isSelfAdjoint hcyc hsep))
      = conjModularSqrt hcyc hsep := generator_genToGroup _
  refine borelMeasure_Iio_zero_eq_zero_of_dense _ ?_ ?_ ξ
  · rw [hgen]
    exact (conjModularSqrt_isSelfAdjoint hcyc hsep).dense_domain
  · rintro ⟨ψ, hψ'⟩
    have hψ : ψ ∈ (conjModularSqrt hcyc hsep).domain := by rw [← hgen]; exact hψ'
    have hval : generator (genToGroup (conjModularSqrt_isSelfAdjoint hcyc hsep)) ⟨ψ, hψ'⟩
        = conjModularSqrt hcyc hsep ⟨ψ, hψ⟩ := (le_of_eq hgen).2 rfl
    rw [hval]
    exact conjPMap_re_inner_nonneg (inner_modularConjugation hcyc hsep)
      (modularSqrt_re_inner_nonneg hcyc hsep) ⟨ψ, hψ⟩

end Spectra.TomitaTakesaki

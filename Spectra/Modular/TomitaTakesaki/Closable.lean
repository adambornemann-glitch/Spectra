/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.TomitaTakesaki.TomitaOperator
import Spectra.Modular.TomitaTakesaki.Duality
/-!
# Closability of the Tomita operator (H2)

The Tomita operator `S̃ = tomitaOp M Ω : H →ₗ.[ℂ] Conj H` is **closable** when `Ω` is cyclic and
separating. The proof: `S̃ ≤ S̃††` and `S̃††` is closed (`adjoint_isClosed`), so `S̃` has a closed
extension. The one nontrivial input is `Dense S̃†.domain`, established by showing every
`toConj (b Ω)` (`b ∈ M'`) lies in `S̃†.domain` — the functional `x ↦ ⟪toConj (b Ω), S̃ x⟫` is the
bounded functional `x ↦ ⟪b⋆ Ω, x⟫` (the **commutation** `a b = b a` of `M` and `M'`) — and that
these vectors are dense in `Conj H` because `M' Ω` is dense (the **duality** E1, transported by the
antiunitary `Conj.toConjₗᵢ`).

See `Spectra/Modular/TomitaTakesaki/ROADMAP.md` (milestone H2).
-/

open scoped InnerProductSpace
open Spectra.Conj

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Commutation identity at the vector level.** For `a ∈ M` and `b ∈ M'`,
`⟪a⋆ Ω, b Ω⟫ = ⟪b⋆ Ω, a Ω⟫` — the Hilbert-space shadow of `a b = b a`. -/
lemma inner_star_comm {M : VonNeumannAlgebra H} {Ω : H} {b : H →L[ℂ] H}
    (hb : b ∈ M.commutant) {a : H →L[ℂ] H} (ha : a ∈ M) :
    ⟪(star a) Ω, b Ω⟫_ℂ = ⟪(star b) Ω, a Ω⟫_ℂ := by
  have hcomm : a * b = b * a := VonNeumannAlgebra.mem_commutant_iff.mp hb a ha
  simp only [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, hcomm]

/-- **The formal-adjoint functional identity.** For `b ∈ M'` and every `x` in the domain of `S̃`,
`⟪toConj (b Ω), S̃ x⟫ = ⟪b⋆ Ω, x⟫`. Proved by induction on the domain `span (M Ω)`. -/
lemma inner_tomitaOp_eq {M : VonNeumannAlgebra H} {Ω : H} (hsep : IsSeparating M Ω)
    {b : H →L[ℂ] H} (hb : b ∈ M.commutant) :
    ∀ (v : H) (hv : v ∈ (tomitaOp M Ω).domain),
      ⟪toConj (b Ω), tomitaOp M Ω ⟨v, hv⟩⟫_ℂ = ⟪(star b) Ω, v⟫_ℂ := by
  have hdom : (tomitaOp M Ω).domain = Submodule.span ℂ (cyclicSet M Ω) :=
    tomitaOp_domain_eq_span M Ω
  suffices h : ∀ v ∈ Submodule.span ℂ (cyclicSet M Ω), ∀ (hv : v ∈ (tomitaOp M Ω).domain),
      ⟪toConj (b Ω), tomitaOp M Ω ⟨v, hv⟩⟫_ℂ = ⟪(star b) Ω, v⟫_ℂ by
    exact fun v hv => h v (hdom ▸ hv) hv
  intro v hspan
  induction hspan using Submodule.span_induction with
  | mem w hw =>
    intro hv
    simp only [cyclicSet, Set.mem_image, SetLike.mem_coe] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    rw [tomitaOp_apply M Ω hsep ha hv, Conj.inner_def, ofConj_toConj, ofConj_toConj]
    exact inner_star_comm hb ha
  | zero =>
    intro hv
    rw [show (⟨(0 : H), hv⟩ : (tomitaOp M Ω).domain) = 0 from rfl, LinearPMap.map_zero,
      inner_zero_right, inner_zero_right]
  | add x y hx hy ihx ihy =>
    intro hv
    have hvx : x ∈ (tomitaOp M Ω).domain := hdom.symm ▸ hx
    have hvy : y ∈ (tomitaOp M Ω).domain := hdom.symm ▸ hy
    rw [show (⟨x + y, hv⟩ : (tomitaOp M Ω).domain) = ⟨x, hvx⟩ + ⟨y, hvy⟩ from rfl,
      LinearPMap.map_add, inner_add_right, inner_add_right, ihx hvx, ihy hvy]
  | smul c x hx ih =>
    intro hv
    have hvx : x ∈ (tomitaOp M Ω).domain := hdom.symm ▸ hx
    rw [show (⟨c • x, hv⟩ : (tomitaOp M Ω).domain) = c • ⟨x, hvx⟩ from rfl, LinearPMap.map_smul,
      inner_smul_right, inner_smul_right, ih hvx]

/-- For `b ∈ M'`, the vector `toConj (b Ω)` lies in the domain of the adjoint `S̃†`. -/
lemma toConj_mem_adjoint_domain {M : VonNeumannAlgebra H} {Ω : H} (hsep : IsSeparating M Ω)
    {b : H →L[ℂ] H} (hb : b ∈ M.commutant) :
    toConj (b Ω) ∈ (tomitaOp M Ω).adjoint.domain := by
  change Continuous ((innerₛₗ ℂ (toConj (b Ω))).comp (tomitaOp M Ω).toFun)
  have hfun : ⇑((innerₛₗ ℂ (toConj (b Ω))).comp (tomitaOp M Ω).toFun)
      = fun x : (tomitaOp M Ω).domain => ⟪(star b) Ω, (x : H)⟫_ℂ := by
    funext x
    exact inner_tomitaOp_eq hsep hb x.1 x.2
  rw [hfun]
  exact ((innerSL ℂ ((star b) Ω)).comp (tomitaOp M Ω).domain.subtypeL).continuous

/-- **The Tomita operator is closable** when `Ω` is cyclic and separating. -/
theorem tomitaOp_isClosable {M : VonNeumannAlgebra H} {Ω : H}
    (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) : (tomitaOp M Ω).IsClosable := by
  have hSdense : Dense ((tomitaOp M Ω).domain : Set H) := tomitaOp_domain_dense M Ω hcyc
  have hcyc' : IsCyclic M.commutant Ω := isCyclic_commutant_of_isSeparating hsep
  -- `toConj '' (M' Ω)` is dense (E1, via the antiunitary) and sits inside `S̃†.domain`
  have hAdense : Dense ((tomitaOp M Ω).adjoint.domain : Set (Conj H)) := by
    have hsub : (toConjₗᵢ H) '' (↑(Submodule.span ℂ (cyclicSet M.commutant Ω)) : Set H)
        ⊆ ((tomitaOp M Ω).adjoint.domain : Set (Conj H)) := by
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe] at hv
      induction hv using Submodule.span_induction with
      | mem w hw =>
        simp only [cyclicSet, Set.mem_image, SetLike.mem_coe] at hw
        obtain ⟨b, hb, rfl⟩ := hw
        exact toConj_mem_adjoint_domain hsep hb
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
      | smul r a _ ha => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ha
    exact Dense.mono hsub
      (((toConjₗᵢ H).toHomeomorph.isDenseEmbedding.dense_image).mpr hcyc')
  rw [LinearPMap.isClosable_iff_exists_closed_extension]
  exact ⟨(tomitaOp M Ω).adjoint.adjoint, LinearPMap.adjoint_isClosed hAdense,
    LinearPMap.IsFormalAdjoint.le_adjoint hAdense (LinearPMap.adjoint_isFormalAdjoint hSdense)⟩

/-- The closure `S = S̄` of the Tomita operator (the genuine modular `S`-operator), available now
that `S̃` is closable. -/
noncomputable def tomitaClosure (M : VonNeumannAlgebra H) (Ω : H) : H →ₗ.[ℂ] Conj H :=
  (tomitaOp M Ω).closure

end Spectra.TomitaTakesaki

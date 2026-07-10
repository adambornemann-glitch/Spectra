/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularSqrt
import Spectra.SpectralTheory.Eigenspace
import Mathlib.Analysis.Normed.Operator.Extend
/-!
# The polar decomposition substrate `S = J Δ^{½}` (R3)

For a cyclic–separating vector `Ω` of a von Neumann algebra `M`, the Tomita operator
`S = tomitaClosure M Ω` and the modular operator `Δ = S⋆S = modularOp M Ω` enter the polar
decomposition `S = J Δ^{½}`.  The modular conjugation `J` is read off from the partial isometry `W`
of `S`, built (R3) as `W = extendOfIsometry (Δ^{½}x ↦ S x)` and then `J = ofConj ∘ W`.

`LinearEquiv.extendOfIsometry` needs, besides the isometry `‖Δ^{½}x‖ = ‖S x‖`
(`norm_modularSqrt_eq_norm_tomita`, R2), the **two density inputs**: the source `Δ^{½}(D(Δ))` and
the target `S(D(Δ))` must be dense.  This file establishes the part of that substrate that is
available without the unbounded-calculus self-adjointness of `Δ^{½}`:

* `tomitaClosure_injective` — **`S` is injective** (`ker S = 0`), from `S⋆(toConj bΩ) = b⋆Ω`
  (`b ∈ M'`) and density of `M' Ω`;
* `modularOp_injective` — **`Δ` is injective** (`ker Δ = 0`), via `Re⟪Δx,x⟫ = ‖Sx‖²`;
* `tomitaClosure_range_dense` — **`range S` is dense** in `Conj H`, from `S(MΩ) = toConj(MΩ)`;
* `denseRange_tomitaOnModularDomain` — **`S(D(Δ))` is dense**, i.e. `D(Δ)` is a core for `S`
  (the target density input to `W`), from the surjectivity of `1 + Δ`
  (`one_add_modularOp_surjective`).

The remaining source density `Δ^{½}(D(Δ))` dense (hence `W`, then `J`) is gated on
`Δ^{½}` being self-adjoint and the product law `(Δ^{½})² = Δ` — the R2 calculus completion.

See `Spectra/Modular/TomitaTakesaki/ROADMAP.md` (R3) and the vault canvas *Modular Operator
Calculus*.
-/

open scoped InnerProductSpace
open Spectra.Conj

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ## The adjoint of the closure and `S ≤ S⋆⋆` -/

/-- **Density of `S†`'s domain.**  Every `toConj (b Ω)` with `b ∈ M'` lies in `D(S†)`
(`toConj_mem_adjoint_domain`); these are dense because `M' Ω` is dense (the duality `E1`,
transported by the antiunitary `toConjₗᵢ`).  (Extracted from the closability proof.) -/
theorem tomitaOp_adjoint_domain_dense (hsep : IsSeparating M Ω) :
    Dense ((tomitaOp M Ω).adjoint.domain : Set (Conj H)) := by
  have hcyc' : IsCyclic M.commutant Ω := isCyclic_commutant_of_isSeparating hsep
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

/-- **`S ≤ S⋆⋆`.**  The closed Tomita operator is contained in the double adjoint: `S₀ ≤ S₀⋆⋆`
(`IsFormalAdjoint.le_adjoint`), `S₀⋆⋆` is closed (`adjoint_isClosed`), and `S = S₀.closure` is the
smallest closed extension. -/
theorem tomitaClosure_le_adjoint_adjoint (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    tomitaClosure M Ω ≤ (tomitaOp M Ω).adjoint.adjoint := by
  have hSdense : Dense ((tomitaOp M Ω).domain : Set H) := tomitaOp_domain_dense M Ω hcyc
  have hAdense : Dense ((tomitaOp M Ω).adjoint.domain : Set (Conj H)) :=
    tomitaOp_adjoint_domain_dense hsep
  have h_le : tomitaOp M Ω ≤ (tomitaOp M Ω).adjoint.adjoint :=
    (LinearPMap.adjoint_isFormalAdjoint hSdense).le_adjoint hAdense
  have h_closed : ((tomitaOp M Ω).adjoint).adjoint.IsClosed := LinearPMap.adjoint_isClosed hAdense
  have hmono := h_closed.isClosable.closure_mono h_le
  have hce : ((tomitaOp M Ω).adjoint).adjoint.closure = ((tomitaOp M Ω).adjoint).adjoint := by
    apply LinearPMap.eq_of_eq_graph
    rw [← h_closed.isClosable.graph_closure_eq_closure_graph]
    exact (h_closed :
      IsClosed (↑(((tomitaOp M Ω).adjoint).adjoint.graph) : Set (H × Conj H))
      ).submodule_topologicalClosure_eq
  rwa [hce] at hmono

/-- The value of `S†` on `M' Ω`: `S†(toConj (b Ω)) = b⋆ Ω` for `b ∈ M'`.  From the functional
identity `⟪toConj (b Ω), S₀ x⟫ = ⟪b⋆ Ω, x⟫` (`inner_tomitaOp_eq`) and `adjoint_apply_eq`. -/
theorem tomitaAdjoint_apply_commutant (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    {b : H →L[ℂ] H} (hb : b ∈ M.commutant) :
    (tomitaOp M Ω).adjoint ⟨toConj (b Ω), toConj_mem_adjoint_domain hsep hb⟩ = (star b) Ω :=
  LinearPMap.adjoint_apply_eq (tomitaOp_domain_dense M Ω hcyc)
    ⟨toConj (b Ω), toConj_mem_adjoint_domain hsep hb⟩
    (fun x => (inner_tomitaOp_eq hsep hb (x : H) x.2).symm)

/-! ## R3 `inj`: `S` and `Δ` are injective -/

/-- **The Tomita operator `S` is injective** (`ker S = 0`).  If `S x = 0` then for every `b ∈ M'`,
`⟪x, b⋆ Ω⟫ = ⟪S†(toConj bΩ)†…⟫ = ⟪S x, toConj bΩ⟫⋆ = 0` (formal adjoint of `S ≤ S₀⋆⋆` with
`S₀⋆(toConj bΩ) = b⋆Ω`); since `M' Ω` is dense, `x = 0`. -/
theorem tomitaClosure_injective (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (tomitaClosure M Ω).domain) (hx0 : tomitaClosure M Ω x = 0) : (x : H) = 0 := by
  have hAdense : Dense ((tomitaOp M Ω).adjoint.domain : Set (Conj H)) :=
    tomitaOp_adjoint_domain_dense hsep
  have hxle : tomitaClosure M Ω ≤ (tomitaOp M Ω).adjoint.adjoint :=
    tomitaClosure_le_adjoint_adjoint hcyc hsep
  have hxmem : (x : H) ∈ ((tomitaOp M Ω).adjoint).adjoint.domain := hxle.1 x.2
  have hxval : ((tomitaOp M Ω).adjoint).adjoint ⟨(x : H), hxmem⟩ = tomitaClosure M Ω x :=
    (hxle.2 rfl).symm
  have hFA := LinearPMap.adjoint_isFormalAdjoint (T := (tomitaOp M Ω).adjoint) hAdense
  have hperp : ∀ b ∈ M.commutant, ⟪(x : H), (star b) Ω⟫_ℂ = 0 := by
    intro b hb
    have hη : toConj (b Ω) ∈ (tomitaOp M Ω).adjoint.domain := toConj_mem_adjoint_domain hsep hb
    have hval : (tomitaOp M Ω).adjoint ⟨toConj (b Ω), hη⟩ = (star b) Ω :=
      tomitaAdjoint_apply_commutant hcyc hsep hb
    have key := hFA ⟨(x : H), hxmem⟩ ⟨toConj (b Ω), hη⟩
    rw [hxval, hx0, hval, inner_zero_left] at key
    exact key.symm
  -- `x ⊥ span (cyclicSet M' Ω)`, which is dense, so `x = 0`.
  have hcyc' : IsCyclic M.commutant Ω := isCyclic_commutant_of_isSeparating hsep
  have hxperp_set : ∀ v ∈ cyclicSet M.commutant Ω, ⟪v, (x : H)⟫_ℂ = 0 := by
    rintro _ ⟨c, hc, rfl⟩
    have hsc : (star c) ∈ M.commutant := star_mem hc
    have h0 := hperp (star c) hsc
    rw [star_star] at h0
    rw [← inner_conj_symm, h0, map_zero]
  have hxmem_perp : (x : H) ∈ (Submodule.span ℂ (cyclicSet M.commutant Ω))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem w hw => exact hxperp_set w hw
    | zero => simp
    | add a c _ _ ha hc => rw [inner_add_left, ha, hc, add_zero]
    | smul r a _ ha => rw [inner_smul_left, ha, mul_zero]
  have hbot : (Submodule.span ℂ (cyclicSet M.commutant Ω))ᗮ = ⊥ :=
    Submodule.topologicalClosure_eq_top_iff.mp
      (Submodule.dense_iff_topologicalClosure_eq_top.mp hcyc')
  rw [hbot, Submodule.mem_bot] at hxmem_perp
  exact hxmem_perp

/-- `D(Δ) ⊆ D(S)`: the modular domain is contained in the domain of `S`. -/
theorem modularOp_domain_le_tomita :
    (modularOp M Ω).domain ≤ (tomitaClosure M Ω).domain := by
  intro x hx
  obtain ⟨⟨hxS, _⟩, _⟩ := hx
  exact hxS

/-- **The modular operator `Δ` is injective** (`ker Δ = 0`).  `Δ x = 0 ⟹ Re⟪Δx,x⟫ = ‖Sx‖² = 0
⟹ S x = 0 ⟹ x = 0` (injectivity of `S`). -/
theorem modularOp_injective (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (modularOp M Ω).domain) (hx0 : modularOp M Ω x = 0) : (x : H) = 0 := by
  have hxS : (x : H) ∈ (tomitaClosure M Ω).domain := modularOp_domain_le_tomita x.2
  have hform : (⟪modularOp M Ω x, (x : H)⟫_ℂ).re = ‖tomitaClosure M Ω ⟨(x : H), hxS⟩‖ ^ 2 :=
    modularOp_re_inner_eq_normSq hcyc x hxS
  rw [hx0, inner_zero_left] at hform
  have hsq : ‖tomitaClosure M Ω ⟨(x : H), hxS⟩‖ ^ 2 = 0 := by simpa using hform.symm
  have hSx0 : tomitaClosure M Ω ⟨(x : H), hxS⟩ = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq)
  exact tomitaClosure_injective hcyc hsep ⟨(x : H), hxS⟩ hSx0

/-! ## R3 `denserange` (easy half): `range S` is dense -/

/-- **`range S` is dense in `Conj H`.**  `S(a Ω) = toConj((a⋆) Ω)`, so `range S ⊇ toConj(M Ω)`
(`a ↦ a⋆` bijects `M`); the latter spans a dense subspace (cyclicity of `Ω`, transported by the
antiunitary `toConjₗᵢ`). -/
theorem tomitaClosure_range_dense (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    Dense ((LinearMap.range (tomitaClosure M Ω).toFun : Submodule ℂ (Conj H)) : Set (Conj H)) := by
  -- generators: `toConj (a Ω) ∈ range S` for `a ∈ M`.
  have hgen : (toConjₗᵢ H) '' (cyclicSet M Ω)
      ⊆ (LinearMap.range (tomitaClosure M Ω).toFun : Set (Conj H)) := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [cyclicSet, Set.mem_image, SetLike.mem_coe] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    have hstar : (star a) ∈ M := star_mem ha
    have hzdom_op : (star a) Ω ∈ (tomitaOp M Ω).domain := by
      rw [tomitaOp_domain_eq_span]
      exact Submodule.subset_span ⟨star a, hstar, rfl⟩
    have hzdom : (star a) Ω ∈ (tomitaClosure M Ω).domain :=
      (LinearPMap.le_closure (tomitaOp M Ω)).1 hzdom_op
    refine ⟨⟨(star a) Ω, hzdom⟩, ?_⟩
    change tomitaClosure M Ω ⟨(star a) Ω, hzdom⟩ = (toConjₗᵢ H) (a Ω)
    have hagree : tomitaOp M Ω ⟨(star a) Ω, hzdom_op⟩ = tomitaClosure M Ω ⟨(star a) Ω, hzdom⟩ :=
      (LinearPMap.le_closure (tomitaOp M Ω)).2 rfl
    rw [coe_toConjₗᵢ, ← hagree, tomitaOp_apply M Ω hsep hstar hzdom_op, star_star]
  -- the dense subspace `toConj '' span (cyclicSet M Ω)` sits inside `range S`.
  have hdense_img : Dense ((toConjₗᵢ H) '' (↑(Submodule.span ℂ (cyclicSet M Ω)) : Set H)) :=
    ((toConjₗᵢ H).toHomeomorph.isDenseEmbedding.dense_image).mpr hcyc
  refine hdense_img.mono ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe] at hv
  rw [SetLike.mem_coe]
  induction hv using Submodule.span_induction with
  | mem w hw => exact hgen ⟨w, hw, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a c _ _ ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
  | smul r a _ ha => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ha

/-! ## R3 `denserange` (hard half): `S(D(Δ))` is dense — `D(Δ)` is a core for `S` -/

/-- The linear map `D(Δ) → Conj H`, `x ↦ S x`. -/
noncomputable def tomitaOnModularDomain (M : VonNeumannAlgebra H) (Ω : H) :
    (modularOp M Ω).domain →ₗ[ℂ] Conj H :=
  (tomitaClosure M Ω).toFun.comp (Submodule.inclusion modularOp_domain_le_tomita)

/-- Unfold `tomitaOnModularDomain`: it is just `S` evaluated on the inclusion of `D(Δ)` into
`D(S)`. -/
theorem tomitaOnModularDomain_apply (x : (modularOp M Ω).domain) :
    tomitaOnModularDomain M Ω x
      = tomitaClosure M Ω ⟨(x : H), modularOp_domain_le_tomita x.2⟩ := rfl

/-- The pairing `D(Δ) → WithLp 2 (H × Conj H)`, `x ↦ (x, S x)`, whose range is the restricted
graph. -/
noncomputable def modularPairing (M : VonNeumannAlgebra H) (Ω : H) :
    (modularOp M Ω).domain →ₗ[ℂ] WithLp 2 (H × Conj H) :=
  (WithLp.linearEquiv 2 ℂ (H × Conj H)).symm.toLinearMap.comp
    (((modularOp M Ω).domain.subtype).prod (tomitaOnModularDomain M Ω))

/-- Unfold `modularPairing`: `x ↦ toLp ((x:H), S x)`. -/
theorem modularPairing_apply (x : (modularOp M Ω).domain) :
    modularPairing M Ω x = WithLp.toLp 2 ((x : H), tomitaOnModularDomain M Ω x) := rfl

/-- **The restricted graph** `Γ(S ↾ D(Δ))` in the L² space, as the range of `modularPairing`. -/
noncomputable def modularGraphL2 (M : VonNeumannAlgebra H) (Ω : H) :
    Submodule ℂ (WithLp 2 (H × Conj H)) :=
  LinearMap.range (modularPairing M Ω)

/-- Step B — `modularGraphL2 ≤ graphL2`: every restricted-graph point `(x, S x)` (`x ∈ D(Δ)`) lies
in the full graph `Γ(S)`. -/
theorem modularGraphL2_le_graphL2 : modularGraphL2 M Ω ≤ graphL2 M Ω := by
  rintro _ ⟨x, rfl⟩
  rw [modularPairing_apply, mem_graphL2_iff, WithLp.ofLp_toLp, tomitaOnModularDomain_apply]
  exact (tomitaClosure M Ω).mem_graph ⟨(x : H), modularOp_domain_le_tomita x.2⟩

/-- Step C — **the key lemma.**  If `q ∈ Γ(S)` and `q ⊥ Γ(S ↾ D(Δ))`, then `q = 0`.

Membership in `Γ(S)` exposes `q = (η, S η)` with `η ∈ D(S)`; orthogonality against every
restricted-graph generator `(x, S x)` gives `⟪x, η⟫ + ⟪S x, S η⟫ = 0`, and the adjoint relation
`Δ x = S⋆(S x)` turns the second term into `⟪Δ x, η⟫`, so `⟪(1 + Δ) x, η⟫ = 0` for all
`x ∈ D(Δ)`.  Surjectivity of `1 + Δ` then forces `η ⊥ H`, hence `η = 0`, hence `q = 0`. -/
theorem eq_zero_of_mem_graphL2_orthogonal (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    {q : WithLp 2 (H × Conj H)} (hqΓ : q ∈ graphL2 M Ω) (hqperp : q ∈ (modularGraphL2 M Ω)ᗮ) :
    q = 0 := by
  have hdense : Dense ((tomitaClosure M Ω).domain : Set H) := tomitaClosure_domain_dense hcyc
  -- `q ∈ Γ(S)`: expose `η ∈ D(S)` with `(ofLp q).1 = η`, `(ofLp q).2 = S η`.
  rw [mem_graphL2_iff, (tomitaClosure M Ω).mem_graph_iff] at hqΓ
  obtain ⟨η, hη1, hη2⟩ := hqΓ
  -- The formal-adjoint relation for `S⋆`.
  have hFA := LinearPMap.adjoint_isFormalAdjoint (T := tomitaClosure M Ω) hdense
  -- For every `x ∈ D(Δ)`, `⟪(1 + Δ) x, η⟫ = 0`.
  have hkey : ∀ x : (modularOp M Ω).domain,
      ⟪modularOp M Ω x + (x : H), (η : H)⟫_ℂ = 0 := by
    intro x
    obtain ⟨⟨hxS, hSx⟩, _⟩ := x.2
    -- Orthogonality of `q` against the generator `(x, S x)`.
    have hgen : modularPairing M Ω x ∈ modularGraphL2 M Ω := LinearMap.mem_range_self _ x
    have hperp := (Submodule.mem_orthogonal _ q).1 hqperp _ hgen
    rw [modularPairing_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp, ← hη1, ← hη2,
      tomitaOnModularDomain_apply] at hperp
    -- `hperp : ⟪x, η⟫ + ⟪S x, S η⟫ = 0`.
    -- Transform the second term using `Δ x = S⋆ (S x)` and the formal-adjoint relation.
    have hΔ : modularOp M Ω x = (tomitaClosure M Ω).adjoint
        ⟨tomitaClosure M Ω ⟨(x : H), hxS⟩, hSx⟩ := modularOp_apply x hxS hSx
    have hadj := hFA ⟨tomitaClosure M Ω ⟨(x : H), hxS⟩, hSx⟩ ⟨(η : H), hη1 ▸ η.2⟩
    -- `hadj : ⟪S⋆ (S x), η⟫ = ⟪S x, S η⟫`.
    have hηcoe : tomitaClosure M Ω ⟨(η : H), hη1 ▸ η.2⟩ = tomitaClosure M Ω η := by
      congr 1
    rw [hηcoe] at hadj
    -- Replace `⟪S x, S η⟫` by `⟪Δ x, η⟫` in `hperp`.
    rw [← hadj, ← hΔ] at hperp
    -- Now `hperp : ⟪x, η⟫ + ⟪Δ x, η⟫ = 0`.
    rw [inner_add_left, add_comm]
    exact hperp
  -- Surjectivity of `1 + Δ` gives `η ⊥ H`, hence `η = 0`.
  have hηperp : ∀ h : H, ⟪h, (η : H)⟫_ℂ = 0 := by
    intro h
    obtain ⟨x, hx⟩ := one_add_modularOp_surjective hcyc hsep h
    rw [← hx]; exact hkey x
  have hηzero : (η : H) = 0 := by
    have := hηperp (η : H)
    exact inner_self_eq_zero.mp this
  -- Conclude `ofLp q = 0`, hence `q = 0`.
  have hofLp : WithLp.ofLp q = 0 := by
    apply Prod.ext
    · simp only [← hη1, hηzero, Prod.fst_zero]
    · have : tomitaClosure M Ω η = 0 := by
        rw [show η = 0 from Subtype.ext hηzero, LinearPMap.map_zero]
      simp only [← hη2, this, Prod.snd_zero]
  exact WithLp.ofLp_injective 2 (by rw [hofLp]; rfl)

/-- Step D — **`Γ(S) = closure (Γ(S ↾ D(Δ)))`.**  The closure is the smallest closed extension, so
`⊆`; for `⊇`, orthogonally decompose any `q ∈ Γ(S)` along the closed `K := closure(...)`:
the complementary part `k'` lies in `Γ(S) ∩ K ᗮ ⊆ Γ(S) ∩ (Γ(S ↾ D(Δ)))ᗮ`, so `k' = 0` by Step C,
forcing `q = k ∈ K`. -/
theorem graphL2_eq_topologicalClosure_modularGraphL2 (hcyc : IsCyclic M Ω)
    (hsep : IsSeparating M Ω) :
    graphL2 M Ω = (modularGraphL2 M Ω).topologicalClosure := by
  set K := (modularGraphL2 M Ω).topologicalClosure with _hKdef
  have hKle : K ≤ graphL2 M Ω :=
    Submodule.topologicalClosure_minimal _ modularGraphL2_le_graphL2 (graphL2_isClosed hcyc hsep)
  refine le_antisymm ?_ hKle
  -- `Γ(S) ≤ K`.
  have hKclosed : IsClosed (K : Set (WithLp 2 (H × Conj H))) :=
    Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace K := hKclosed.isComplete.completeSpace_coe
  haveI : K.HasOrthogonalProjection := inferInstance
  intro q hq
  obtain ⟨k, hk, k', hk', hdecomp⟩ := K.exists_add_mem_mem_orthogonal q
  -- `k ∈ K ≤ Γ(S)`, so `k' = q - k ∈ Γ(S)`.
  have hkΓ : k ∈ graphL2 M Ω := hKle hk
  have hk'Γ : k' ∈ graphL2 M Ω := by
    have : k' = q - k := by rw [hdecomp]; abel
    rw [this]; exact (graphL2 M Ω).sub_mem hq hkΓ
  -- `k' ∈ Kᗮ ≤ (modularGraphL2)ᗮ`.
  have hk'perp : k' ∈ (modularGraphL2 M Ω)ᗮ :=
    Submodule.orthogonal_le (Submodule.le_topologicalClosure _) hk'
  -- Step C: `k' = 0`, so `q = k ∈ K`.
  have hk'0 : k' = 0 := eq_zero_of_mem_graphL2_orthogonal hcyc hsep hk'Γ hk'perp
  rw [hdecomp, hk'0, add_zero]
  exact hk

/-- **`S(D(Δ))` is dense in `Conj H`** — `D(Δ)` is a core for `S`. -/
theorem denseRange_tomitaOnModularDomain (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    DenseRange (tomitaOnModularDomain M Ω) := by
  -- The projection onto the second coordinate, continuous.
  set π₂ : WithLp 2 (H × Conj H) → Conj H := fun w => (WithLp.ofLp w).2 with hπ₂def
  have hπ₂cont : Continuous π₂ :=
    continuous_snd.comp (WithLp.prod_continuous_ofLp 2 H (Conj H))
  -- `π₂ '' ↑modularGraphL2 = range (tomitaOnModularDomain)`.
  have himg : π₂ '' (modularGraphL2 M Ω : Set (WithLp 2 (H × Conj H)))
      = Set.range (tomitaOnModularDomain M Ω) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, by simp only [hπ₂def, modularPairing_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨modularPairing M Ω x, LinearMap.mem_range_self _ x,
        by simp only [hπ₂def, modularPairing_apply]⟩
  -- The dense set `↑(range S.toFun)` sits inside `closure (range (tomitaOnModularDomain))`.
  have hsub : (LinearMap.range (tomitaClosure M Ω).toFun : Set (Conj H))
      ⊆ closure (Set.range (tomitaOnModularDomain M Ω)) := by
    rintro _ ⟨y, rfl⟩
    -- `q := toLp ((y:H), S y) ∈ Γ(S)`.
    have hqΓ : WithLp.toLp 2 ((y : H), tomitaClosure M Ω y) ∈ graphL2 M Ω := by
      rw [mem_graphL2_iff, WithLp.ofLp_toLp]
      exact (tomitaClosure M Ω).mem_graph y
    -- By Step D, `q ∈ ↑K = closure (↑modularGraphL2)`.
    have hqK : WithLp.toLp 2 ((y : H), tomitaClosure M Ω y)
        ∈ ((modularGraphL2 M Ω).topologicalClosure : Set (WithLp 2 (H × Conj H))) := by
      rw [← graphL2_eq_topologicalClosure_modularGraphL2 hcyc hsep]; exact hqΓ
    rw [Submodule.topologicalClosure_coe] at hqK
    -- `π₂ q ∈ closure (π₂ '' ↑modularGraphL2) = closure (range (tomitaOnModularDomain))`.
    have hmem := image_closure_subset_closure_image hπ₂cont (Set.mem_image_of_mem π₂ hqK)
    rw [himg] at hmem
    have hval : π₂ (WithLp.toLp 2 ((y : H), tomitaClosure M Ω y)) = tomitaClosure M Ω y := by
      simp only [hπ₂def]
    rw [hval] at hmem
    -- `tomitaClosure M Ω y = (tomitaClosure M Ω).toFun y` definitionally.
    exact hmem
  -- `range S` dense and `range S ⊆ closure (range e₂)`, so `closure (range e₂)` is dense,
  -- hence `range e₂` is dense.
  have hSdense := tomitaClosure_range_dense hcyc hsep
  rw [DenseRange]
  exact (hSdense.mono hsub).of_closure

/-! ## R3 `denserange` (source half): `Δ^{½}(D(Δ))` is dense

The remaining density input to the polar isometry `W = extendOfIsometry (Δ^{½}x ↦ S x)`: the source
`Δ^{½}(D(Δ))` is dense in `H`.  Equivalently, `D(Δ)` is a core for `Δ^{½}` in the spectral sense.

The proof works with the spectral data of the (non-negative, self-adjoint, injective) modular
operator `Δ = generator U`, `U := genToGroup (modularOp_isSelfAdjoint hcyc hsep)`.  Fixing a vector
`y ⊥ Δ^{½}(D(Δ))`, the cut-off vectors `x_n = E([0,n]) y` lie in `D(Δ)` and the pairing
`⟪y, Δ^{½} x_n⟫ = ∫_{[0,n]} √s dμ_y` vanishes; non-negativity of `√` forces `μ_y((0,∞)) = 0`,
positivity of `Δ` forces `μ_y((-∞,0)) = 0`, and injectivity of `Δ` forces `μ_y({0}) = 0`, so
`‖y‖² = μ_y(ℝ) = 0`.
-/

open Complex MeasureTheory Filter Topology
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel

/-- The unitary group of the modular operator `Δ = modularOp M Ω`. -/
private noncomputable abbrev modularGroup (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    OneParameterUnitaryGroup (H := H) :=
  genToGroup (modularOp_isSelfAdjoint hcyc hsep)

/-- `generator (modularGroup …) = modularOp M Ω` (Stone). -/
private theorem generator_modularGroup (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    generator (modularGroup hcyc hsep) = modularOp M Ω :=
  generator_genToGroup _

/-- `D(Δ) ⊆ D(Δ^{½})`: the modular domain sits in the `L²` domain of the `√` calculus.  Each
`x ∈ D(Δ) = D(generator U)` lies in the natural domain of `Δ^{½} = pmapOfPVM U √` since
`∫ |√·|² dμ_x < ∞` (`sqrt_integrable_of_mem_generator`). -/
theorem modularOp_domain_le_modularSqrt_domain (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    (modularOp M Ω).domain ≤ (modularSqrt hcyc hsep).domain := by
  intro x hx
  have hxgen : x ∈ (generator (modularGroup hcyc hsep)).domain := by
    rw [generator_modularGroup hcyc hsep]; exact hx
  exact (ProjValMeasure.mem_pmapDomain _).mpr
    (sqrt_integrable_of_mem_generator (modularGroup hcyc hsep) ⟨x, hxgen⟩)

/-- **The modular square root restricted to `D(Δ)`** as a linear map `D(Δ) → H`, `x ↦ Δ^{½} x`. -/
noncomputable def modularSqrtOnModularDomain (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    (modularOp M Ω).domain →ₗ[ℂ] H :=
  (modularSqrt hcyc hsep).toFun.comp
    (Submodule.inclusion (modularOp_domain_le_modularSqrt_domain hcyc hsep))

/-- Unfold `modularSqrtOnModularDomain`: it is `Δ^{½}` evaluated on the inclusion of `D(Δ)` into
`D(Δ^{½})`. -/
theorem modularSqrtOnModularDomain_apply (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (modularOp M Ω).domain) :
    modularSqrtOnModularDomain hcyc hsep x
      = modularSqrt hcyc hsep
          ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩ := rfl

/-- **Non-negativity of the modular generator**, in the `hpos` shape demanded by the spectral
positivity lemmas: `0 ≤ Re ⟪z, (generator U) z⟫` for `z ∈ D(generator U)`.  Transported from
`modularOp_nonneg` (`Δ x = S⋆(Sx)`, so `Re⟪Δx,x⟫ = ‖Sx‖² ≥ 0`) via Stone and `inner_conj_symm`. -/
private theorem modularGroup_hpos (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    ∀ z : (generator (modularGroup hcyc hsep)).domain,
      0 ≤ (⟪(z : H), generator (modularGroup hcyc hsep) z⟫_ℂ).re := by
  rintro ⟨ψ, hψ'⟩
  have hgen : generator (modularGroup hcyc hsep) = modularOp M Ω :=
    generator_modularGroup hcyc hsep
  have hψ : ψ ∈ (modularOp M Ω).domain := by rw [← hgen]; exact hψ'
  have hval : generator (modularGroup hcyc hsep) ⟨ψ, hψ'⟩ = modularOp M Ω ⟨ψ, hψ⟩ :=
    (le_of_eq hgen).2 rfl
  rw [hval, ← inner_conj_symm, Complex.conj_re]
  exact modularOp_nonneg hcyc ⟨ψ, hψ⟩

/-- **Step 1: the modular spectral measure charges no negative reals**, for EVERY `y`:
`μ_y((-∞,0)) = 0`.  On the dense domain `D(Δ)` we have `‖E((-∞,0)) z‖² = μ_z((-∞,0)) = 0`
(`borelMeasure_Iio_zero_eq_zero`), so the continuous operator `E((-∞,0))` vanishes on a dense set,
hence is `0`; then `μ_y((-∞,0)) = ‖E((-∞,0)) y‖² = 0`. -/
theorem borelMeasure_modular_Iio_zero (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (y : H) :
    borelMeasure (modularGroup hcyc hsep) y (Set.Iio (0 : ℝ)) = 0 := by
  set U := modularGroup hcyc hsep with _hU
  -- `E((-∞,0))` vanishes on the dense domain `D(generator U) = D(Δ)`.
  have hdense : Dense ((generator U).domain : Set H) := by
    rw [generator_modularGroup hcyc hsep]
    exact (modularOp_isSelfAdjoint hcyc hsep).dense_domain
  have hdense' : Dense (Submodule.span ℂ ((generator U).domain : Set H) : Set H) := by
    rwa [Submodule.span_eq]
  have hzero : Set.EqOn (spectralProjection U (Set.Iio 0) measurableSet_Iio) 0
      ((generator U).domain : Set H) := by
    intro z hz
    have hmem : z ∈ (generator U).domain := hz
    have hμ : borelMeasure U z (Set.Iio 0) = 0 :=
      borelMeasure_Iio_zero_eq_zero U (modularGroup_hpos hcyc hsep) ⟨z, hmem⟩
    change spectralProjection U (Set.Iio 0) measurableSet_Iio z = 0
    rw [← norm_eq_zero, ← sq_eq_zero_iff,
      norm_sq_spectralProjection U (Set.Iio 0) measurableSet_Iio z, hμ]
    simp
  -- a continuous operator zero on a dense set is zero.
  have hE0 : spectralProjection U (Set.Iio 0) measurableSet_Iio = 0 :=
    ContinuousLinearMap.ext_on hdense' hzero
  -- hence `μ_y((-∞,0)) = ‖E((-∞,0)) y‖² = 0`.
  have hnorm : ((borelMeasure U y (Set.Iio 0)).toReal) = 0 := by
    rw [← norm_sq_spectralProjection U (Set.Iio 0) measurableSet_Iio y, hE0]
    simp
  haveI : IsFiniteMeasure (borelMeasure U y) := borelMeasure_isFiniteMeasure U y
  exact (ENNReal.toReal_eq_zero_iff _).mp hnorm |>.resolve_right (measure_ne_top _ _)

/-! ## Step 2 — the cut-off vectors `x_n = E([0,n]) y` and the pairing on cut-offs -/

/-- The cut-off vector `x_n = E([0,n]) y` lies in `D(Δ)` (`spectralProjection_mem_generatorDomain`
on the bounded set `[0,n]`, then Stone-transport `D(generator U) = D(Δ)`). -/
theorem modular_cutoff_mem_domain (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (y : H) (n : ℕ) :
    spectralProjection (modularGroup hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc y
      ∈ (modularOp M Ω).domain := by
  have hmem : spectralProjection (modularGroup hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc y
      ∈ (generator (modularGroup hcyc hsep)).domain :=
    spectralProjection_mem_generatorDomain (modularGroup hcyc hsep) measurableSet_Icc (R := n)
      (fun s hs => by
        rw [abs_of_nonneg hs.1]; exact hs.2) y
  rwa [generator_modularGroup hcyc hsep] at hmem

/-- The square-root symbol restricted to `[0,n]`, `g_n s = √s · 1_{[0,n]}(s)`. -/
private noncomputable def sqrtCutoffSym (n : ℕ) : ℝ → ℂ :=
  fun s => (Real.sqrt s : ℂ) * Set.indicator (Set.Icc 0 (n : ℝ)) (fun _ => (1 : ℂ)) s

private lemma measurable_sqrtCutoffSym (n : ℕ) : Measurable (sqrtCutoffSym n) :=
  measurable_sqrtC.mul (measurable_const.indicator measurableSet_Icc)

private lemma bdd_sqrtCutoffSym (n : ℕ) : ∃ C, ∀ s, ‖sqrtCutoffSym n s‖ ≤ C := by
  refine ⟨Real.sqrt (n : ℝ), fun s => ?_⟩
  rw [sqrtCutoffSym, norm_mul]
  by_cases hs : s ∈ Set.Icc 0 (n : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
    exact Real.sqrt_le_sqrt hs.2
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity

/-- **Step 2 (operator identity).**  `Δ^{½} (E([0,n]) y) = Φ(√·1_{[0,n]}) y`.  Truncating the `√`
calculus, `pmapTrunc U √ m (E([0,n])y) = Φ(truncSym √ m · 1_{[0,n]}) y`, which is EVENTUALLY (in
`m`) equal to `Φ(√·1_{[0,n]}) y = Φ(g_n) y` (on `[0,n]`, `‖√s‖ = √s ≤ √n ≤ m`); an
eventually-constant sequence converges to that constant, while `pmapOfPVM_apply_tendsto` says it
converges to `Δ^{½}(E([0,n])y)`.  Uniqueness of limits finishes. -/
theorem modularSqrt_cutoff_apply (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (y : H) (n : ℕ) :
    modularSqrt hcyc hsep
        ⟨spectralProjection (modularGroup hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc y,
          modularOp_domain_le_modularSqrt_domain hcyc hsep
            (modular_cutoff_mem_domain hcyc hsep y n)⟩
      = spectralCalculus (modularGroup hcyc hsep) (sqrtCutoffSym n)
          (measurable_sqrtCutoffSym n) (bdd_sqrtCutoffSym n) y := by
  set U := modularGroup hcyc hsep with _hU
  set xn := spectralProjection U (Set.Icc 0 (n : ℝ)) measurableSet_Icc y with hxn
  -- the membership facts for the domain element on the LHS
  have hxnmem : xn ∈ (modularOp M Ω).domain := modular_cutoff_mem_domain hcyc hsep y n
  have hxnL2 : Integrable (fun s => ‖(Real.sqrt s : ℂ)‖ ^ 2) (borelMeasure U xn) := by
    have := modularOp_domain_le_modularSqrt_domain hcyc hsep hxnmem
    exact (ProjValMeasure.mem_pmapDomain _).mp this
  -- the truncated calculus on `xn`, rewritten as `Φ(truncSym √ m · 1_{[0,n]}) y`.
  have htrunc : ∀ m : ℕ, pmapTrunc U (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC m xn
      = spectralCalculus U
          (fun s => truncSym (fun t => (Real.sqrt t : ℂ)) m s
            * Set.indicator (Set.Icc 0 (n : ℝ)) (fun _ => (1 : ℂ)) s)
          ((measurable_truncSym measurable_sqrtC m).mul
            (measurable_const.indicator measurableSet_Icc))
          (bounded_mul (truncSym_bdd _ m) (indicator_one_bdd _)) y := by
    intro m
    rw [pmapTrunc_apply]
    have hE : xn = spectralCalculus U (Set.indicator (Set.Icc 0 (n : ℝ)) fun _ => (1 : ℂ))
        (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _) y := by
      rw [hxn]; rfl
    rw [hE, ← ContinuousLinearMap.mul_apply,
      spectralCalculus_mul U (Set.indicator (Set.Icc 0 (n : ℝ)) fun _ => (1 : ℂ))
        (truncSym (fun t => (Real.sqrt t : ℂ)) m)
        (measurable_const.indicator measurableSet_Icc) (indicator_one_bdd _)
        (measurable_truncSym measurable_sqrtC m) (truncSym_bdd _ m)
        ((measurable_truncSym measurable_sqrtC m).mul
          (measurable_const.indicator measurableSet_Icc))
        (bounded_mul (truncSym_bdd _ m) (indicator_one_bdd _))]
  -- for `m ≥ ⌈√n⌉₊`, the truncated symbol equals `g_n` pointwise.
  have hev : ∀ᶠ m : ℕ in atTop,
      pmapTrunc U (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC m xn
        = spectralCalculus U (sqrtCutoffSym n) (measurable_sqrtCutoffSym n)
          (bdd_sqrtCutoffSym n) y := by
    filter_upwards [eventually_ge_atTop ⌈Real.sqrt (n : ℝ)⌉₊] with m hm
    rw [htrunc m]
    refine congrArg (fun T : H →L[ℂ] H => T y) ?_
    refine spectralCalculus_congr U ?_ _ _ _ _
    funext s
    rw [sqrtCutoffSym]
    by_cases hs : s ∈ Set.Icc 0 (n : ℝ)
    · rw [Set.indicator_of_mem hs, mul_one, mul_one, truncSym_apply, if_pos]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
      calc Real.sqrt s ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hs.2
        _ ≤ ⌈Real.sqrt (n : ℝ)⌉₊ := Nat.le_ceil _
        _ ≤ (m : ℝ) := by exact_mod_cast hm
    · rw [Set.indicator_of_notMem hs, mul_zero, mul_zero]
  -- uniqueness of limits: eventually-constant ⟹ tends to the constant;
  -- and `pmapOfPVM_apply_tendsto`.
  have htends1 := pmapOfPVM_apply_tendsto U (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC hxnL2
  have htends2 : Tendsto (fun m => pmapTrunc U (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC m xn)
      atTop (𝓝 (spectralCalculus U (sqrtCutoffSym n) (measurable_sqrtCutoffSym n)
        (bdd_sqrtCutoffSym n) y)) :=
    Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  exact tendsto_nhds_unique htends1 htends2

/-- **Step 2 (the pairing on cut-offs).**  `⟪y, Δ^{½}(E([0,n])y)⟫ = ∫ √s·1_{[0,n]}(s) dμ_y`.
Substitute the operator identity (`modularSqrt_cutoff_apply`), then read off the quadratic form
(`inner_spectralCalculus` + `spectralForm_self`). -/
theorem inner_modularSqrt_cutoff (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (y : H) (n : ℕ) :
    ⟪y, modularSqrt hcyc hsep
        ⟨spectralProjection (modularGroup hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc y,
          modularOp_domain_le_modularSqrt_domain hcyc hsep
            (modular_cutoff_mem_domain hcyc hsep y n)⟩⟫_ℂ
      = ∫ s, sqrtCutoffSym n s ∂(borelMeasure (modularGroup hcyc hsep) y) := by
  rw [modularSqrt_cutoff_apply hcyc hsep y n,
    inner_spectralCalculus (modularGroup hcyc hsep) (sqrtCutoffSym n) (measurable_sqrtCutoffSym n)
      (bdd_sqrtCutoffSym n) y y,
    spectralForm_self (modularGroup hcyc hsep) y (measurable_sqrtCutoffSym n)
      (bdd_sqrtCutoffSym n)]

/-! ## Step 3 — `μ_y((0,∞)) = 0` from the vanishing pairing -/

/-- The real square-root cut-off `√s · 1_{[0,n]}(s)`, the real shadow of `sqrtCutoffSym n`. -/
private noncomputable def realCutoffSym (n : ℕ) : ℝ → ℝ :=
  fun s => Real.sqrt s * Set.indicator (Set.Icc 0 (n : ℝ)) (fun _ => (1 : ℝ)) s

private lemma sqrtCutoffSym_eq_ofReal (n : ℕ) (s : ℝ) :
    sqrtCutoffSym n s = ((realCutoffSym n s : ℝ) : ℂ) := by
  rw [sqrtCutoffSym, realCutoffSym, Complex.ofReal_mul]
  congr 1
  by_cases hs : s ∈ Set.Icc 0 (n : ℝ)
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Complex.ofReal_one]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, Complex.ofReal_zero]

private lemma realCutoffSym_nonneg (n : ℕ) : 0 ≤ realCutoffSym n := by
  intro s
  rw [realCutoffSym]
  apply mul_nonneg (Real.sqrt_nonneg s)
  rw [Set.indicator_apply]; split_ifs <;> norm_num

private lemma measurable_realCutoffSym (n : ℕ) : Measurable (realCutoffSym n) :=
  Real.continuous_sqrt.measurable.mul (measurable_const.indicator measurableSet_Icc)

private lemma integrable_realCutoffSym (U_grp : OneParameterUnitaryGroup (H := H)) (y : H) (n : ℕ) :
    Integrable (realCutoffSym n) (borelMeasure U_grp y) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp y) := borelMeasure_isFiniteMeasure U_grp y
  refine (integrable_const (Real.sqrt (n : ℝ))).mono'
    (measurable_realCutoffSym n).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (realCutoffSym_nonneg n s), realCutoffSym]
  by_cases hs : s ∈ Set.Icc 0 (n : ℝ)
  · rw [Set.indicator_of_mem hs, mul_one]; exact Real.sqrt_le_sqrt hs.2
  · rw [Set.indicator_of_notMem hs, mul_zero]; positivity

/-- **Step 3 (cut-off version).**  If `⟪y, Δ^{½}(E([0,n])y)⟫ = 0` then `μ_y((0,n]) = 0`.  The
pairing is `∫ √s·1_{[0,n]} dμ_y = ∫ (realCutoffSym n) dμ_y` (real); vanishing of a nonnegative
integrable integral gives `realCutoffSym n =ᵐ 0`, but `realCutoffSym n > 0` on `(0,n]`, so
`μ_y((0,n]) = 0`. -/
theorem borelMeasure_modular_Ioc_zero (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (y : H)
    (n : ℕ)
    (hpair : ⟪y, modularSqrt hcyc hsep
        ⟨spectralProjection (modularGroup hcyc hsep) (Set.Icc 0 (n : ℝ)) measurableSet_Icc y,
          modularOp_domain_le_modularSqrt_domain hcyc hsep
            (modular_cutoff_mem_domain hcyc hsep y n)⟩⟫_ℂ = 0) :
    borelMeasure (modularGroup hcyc hsep) y (Set.Ioc 0 (n : ℝ)) = 0 := by
  set U := modularGroup hcyc hsep with _hU
  set μ := borelMeasure U y with _hμ
  -- the real integral vanishes
  have hint0 : ∫ s, realCutoffSym n s ∂μ = 0 := by
    have h := inner_modularSqrt_cutoff hcyc hsep y n
    rw [hpair] at h
    have hcast : ∫ s, sqrtCutoffSym n s ∂μ = ((∫ s, realCutoffSym n s ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall fun s => sqrtCutoffSym_eq_ofReal n s)
    rw [hcast] at h
    exact_mod_cast h.symm
  -- `realCutoffSym n =ᵐ 0`
  have hae : realCutoffSym n =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (realCutoffSym_nonneg n)
      (integrable_realCutoffSym U y n)).mp hint0
  -- `μ {realCutoffSym n ≠ 0} = 0`, and `(0,n] ⊆ {realCutoffSym n ≠ 0}`.
  have hnull : μ {s | realCutoffSym n s ≠ 0} = 0 := by
    have := (ae_iff (μ := μ)).mp hae
    simpa using this
  refine measure_mono_null (fun s hs => ?_) hnull
  rw [Set.mem_setOf_eq, realCutoffSym]
  have hs0 : (0 : ℝ) < s := hs.1
  have hsIcc : s ∈ Set.Icc 0 (n : ℝ) := Set.mem_Icc.mpr ⟨le_of_lt hs0, hs.2⟩
  rw [Set.indicator_of_mem hsIcc, mul_one]
  exact ne_of_gt (Real.sqrt_pos.mpr hs0)

/-- **Step 3.**  If `y ⊥ Δ^{½}(D(Δ))` then `μ_y((0,∞)) = 0`.  Each cut-off pairing
`⟪y, Δ^{½}(E([0,n])y)⟫` vanishes (orthogonality), so `μ_y((0,n]) = 0` for all `n`, and
`(0,∞) = ⋃ₙ (0,n]`. -/
theorem borelMeasure_modular_Ioi_zero (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (y : H)
    (hperp : ∀ x : (modularOp M Ω).domain,
      ⟪y, modularSqrtOnModularDomain hcyc hsep x⟫_ℂ = 0) :
    borelMeasure (modularGroup hcyc hsep) y (Set.Ioi (0 : ℝ)) = 0 := by
  have hcover : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioc 0 (n : ℝ) := by
    ext s
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · intro hs
      obtain ⟨n, hn⟩ := exists_nat_ge s
      exact ⟨n, hs, hn⟩
    · rintro ⟨n, hs, _⟩; exact hs
  rw [hcover]
  refine measure_iUnion_null fun n => ?_
  refine borelMeasure_modular_Ioc_zero hcyc hsep y n ?_
  have h := hperp ⟨spectralProjection (modularGroup hcyc hsep) (Set.Icc 0 (n : ℝ))
    measurableSet_Icc y, modular_cutoff_mem_domain hcyc hsep y n⟩
  rwa [modularSqrtOnModularDomain_apply] at h

/-! ## Step 4 — `μ_y({0}) = 0` (injectivity) and `y = 0` -/

/-- **Step 4 (the atom).**  `μ_y({0}) = 0`.  `E({0})y` is a `0`-eigenvector of `Δ` (group-level
`generator U ⟨E({0})y,_⟩ = 0`, transported by Stone), but `Δ` is injective, so `E({0})y = 0`, and
`μ_y({0}) = ‖E({0})y‖² = 0`. -/
theorem borelMeasure_modular_singleton_zero (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (y : H) :
    borelMeasure (modularGroup hcyc hsep) y ({0} : Set ℝ) = 0 := by
  set U := modularGroup hcyc hsep with _hU
  -- `E({0}) y ∈ D(Δ)` (group level then Stone)
  have hmem_gen : spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y
      ∈ (generator U).domain :=
    spectralProjection_singleton_mem_generatorDomain U 0 y
  have hmem : spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y
      ∈ (modularOp M Ω).domain := by
    rw [← generator_modularGroup hcyc hsep]; exact hmem_gen
  -- `Δ (E({0})y) = 0`
  have hgen0 : generator U ⟨spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y,
      hmem_gen⟩ = 0 := by
    have h := generator_spectralProjection_singleton U 0 y
    simp only [Complex.ofReal_zero, zero_smul] at h
    convert h using 2
  have hΔ0 : modularOp M Ω ⟨spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y,
      hmem⟩ = 0 := by
    have htrans : modularOp M Ω
        ⟨spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y, hmem⟩
      = generator U ⟨spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y, hmem_gen⟩ :=
      ((le_of_eq (generator_modularGroup hcyc hsep)).2 rfl).symm
    rw [htrans, hgen0]
  -- injectivity: `E({0})y = 0`
  have hEy0 : spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y = 0 :=
    modularOp_injective hcyc hsep
      ⟨spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y, hmem⟩ hΔ0
  -- `μ_y({0}) = ‖E({0})y‖² = 0`
  haveI : IsFiniteMeasure (borelMeasure U y) := borelMeasure_isFiniteMeasure U y
  have hnorm : ((borelMeasure U y ({0} : Set ℝ)).toReal) = 0 := by
    rw [← norm_sq_spectralProjection U ({0} : Set ℝ) (measurableSet_singleton 0) y, hEy0]
    simp
  exact (ENNReal.toReal_eq_zero_iff _).mp hnorm |>.resolve_right (measure_ne_top _ _)

/-- **Step 4 (conclusion).**  If `y ⊥ Δ^{½}(D(Δ))` then `y = 0`.  The modular spectral measure
`μ_y` charges neither `(-∞,0)` (positivity, Step 1), nor `(0,∞)` (the vanishing pairing, Step 3),
nor `{0}` (injectivity, Step 4); so `μ_y(ℝ) = 0`, i.e. `‖y‖² = ‖E(ℝ)y‖² = μ_y(ℝ).toReal = 0`. -/
theorem eq_zero_of_orthogonal_modularSqrt (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) (y : H)
    (hperp : ∀ x : (modularOp M Ω).domain,
      ⟪y, modularSqrtOnModularDomain hcyc hsep x⟫_ℂ = 0) :
    y = 0 := by
  set U := modularGroup hcyc hsep with _hU
  haveI : IsFiniteMeasure (borelMeasure U y) := borelMeasure_isFiniteMeasure U y
  -- the three pieces vanish
  have hIio : borelMeasure U y (Set.Iio (0 : ℝ)) = 0 := borelMeasure_modular_Iio_zero hcyc hsep y
  have hIoi : borelMeasure U y (Set.Ioi (0 : ℝ)) = 0 :=
    borelMeasure_modular_Ioi_zero hcyc hsep y hperp
  have hzero : borelMeasure U y ({0} : Set ℝ) = 0 := borelMeasure_modular_singleton_zero hcyc hsep y
  -- `univ ⊆ Iio 0 ∪ ({0} ∪ Ioi 0)`, so `μ_y(univ) = 0`
  have hsub : (Set.univ : Set ℝ) ⊆ Set.Iio 0 ∪ ({0} ∪ Set.Ioi 0) := by
    intro s _
    rcases lt_trichotomy s 0 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hunivle : borelMeasure U y (Set.univ : Set ℝ)
      ≤ borelMeasure U y (Set.Iio 0) + (borelMeasure U y ({0} : Set ℝ)
          + borelMeasure U y (Set.Ioi 0)) :=
    le_trans (measure_mono hsub)
      (le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _))
  have huniv0 : borelMeasure U y (Set.univ : Set ℝ) = 0 := by
    have : borelMeasure U y (Set.univ : Set ℝ) ≤ 0 := by
      rw [hIio, hzero, hIoi] at hunivle; simpa using hunivle
    exact le_antisymm this bot_le
  -- `‖y‖² = μ_y(univ).toReal = 0`
  have hnormsq : ‖y‖ ^ 2 = 0 := by
    have h := norm_sq_spectralProjection U (Set.univ : Set ℝ) MeasurableSet.univ y
    rw [spectralProjection_univ] at h
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h, huniv0]; simp
  have : ‖y‖ = 0 := by nlinarith [norm_nonneg y, hnormsq]
  exact norm_eq_zero.mp this

/-- **`Δ^{½}(D(Δ))` is dense in `H`** — the source density input to the polar isometry
`W = extendOfIsometry (Δ^{½}x ↦ S x)` of `S = J Δ^{½}` (R3).  Equivalently, no nonzero vector is
orthogonal to `Δ^{½}(D(Δ))`: any such `y` would have a modular spectral measure `μ_y` vanishing on
`(-∞,0)` (positivity of `Δ`), on `(0,∞)` (the vanishing cut-off pairings), and on `{0}`
(injectivity of `Δ`), hence `‖y‖² = μ_y(ℝ) = 0`. -/
theorem denseRange_modularSqrtOnModularDomain (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    DenseRange (modularSqrtOnModularDomain hcyc hsep) := by
  rw [DenseRange, ← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  refine eq_zero_of_orthogonal_modularSqrt hcyc hsep y (fun x => ?_)
  exact (Submodule.mem_orthogonal' _ y).mp hy _ (LinearMap.mem_range_self _ x)

/-! ## R3 capstone: the polar isometry `W` and the modular conjugation `J`

With both density inputs in hand — `denseRange_modularSqrtOnModularDomain` (source `Δ^{½}(D(Δ))`)
and `denseRange_tomitaOnModularDomain` (target `S(D(Δ))`) — and the isometry `‖S x‖ = ‖Δ^{½} x‖`
(`norm_modularSqrt_eq_norm_tomita`, R2), `LinearEquiv.extendOfIsometry` extends the densely-defined
correspondence `Δ^{½}x ↦ S x` to a unitary `W : H ≃ₗᵢ[ℂ] Conj H`.  The **modular conjugation** is
`J = ofConj ∘ W : H ≃ₗᵢ⋆[ℂ] H` (antiunitary), and the polar decomposition reads `S = J Δ^{½}`. -/

/-- **The polar isometry hypothesis** `‖S x‖ = ‖Δ^{½} x‖` on `D(Δ)`, in the form the
`extendOfIsometry` correspondence needs.  This is `norm_modularSqrt_eq_norm_tomita` (R2) repackaged
for the two domain-restricted linear maps. -/
theorem norm_tomitaOnModularDomain_eq (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (modularOp M Ω).domain) :
    ‖tomitaOnModularDomain M Ω x‖ = ‖modularSqrtOnModularDomain hcyc hsep x‖ := by
  have hxgen : (x : H) ∈ (generator (modularGroup hcyc hsep)).domain := by
    rw [generator_modularGroup hcyc hsep]; exact x.2
  rw [modularSqrtOnModularDomain_apply, tomitaOnModularDomain_apply]
  exact (norm_modularSqrt_eq_norm_tomita hcyc hsep ⟨(x : H), hxgen⟩
    (modularOp_domain_le_tomita x.2)).symm

/-- **The polar isometry `W : H ≃ₗᵢ[ℂ] Conj H`** of the polar decomposition `S = J Δ^{½}`.  It is
the unitary extension (`LinearEquiv.extendOfIsometry`) of the dense, norm-preserving correspondence
`Δ^{½} x ↦ S x` (`x ∈ D(Δ)`); see `modularW_apply_modularSqrt` for the defining property. -/
noncomputable def modularW (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    H ≃ₗᵢ[ℂ] Conj H :=
  (LinearEquiv.refl ℂ (modularOp M Ω).domain).extendOfIsometry
    (modularSqrtOnModularDomain hcyc hsep) (tomitaOnModularDomain M Ω)
    (denseRange_modularSqrtOnModularDomain hcyc hsep)
    (denseRange_tomitaOnModularDomain hcyc hsep)
    (fun x => norm_tomitaOnModularDomain_eq hcyc hsep x)

/-- **The defining property of `W`**: `W (Δ^{½} x) = S x` for `x ∈ D(Δ)`. -/
@[simp] theorem modularW_apply_modularSqrt (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (modularOp M Ω).domain) :
    modularW hcyc hsep (modularSqrtOnModularDomain hcyc hsep x) = tomitaOnModularDomain M Ω x :=
  (LinearEquiv.refl ℂ (modularOp M Ω).domain).extendOfIsometry_eq
    (modularSqrtOnModularDomain hcyc hsep) (tomitaOnModularDomain M Ω)
    (denseRange_modularSqrtOnModularDomain hcyc hsep)
    (denseRange_tomitaOnModularDomain hcyc hsep)
    (fun x => norm_tomitaOnModularDomain_eq hcyc hsep x) x

/-- **The modular conjugation `J = ofConj ∘ W : H ≃ₗᵢ⋆[ℂ] H`** (antiunitary), extracted from the
polar decomposition `S = J Δ^{½}` (R3).  Antilinearity is exactly the conjugation in `ofConj`
(`= (toConjₗᵢ H).symm`), composed with the `ℂ`-linear `W`. -/
noncomputable def modularConjugation (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    H ≃ₗᵢ⋆[ℂ] H :=
  (modularW hcyc hsep).trans (toConjₗᵢ H).symm

/-- **The polar decomposition `S = J Δ^{½}`**: for `x ∈ D(Δ)`, `toConj (J (Δ^{½} x)) = S x`, i.e.
`S x = J (Δ^{½} x)` read in `Conj H` via the antiunitary `toConjₗᵢ`.  (Equivalently
`J (Δ^{½} x) = ofConj (S x)`.) -/
theorem tomita_eq_modularConjugation_modularSqrt (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)
    (x : (modularOp M Ω).domain) :
    (toConjₗᵢ H) (modularConjugation hcyc hsep (modularSqrtOnModularDomain hcyc hsep x))
      = tomitaOnModularDomain M Ω x := by
  rw [modularConjugation, LinearIsometryEquiv.trans_apply, modularW_apply_modularSqrt,
    LinearIsometryEquiv.apply_symm_apply]

end Spectra.TomitaTakesaki

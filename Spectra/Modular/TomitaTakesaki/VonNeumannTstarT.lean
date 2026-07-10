/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.TomitaTakesaki.ModularOperator
/-!
# von Neumann's `T⋆T` theorem for the modular operator `Δ = S⋆ S` (H3)

Let `S = tomitaClosure M Ω : H →ₗ.[ℂ] Conj H` be the closed, densely-defined Tomita operator
(H2), with adjoint `S⋆ = S.adjoint`. The **modular operator** is `Δ = S⋆ S`, the central object
of Tomita–Takesaki theory. This file constructs it as a **self-adjoint, non-negative**
`LinearPMap` — *von Neumann's theorem*: for a closed, densely-defined `T`, the operator `T⋆ T`
is self-adjoint and `≥ 0`.

## Main results

* `modularOp` — `Δ = S⋆.comp (S.domRestrict modularDomain)`, the modular operator on its proper
  domain `{x ∈ D(S) : S x ∈ D(S⋆)}`;
* `modularOp_nonneg` — `Re ⟪Δ x, x⟫ ≥ 0`;
* `modularOp_isSymmetric` — `Δ` is a formal adjoint of itself (symmetric);
* `one_add_modularOp_surjective` — `1 + Δ` is **surjective** (von Neumann's graph argument);
* `modularOp_isSelfAdjoint` — `Δ` is **self-adjoint**, discharging ROADMAP milestone H3.

## Proof outline

The hard content is `one_add_modularOp_surjective`, proved by the classical orthogonal
decomposition of the closed graph `Γ(S)`:

* `graphL2_hasOrthogonalProjection` — `Γ(S)` is closed in the L² space `WithLp 2 (H × Conj H)`,
  hence has an orthogonal projection (transport of `tomitaClosure_isClosed` through the
  continuous coordinate map `ofLp`);
* decompose `toLp (h, 0) = (x, S x) + q` with `(x, S x) ∈ Γ(S)`, `q ∈ Γ(S)ᗮ`;
* identify `Γ(S)ᗮ` via `LinearPMap.adjoint_graph_eq_graph_adjoint` and `Submodule.mem_adjoint_iff`:
  `q = (-S⋆ g, g)`; matching components forces `x ∈ D(Δ)` and `h = x + S⋆(S x) = (1 + Δ) x`.

Self-adjointness then follows from the real von Neumann criterion (a densely-defined symmetric
operator with `1 + Δ` bijective and bounded inverse is self-adjoint), proved directly from the
positivity bound `‖(1 + Δ) x‖ ≥ ‖x‖`.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]
-/

open scoped InnerProductSpace
open Spectra.Conj

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ## The modular operator `Δ = S⋆ S` (promoted from the recon spike) -/

/-- The domain of the modular operator: `{x ∈ D(S) : S x ∈ D(S⋆)}`, as a submodule of `H`. -/
noncomputable def modularDomain (M : VonNeumannAlgebra H) (Ω : H) : Submodule ℂ H where
  carrier := {x | ∃ hx : x ∈ (tomitaClosure M Ω).domain,
    (tomitaClosure M Ω) ⟨x, hx⟩ ∈ (tomitaClosure M Ω).adjoint.domain}
  add_mem' := by
    rintro x y ⟨hx, hSx⟩ ⟨hy, hSy⟩
    refine ⟨(tomitaClosure M Ω).domain.add_mem hx hy, ?_⟩
    rw [show (⟨x + y, (tomitaClosure M Ω).domain.add_mem hx hy⟩ : (tomitaClosure M Ω).domain)
        = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, LinearPMap.map_add]
    exact (tomitaClosure M Ω).adjoint.domain.add_mem hSx hSy
  zero_mem' := by
    refine ⟨(tomitaClosure M Ω).domain.zero_mem, ?_⟩
    rw [show (⟨(0 : H), (tomitaClosure M Ω).domain.zero_mem⟩ : (tomitaClosure M Ω).domain) = 0
        from rfl, LinearPMap.map_zero]
    exact (tomitaClosure M Ω).adjoint.domain.zero_mem
  smul_mem' := by
    rintro c x ⟨hx, hSx⟩
    refine ⟨(tomitaClosure M Ω).domain.smul_mem c hx, ?_⟩
    rw [show (⟨c • x, (tomitaClosure M Ω).domain.smul_mem c hx⟩ : (tomitaClosure M Ω).domain)
        = c • ⟨x, hx⟩ from rfl, LinearPMap.map_smul]
    exact (tomitaClosure M Ω).adjoint.domain.smul_mem c hSx

/-- **The modular operator `Δ = S⋆ S`**, as a `LinearPMap`, built by restricting `S` to the proper
domain `{x ∈ D(S) : S x ∈ D(S⋆)}` and post-composing with `S⋆`. -/
noncomputable def modularOp (M : VonNeumannAlgebra H) (Ω : H) : H →ₗ.[ℂ] H :=
  (tomitaClosure M Ω).adjoint.comp ((tomitaClosure M Ω).domRestrict (modularDomain M Ω)) <| by
    rintro ⟨x, hx⟩
    obtain ⟨⟨hxS, hSx⟩, _⟩ := hx
    rw [LinearPMap.domRestrict_apply (y := ⟨x, hxS⟩) rfl]
    exact hSx

/-- **Key applied identity.** For `x` in `D(Δ)`, `Δ x = S⋆ (S x₀)` where `x₀` is `x` viewed in
`D(S)`. -/
theorem modularOp_apply (x : (modularOp M Ω).domain)
    (hxS : (x : H) ∈ (tomitaClosure M Ω).domain)
    (hSx : (tomitaClosure M Ω) ⟨(x : H), hxS⟩ ∈ (tomitaClosure M Ω).adjoint.domain) :
    modularOp M Ω x
      = (tomitaClosure M Ω).adjoint ⟨(tomitaClosure M Ω) ⟨(x : H), hxS⟩, hSx⟩ := by
  have hinner : (tomitaClosure M Ω).domRestrict (modularDomain M Ω) x
      = (tomitaClosure M Ω) ⟨(x : H), hxS⟩ :=
    LinearPMap.domRestrict_apply (y := ⟨(x : H), hxS⟩) rfl
  change (tomitaClosure M Ω).adjoint.toFun.compPMap _ x = _
  rw [LinearMap.compPMap_apply]
  exact congrArg _ (Subtype.ext hinner)

/-- `Δ` is a formal adjoint of itself (symmetric). -/
theorem modularOp_isSymmetric (hcyc : IsCyclic M Ω) :
    (modularOp M Ω).IsFormalAdjoint (modularOp M Ω) := by
  intro x y
  obtain ⟨⟨hxS, hSx⟩, _⟩ := x.2
  obtain ⟨⟨hyS, hSy⟩, _⟩ := y.2
  have hdense : Dense ((tomitaClosure M Ω).domain : Set H) := tomitaClosure_domain_dense hcyc
  rw [modularOp_apply x hxS hSx, modularOp_apply y hyS hSy]
  have hL := LinearPMap.adjoint_isFormalAdjoint (T := tomitaClosure M Ω) hdense
    ⟨(tomitaClosure M Ω) ⟨(x : H), hxS⟩, hSx⟩ ⟨(y : H), hyS⟩
  have hR := LinearPMap.adjoint_isFormalAdjoint (T := tomitaClosure M Ω) hdense
    ⟨(tomitaClosure M Ω) ⟨(y : H), hyS⟩, hSy⟩ ⟨(x : H), hxS⟩
  rw [hL, ← inner_conj_symm (𝕜 := ℂ) ((x : H)), hR, inner_conj_symm]

/-- `Δ ≥ 0`: `Re ⟪Δ x, x⟫ = ‖S x‖² ≥ 0`. -/
theorem modularOp_nonneg (hcyc : IsCyclic M Ω) (x : (modularOp M Ω).domain) :
    0 ≤ RCLike.re ⟪modularOp M Ω x, (x : H)⟫_ℂ := by
  obtain ⟨⟨hxS, hSx⟩, _⟩ := x.2
  rw [modularOp_apply x hxS hSx]
  have hdense : Dense ((tomitaClosure M Ω).domain : Set H) := tomitaClosure_domain_dense hcyc
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := tomitaClosure M Ω) hdense
    ⟨(tomitaClosure M Ω) ⟨(x : H), hxS⟩, hSx⟩ ⟨(x : H), hxS⟩
  rw [hfa]
  exact inner_self_nonneg

/-! ## V0. The L²-transported graph has an orthogonal projection -/

/-- **The L²-transported graph of `S`** — `Γ := image of S.graph in `WithLp 2 (H × Conj H)`. -/
noncomputable def graphL2 (M : VonNeumannAlgebra H) (Ω : H) :
    Submodule ℂ (WithLp 2 (H × Conj H)) :=
  (tomitaClosure M Ω).graph.map (WithLp.linearEquiv 2 ℂ (H × Conj H)).symm.toLinearMap

theorem mem_graphL2_iff (M : VonNeumannAlgebra H) (Ω : H) (x : WithLp 2 (H × Conj H)) :
    x ∈ graphL2 M Ω ↔ (WithLp.ofLp x) ∈ (tomitaClosure M Ω).graph := by
  simp only [graphL2, Submodule.mem_map, LinearEquiv.coe_coe, WithLp.coe_symm_linearEquiv]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rwa [WithLp.ofLp_toLp]
  · intro hx
    exact ⟨WithLp.ofLp x, hx, WithLp.toLp_ofLp _ _⟩

/-- `Γ := graphL2` is **closed** in `WithLp 2 (H × Conj H)`: it is the preimage of the closed
`S.graph` under the continuous coordinate map `ofLp`. -/
theorem graphL2_isClosed (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    IsClosed (graphL2 M Ω : Set (WithLp 2 (H × Conj H))) := by
  have hclosed : IsClosed ((tomitaClosure M Ω).graph : Set (H × Conj H)) :=
    tomitaClosure_isClosed hcyc hsep
  have : (graphL2 M Ω : Set (WithLp 2 (H × Conj H)))
      = WithLp.ofLp ⁻¹' ((tomitaClosure M Ω).graph : Set (H × Conj H)) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_preimage, mem_graphL2_iff]
  rw [this]
  exact hclosed.preimage (WithLp.prod_continuous_ofLp 2 H (Conj H))

/-- `Γ := graphL2` has an orthogonal projection (it is closed in the complete L² space). -/
theorem graphL2_hasOrthogonalProjection (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    (graphL2 M Ω).HasOrthogonalProjection := by
  have : CompleteSpace (graphL2 M Ω) :=
    (graphL2_isClosed hcyc hsep).isComplete.completeSpace_coe
  infer_instance

/-! ## V1–V3. `1 + Δ` is surjective (von Neumann's graph argument) -/

/-- **Membership in the orthogonal complement `Γ(S)ᗮ`** (computed in `WithLp 2 (H × Conj H)`)
characterizes the second coordinate as lying in `D(S⋆)`: if `q ∈ Γᗮ`, then `(ofLp q).2 ∈ D(S⋆)`
and `S⋆ (ofLp q).2 = -(ofLp q).1`. This is the orthogonal-complement-of-the-graph computation at
the heart of von Neumann's theorem. -/
theorem mem_graphL2_orthogonal (hcyc : IsCyclic M Ω) {q : WithLp 2 (H × Conj H)}
    (hq : q ∈ (graphL2 M Ω)ᗮ) :
    ∃ hr : (WithLp.ofLp q).2 ∈ (tomitaClosure M Ω).adjoint.domain,
      (tomitaClosure M Ω).adjoint ⟨(WithLp.ofLp q).2, hr⟩ = -(WithLp.ofLp q).1 := by
  have hdense : Dense ((tomitaClosure M Ω).domain : Set H) := tomitaClosure_domain_dense hcyc
  set p : H := (WithLp.ofLp q).1 with _hp
  set r : Conj H := (WithLp.ofLp q).2 with _hr
  -- Orthogonality against every graph element `(a, S a)`:
  -- `⟪a, p⟫ + ⟪S a, r⟫ = 0` for all `a ∈ D(S)`.
  have hortho : ∀ a : (tomitaClosure M Ω).domain,
      ⟪(a : H), p⟫_ℂ + ⟪tomitaClosure M Ω a, r⟫_ℂ = 0 := by
    intro a
    have hmem : WithLp.toLp 2 ((a : H), tomitaClosure M Ω a) ∈ graphL2 M Ω := by
      rw [mem_graphL2_iff, WithLp.ofLp_toLp]
      exact (tomitaClosure M Ω).mem_graph a
    have := (Submodule.mem_orthogonal _ q).1 hq _ hmem
    rwa [WithLp.prod_inner_apply, WithLp.ofLp_toLp] at this
  -- The single identity `⟪-p, a⟫ = ⟪r, S a⟫` for all `a ∈ D(S)`.
  have hkey : ∀ a : (tomitaClosure M Ω).domain,
      ⟪(-p : H), (a : H)⟫_ℂ = ⟪r, tomitaClosure M Ω a⟫_ℂ := by
    intro a
    have h := hortho a
    have hSa : ⟪tomitaClosure M Ω a, r⟫_ℂ = -⟪(a : H), p⟫_ℂ := by linear_combination h
    rw [← inner_conj_symm (𝕜 := ℂ) r (tomitaClosure M Ω a), hSa, map_neg,
      inner_conj_symm, inner_neg_left]
  have hrdom : r ∈ (tomitaClosure M Ω).adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists r ⟨-p, hkey⟩
  exact ⟨hrdom, LinearPMap.adjoint_apply_eq hdense ⟨r, hrdom⟩ hkey⟩

/-- **V1 + V2 + V3 — `1 + Δ` is surjective.**  For every `h : H` there is `x ∈ D(Δ)` with
`Δ x + x = h`. Proof: orthogonally decompose `toLp (h, 0) = (x, S x) + q` in the L² graph space;
`q ∈ Γᗮ` forces `S x ∈ D(S⋆)` (so `x ∈ D(Δ)`) and `S⋆ (S x) = x.1`, whence
`h = x + S⋆(S x) = (1 + Δ) x`. -/
theorem one_add_modularOp_surjective (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    ∀ h : H, ∃ x : (modularOp M Ω).domain, modularOp M Ω x + (x : H) = h := by
  intro h
  haveI := graphL2_hasOrthogonalProjection hcyc hsep
  -- Decompose `toLp (h, 0) = w + q`, `w ∈ Γ`, `q ∈ Γᗮ`.
  obtain ⟨w, hw, q, hq, hdecomp⟩ :=
    (graphL2 M Ω).exists_add_mem_mem_orthogonal (WithLp.toLp 2 ((h, (0 : Conj H))))
  -- `w ∈ Γ`: `ofLp w = (xH, S xH)`.
  rw [mem_graphL2_iff] at hw
  rw [(tomitaClosure M Ω).mem_graph_iff] at hw
  obtain ⟨xS, hxS_fst, hxS_snd⟩ := hw
  set xH : H := (xS : H) with hxH
  -- `q ∈ Γᗮ`: `(ofLp q).2 ∈ D(S⋆)` and `S⋆ (ofLp q).2 = -(ofLp q).1`.
  obtain ⟨hr, hSstar⟩ := mem_graphL2_orthogonal hcyc hq
  -- Read off both components of `ofLp (toLp (h,0)) = ofLp w + ofLp q`.
  have hcomp : ((h, (0 : Conj H)) : H × Conj H) = WithLp.ofLp w + WithLp.ofLp q := by
    have := congrArg WithLp.ofLp hdecomp
    rwa [WithLp.ofLp_toLp, WithLp.ofLp_add] at this
  have hfst : h = xH + (WithLp.ofLp q).1 := by
    have := congrArg Prod.fst hcomp
    simpa [hxS_fst, hxH] using this
  have hsnd : (0 : Conj H) = tomitaClosure M Ω xS + (WithLp.ofLp q).2 := by
    have := congrArg Prod.snd hcomp
    simpa [hxS_snd] using this
  -- From `0 = S xH + (ofLp q).2`: `(ofLp q).2 = - S xH`, so `S xH ∈ D(S⋆)`.
  have hq2 : (WithLp.ofLp q).2 = -(tomitaClosure M Ω xS) := by
    have : (WithLp.ofLp q).2 + tomitaClosure M Ω xS = 0 := by
      rw [add_comm]; exact hsnd.symm
    exact eq_neg_of_add_eq_zero_left this
  have hSxdom : tomitaClosure M Ω xS ∈ (tomitaClosure M Ω).adjoint.domain := by
    rw [← neg_neg (tomitaClosure M Ω xS), ← hq2]
    exact (tomitaClosure M Ω).adjoint.domain.neg_mem hr
  -- Hence `xH ∈ modularDomain` (note `⟨xH, xS.2⟩ = xS`).
  have hxmem : xH ∈ modularDomain M Ω := by
    refine ⟨xS.2, ?_⟩
    convert hSxdom using 2
  -- Package `x : D(Δ)` and compute `(1 + Δ) x = h`.
  have hxΔdom : xH ∈ (modularOp M Ω).domain := ⟨hxmem, xS.2⟩
  refine ⟨⟨xH, hxΔdom⟩, ?_⟩
  -- `Δ ⟨xH,_⟩ = S⋆ ⟨S xH, _⟩`.
  rw [modularOp_apply ⟨xH, hxΔdom⟩ xS.2 (by convert hSxdom using 2)]
  -- `S⋆ (S xH) = - (ofLp q).2-adjoint`… use `hSstar` and `hq2`.
  -- `S⋆ (ofLp q).2 = -(ofLp q).1`, and `(ofLp q).2 = - S xH`, so `S⋆ (S xH) = (ofLp q).1`.
  have hSstar' : (tomitaClosure M Ω).adjoint ⟨tomitaClosure M Ω xS, hSxdom⟩
      = (WithLp.ofLp q).1 := by
    have hcong : (⟨(WithLp.ofLp q).2, hr⟩ : (tomitaClosure M Ω).adjoint.domain)
        = -⟨tomitaClosure M Ω xS, hSxdom⟩ := Subtype.ext (by simpa using hq2)
    have hmapneg : (tomitaClosure M Ω).adjoint ⟨(WithLp.ofLp q).2, hr⟩
        = -((tomitaClosure M Ω).adjoint ⟨tomitaClosure M Ω xS, hSxdom⟩) := by
      rw [hcong, LinearPMap.map_neg]
    rw [hmapneg] at hSstar
    exact neg_injective hSstar
  rw [hSstar']
  -- Goal: `(ofLp q).1 + xH = h`; from `hfst : h = xH + (ofLp q).1`.
  rw [hfst]; abel

/-! ## V5. `Δ` is self-adjoint -/

/-- **`Δ` is self-adjoint** — discharges ROADMAP milestone H3.

The real von Neumann criterion: a densely-defined symmetric `Δ ≥ 0` with `1 + Δ` surjective is
self-adjoint. We have `Δ ⊆ Δ†` from symmetry (`IsFormalAdjoint.le_adjoint`); for the reverse, the
kernel of `1 + Δ†` is the orthogonal complement of the (full) range of `1 + Δ`, hence trivial. -/
theorem modularOp_isSelfAdjoint (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    IsSelfAdjoint (modularOp M Ω) := by
  set Δ := modularOp M Ω with _hΔ
  have hsym : Δ.IsFormalAdjoint Δ := modularOp_isSymmetric hcyc
  have hdense : Dense (Δ.domain : Set H) := by
    -- `D(Δ)` is the *smaller* set `modularDomain ⊓ D(S)`, so density does NOT follow from `D(S)`
    -- dense. Instead use von Neumann's argument: `D(Δ)ᗮ = 0`. If `h ⊥ D(Δ)`, surjectivity of
    -- `1 + Δ` gives `h = Δ g + g` with `g ∈ D(Δ)`; then `0 = ⟪g, h⟫ = ⟪g, Δ g⟫ + ‖g‖²` has both
    -- summands `≥ 0`, forcing `g = 0`, hence `h = 0`.
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro h hh
    obtain ⟨g, hg⟩ := one_add_modularOp_surjective hcyc hsep h
    have hortho : ⟪(g : H), h⟫_ℂ = 0 := (Submodule.mem_orthogonal _ h).1 hh (g : H) g.2
    rw [← hg, inner_add_right] at hortho
    have h1 : 0 ≤ RCLike.re ⟪(g : H), modularOp M Ω g⟫_ℂ := by
      rw [inner_re_symm]; exact modularOp_nonneg hcyc g
    have hre : RCLike.re ⟪(g : H), modularOp M Ω g⟫_ℂ + ‖(g : H)‖ ^ 2 = 0 := by
      have hr := congrArg RCLike.re hortho
      rwa [map_add, map_zero, inner_self_eq_norm_sq] at hr
    have hgz : (g : H) = 0 := by
      have h2 : ‖(g : H)‖ ^ 2 = 0 := by linarith [sq_nonneg ‖(g : H)‖]
      exact norm_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h2)
    have hg0 : g = 0 := Subtype.ext hgz
    rw [← hg, hg0]; simp
  have hsurj := one_add_modularOp_surjective hcyc hsep
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ (hsym.le_adjoint hdense)
  -- ⊢ Δ† ≤ Δ.  Key: `ker (1 + Δ†) = 0`, since `range (1 + Δ) = ⊤`.
  have hker : ∀ w : Δ.adjoint.domain, Δ.adjoint w = -(w : H) → (w : H) = 0 := by
    intro w hw
    -- For every `v : D(Δ)`, `⟪w, (1+Δ) v⟫ = ⟪w,v⟫ + ⟪Δ† w, v⟫ = ⟪w,v⟫ - ⟪w,v⟫ = 0`.
    have hortho : ∀ v : Δ.domain, ⟪(w : H), Δ v + (v : H)⟫_ℂ = 0 := by
      intro v
      have hfa : ⟪Δ.adjoint w, (v : H)⟫_ℂ = ⟪(w : H), Δ v⟫_ℂ :=
        LinearPMap.adjoint_isFormalAdjoint hdense w v
      rw [hw, inner_neg_left] at hfa          -- hfa : -⟪w, v⟫ = ⟪w, Δ v⟫
      rw [inner_add_right, ← hfa]; ring
    -- Surjectivity: `(1+Δ)` hits `w`, so `⟪w, w⟫ = 0`.
    obtain ⟨v, hv⟩ := hsurj (w : H)            -- hv : Δ v + v = w
    have hself : ⟪(w : H), (w : H)⟫_ℂ = 0 := by
      have := hortho v                          -- ⟪w, Δ v + v⟫ = 0
      rwa [hv] at this
    exact inner_self_eq_zero.mp hself
  -- Now `Δ† ≤ Δ` via `eqLocus`.
  apply LinearPMap.le_of_eqLocus_ge
  intro w hw
  set W : Δ.adjoint.domain := ⟨w, hw⟩ with hWdef
  -- Apply surjectivity to `h := Δ† W + w`.
  obtain ⟨x, hx⟩ := hsurj (Δ.adjoint W + w)        -- hx : Δ x + x = Δ† W + w
  have hxin : (x : H) ∈ Δ.adjoint.domain := (hsym.le_adjoint hdense).1 x.2
  have hxeq : Δ.adjoint (⟨(x : H), hxin⟩ : Δ.adjoint.domain) = Δ x :=
    ((hsym.le_adjoint hdense).2 (x := x) (y := ⟨(x : H), hxin⟩) rfl).symm
  -- `W' := W - ⟨x,_⟩` lies in `ker (1 + Δ†)`.
  set W' : Δ.adjoint.domain := W - ⟨(x : H), hxin⟩ with hW'def
  have hW'val : (W' : H) = w - (x : H) := rfl
  have hAW' : Δ.adjoint W' = -(W' : H) := by
    have e1 : Δ.adjoint W' = Δ.adjoint W - Δ x := by
      rw [hW'def, LinearPMap.map_sub, hxeq]
    -- `Δ† W - Δ x = Δ† W - (Δ† W + w - x) = x - w = -(w - x) = -(W' )`.
    rw [e1, hW'val]
    -- from `hx : Δ x + x = Δ† W + w` ⟹ `Δ x = Δ† W + w - x`.
    have hΔx : Δ x = Δ.adjoint W + w - (x : H) := by rw [← hx]; abel
    rw [hΔx]; abel
  have hWx : w = (x : H) := by
    have h0 : (W' : H) = 0 := hker W' hAW'
    rw [hW'val] at h0
    exact sub_eq_zero.mp h0
  -- Hence `w = x ∈ D(Δ)` and `Δ† w = Δ w`.
  subst hWx
  exact ⟨hw, x.2, hxeq⟩

end Spectra.TomitaTakesaki

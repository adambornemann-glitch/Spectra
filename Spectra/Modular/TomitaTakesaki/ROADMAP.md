# Tomita–Takesaki Modular Theory — Formalization Roadmap

A map of what it takes to turn `Spectra/Modular/TomitaTakesaki/Basic.lean` from a foundations +
axiomatized-bundle seed into a genuine construction of the modular operator `Δ`, the modular
conjugation `J`, and the two fundamental theorems. Mathlib references were checked against the local
source tree (`leanprover/lean4:v4.31.0-rc1`, `.lake/packages/mathlib/Mathlib/...`); names are real
unless flagged **MISSING**.

> How to read: items are grouped by tractability with a **difficulty** (`easy` ≈ hours,
> `medium` ≈ a day, `hard` ≈ multi-day, `research` ≈ needs genuinely new theory), the **Mathlib
> support** that exists, what is **missing**, and a **strategy**.

This file is the concrete (Hilbert-space) companion to the abstract C\*-side roadmap in
`Spectra/Modular/KMS/ROADMAP.md` (whose **Tier 4 / V2** entry names this construction as the
deferred research target). The abstract bundle there is `Spectra.KMS.ModularTheoryData`; the
concrete bundle here is `Spectra.TomitaTakesaki.ModularData`.

---

## Strategy (decided): the conjugate Hilbert space

The unbounded **antilinear** operators of the theory (the Tomita operator `S` and its adjoint `F`)
are handled by the **conjugate-space reduction**: an antilinear `S : H → H` is the same data as a
*linear* `S̃ : H →ₗ.[ℂ] Conj H`, where `Conj H` is the conjugate Hilbert space (same vectors, with
`c • x = c̄ • x` and `⟪x,y⟫ = ⟪y,x⟫`). The graph of `S̃` **is** a `ℂ`-submodule of `H × Conj H`
(unlike the graph of `S`, which is not a `ℂ`-submodule of `H × H`), so Mathlib's *linear*
`LinearPMap.{graph, IsClosable, closure, adjoint, IsSelfAdjoint}` apply to `S̃` verbatim, and
`F = S̃†`, `Δ = S̃†∘S̃` come out as genuine (linear) operators. Two other strategies were considered
and rejected: porting a σ-general antilinear `LinearPMap` theory (duplicates Mathlib, graph isn't a
submodule) and real-linearification (loses the complex spectral calculus).

## 0. Current status (done, green — `#print axioms`-clean)

- **M0 — the conjugate Hilbert space `Conj E`** (`Spectra/SpectralTheory/Antilinear/ConjugateSpace.lean`,
  `Spectra.Conj`): the type synonym `Conj E := E` with the conjugated `ℂ`-module and inner product,
  inheriting `E`'s additive/normed/complete structure; the **antiunitary equivalence**
  `Conj.toConjₗᵢ : E ≃ₗᵢ⋆[ℂ] Conj E`; and the `ofConj`/`toConj` API. Verified: for
  `S : H →ₗ.[ℂ] Conj H`, Mathlib's `S.adjoint`, `S.IsClosable`, and `S.adjoint.comp S` all
  typecheck — the reduction is fit for purpose.

- **R1 engine — `borelCalculus` → `OneParameterUnitaryGroup`**
  (`Spectra/CayleyTransform/UnitaryGroup.lean`, `Spectra.BorelCFC.borelUnitaryGroup`): a unimodular,
  multiplicative, parameter-continuous symbol family is packaged into a strongly continuous
  one-parameter unitary group (strong continuity from the existing dominated-convergence engine).
  This is the reusable core for `Δ^{it}` (and `e^{itA}`); only the specific symbol remains (see R1).

All in `Basic.lean`, depending only on `[propext, Classical.choice, Quot.sound]`:

- **Cyclic & separating vectors** — `IsCyclic M Ω` (density of the span of `M Ω`) and
  `IsSeparating M Ω` (`T ∈ M`, `T Ω = 0 ⟹ T = 0`). These notions are **missing from Mathlib** and
  are supplied here, together with the helper set `cyclicSet`.
- **The cyclic ↔ separating duality (easy direction)** —
  `isSeparating_commutant_of_isCyclic : IsCyclic M Ω → IsSeparating M.commutant Ω`, via the
  commutation `S T' = T' S` (`mem_commutant_iff`) and continuity-on-a-dense-span
  (`ContinuousLinearMap.ext_on`); plus the corollary
  `isSeparating_of_isCyclic_commutant` (uses `commutant_commutant`, i.e. `M'' = M`).
- **`J`-conjugation** — `jConj J x = J ∘ x ∘ J⁻¹` for an antiunitary `J : H ≃ₗᵢ⋆[ℂ] H`, landing in
  `H →L[ℂ] H` (antilinear ∘ linear ∘ antilinear is linear, via the
  `RingHomCompTriple (starRingEnd ℂ) (starRingEnd ℂ) (RingHom.id ℂ)` instance), with `jConj_apply`.
- **The output bundle** `ModularData M Ω` (axiomatized, honest caveats) — fields for `J`, the
  modular flow `Δ^{it}` (a `Spectra.OneParameterUnitaryGroup H`), `J² = 1`, `J Ω = Ω`,
  `Δ^{it} Ω = Ω`, Tomita's theorem `Δ^{it} M Δ^{-it} = M` (into + onto), and the commutation
  theorem `J M J = M'` (membership form). Projections: `modularAutomorphism_mem`, `symm_J`
  (`J⁻¹ = J`), and `jConj_commutant_mem` (`J M' J = M`).

**Caveat (by design):** `ModularData` is *uninhabited* until a real construction supplies it —
exactly the status of `Spectra.KMS.ModularTheoryData` on the C\*-side. `Δ` and `J` are not built;
the fields are the defining properties a construction must discharge.

---

## Mathlib inventory (quick reference)

| Need | Mathlib status | Where |
|---|---|---|
| von Neumann algebra (concrete) | ✅ `VonNeumannAlgebra H` (= `StarSubalgebra` equal to its bicommutant), `SetLike`/`SubringClass`/`StarMemClass` | `Analysis/VonNeumannAlgebra/Basic.lean` |
| commutant + bicommutant | ✅ `VonNeumannAlgebra.commutant`, `mem_commutant_iff`, `commutant_commutant`, `coe_commutant` | same |
| abstract W\*-algebra | ✅ `WStarAlgebra` (Sakai predual) | same |
| cyclic / separating vectors | ❌ MISSING — **supplied here** (`IsCyclic`, `IsSeparating`) | — |
| continuous-linear ext on dense span | ✅ `ContinuousLinearMap.ext_on` | `Topology/Algebra/Module/ContinuousLinearMap/Basic.lean` |
| antiunitary (antilinear isometric equiv) | ✅ `H ≃ₗᵢ⋆[ℂ] H` = `LinearIsometryEquiv (starRingEnd ℂ)` | `Analysis/Normed/Operator/LinearIsometry.lean` |
| conj∘conj = id comp triple | ✅ `RingHomCompTriple … (RingHom.id ℂ)` from `RingHomInvPair (starRingEnd ℂ) (starRingEnd ℂ)` | `Algebra/Ring/CompTypeclasses.lean`, `Algebra/Star/Basic.lean` |
| unbounded operators (`LinearPMap`) | ✅ semilinear `LinearPMap σ E F` (`→ₛₗ.[σ]`); closure/adjoint/`IsSelfAdjoint` **only for `σ = RingHom.id`** | `LinearAlgebra/LinearPMap.lean`, `Analysis/InnerProductSpace/LinearPMap.lean` |
| GNS construction | ✅ `PositiveLinearMap.GNS`, `gnsStarAlgHom`, `PreGNS` | `Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` |
| CFC, `sqrt`, `rpow` (bounded ops) | ✅ `CFC.sqrt`, `CFC.rpow` | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/*`, `…/Rpow/Basic.lean` |
| one-parameter unitary group + Stone | ✅ project: `Spectra.OneParameterUnitaryGroup`, `generator`, `Spectra.Stone.*` | `Spectra/OneParameterUnitaryGroup/`, `Spectra/Stone/` |
| **antilinear** unbounded operators (`S`, `F`) | ✅ **reduced to linear** via `Conj` (M0) — `S̃ : H →ₗ.[ℂ] Conj H` gets Mathlib's `adjoint`/`closure` | `Spectra/SpectralTheory/Antilinear/ConjugateSpace.lean` |
| **polar decomposition** (bounded *or* unbounded) | ❌ MISSING | — |
| Borel calculus → `Δ^{it}` (unimodular symbol, bounded) | 🟡 **mostly have it** — project `borelCalculus` (Cayley) handles bounded symbols `λ ↦ λ^{it}`; package as a unitary group | `Spectra/CayleyTransform/BorelCalculus.lean` |
| **unbounded** functional calculus → `Δ^{½}`, `Δ^{-½}` (unbounded symbols) | ❌ MISSING — extend `borelCalculus` to unbounded symbols / integrate against `spectralPVM` | `Spectra/CayleyTransform/`, `Spectra/SpectralTheory/ResolventForm.lean` |
| Tomita–Takesaki (`Δ`, `J`, modular flow) | ❌ MISSING (this directory is the target) | — |

---

## Tier 1 — Structural wins (easy–medium, no new analysis)

- **E1. Converse duality (full equivalence).** ✅ **DONE**
  (`Spectra/Modular/TomitaTakesaki/Duality.lean`, `#print axioms`-clean):
  `isCyclic_commutant_of_isSeparating : IsSeparating M Ω → IsCyclic M.commutant Ω`, and the full
  `isCyclic_commutant_iff_isSeparating`. Proof: `P =` orthogonal projection
  (`Submodule.starProjection`) onto `K = closure(M' Ω)`; `K` is `M'`-invariant
  (`Set.MapsTo.closure` of the span-level invariance), so `P ∈ M` by the bicommutant
  (`VonNeumannAlgebra.IsStarProjection.mem_iff`); then `1 - P ∈ M` kills `Ω` (as `Ω ∈ K`), so
  **separation** forces `P = 1`, i.e. `K = ⊤`, i.e. cyclic.
- **E2. `ModularData` consumption lemmas.** From the bundle, derive that
  `σ_t : x ↦ Δ^{it} x Δ^{-it}` is a `*`-automorphism of `M` (multiplicative, unital, star- and
  norm-preserving, group law in `t`), packaged as a bundled automorphism. Difficulty: **easy–medium**.
- **E3. `J` maps the vector state to itself / `Δ^{it}` fixes it.** Vacuum-fixing fields already
  bundled; derive the vector-state invariance `ω(σ_t x) = ω(x)` where `ω(x) = ⟪Ω, x Ω⟫`.
  Difficulty: **easy**.

## Tier 2 — Bridges (medium)

- **M1. GNS bridge `state → (M, Ω)`.** From a faithful normal state (the abstract input of
  `Spectra.KMS.FaithfulNormalState`), produce the concrete data: `M := π(A)''` acting on the GNS
  space, `Ω :=` the cyclic vector, and prove `Ω` is cyclic (GNS) and separating (faithfulness).
  This is the formal link between `ModularData` and `ModularTheoryData`. Difficulty: **medium**,
  uses the project's GNS development (`Spectra/Bochner/GNS/`, `Spectra.KMS.State.gnsSpace`).
- **M2. KMS at β = 1.** Show the vector state is KMS at `β = 1` for `σ_t` and connect to
  `Spectra.KMS.IsKMSState` / `isKMSState_iff_imaginaryTime`. Difficulty: **medium**, **blocked**
  partly on M1 and on relating `Δ^{it}`'s analytic structure to the KMS strip.

## Tier 3 — The Tomita operator `S`, its adjoint `F`, and `Δ = S*S` (medium–hard; **unblocked** by M0)

The conjugate-space reduction (M0) removes the old blocker: `S` is the *linear*
`S̃ : H →ₗ.[ℂ] Conj H`, so Mathlib's `LinearPMap` theory applies.

- **H1. The Tomita operator `S̃` and its adjoint `F`.** ✅ **DONE**
  (`Spectra/Modular/TomitaTakesaki/TomitaOperator.lean`, all `#print axioms`-clean):
  - `tomitaOp M Ω : H →ₗ.[ℂ] Conj H` — the *linear* `S̃`, built from its graph
    `{(x Ω, x⋆ Ω) : x ∈ M}` via `Submodule.toLinearPMap`. The graph is **functional** exactly
    because `Ω` is separating (`tomitaGraph_functional`). Helpers `evalAt` (`T ↦ T Ω`) and `tomitaPre`
    (`T ↦ toConj (T⋆ Ω)`, proved genuinely ℂ-linear — the two conjugations cancel).
  - `tomitaOp_apply` — the defining property `S̃ (x Ω) = x⋆ Ω` (in `Conj H`), under separating.
  - `tomitaOp_domain_eq_span` / `tomitaOp_domain_dense` — domain `= span (M Ω)`, **dense** under
    `IsCyclic` (so the adjoint is genuine).
  - `tomitaAdjoint M Ω := (tomitaOp M Ω).adjoint : Conj H →ₗ.[ℂ] H` — the second Tomita operator `F`.
- **H2. Closability `IsClosable S̃` / closure `S`.** ✅ **DONE**
  (`Spectra/Modular/TomitaTakesaki/Closable.lean`, `#print axioms`-clean):
  `tomitaOp_isClosable : IsCyclic M Ω → IsSeparating M Ω → (tomitaOp M Ω).IsClosable`, and the
  closure `tomitaClosure M Ω := (tomitaOp M Ω).closure` (the genuine modular `S`). Proof: `S̃ ≤ S̃††`
  with `S̃††` closed (`adjoint_isClosed`); the input `Dense S̃†.domain` comes from
  `toConj_mem_adjoint_domain` (every `toConj (b Ω)`, `b ∈ M'`, is in `S̃†.domain` because the
  functional `x ↦ ⟪toConj (b Ω), S̃ x⟫` equals the bounded `x ↦ ⟪b⋆ Ω, x⟫` — the **commutation**
  `inner_star_comm`, proved by span-induction `inner_tomitaOp_eq`), with these vectors dense via E1
  transported through the antiunitary `Conj.toConjₗᵢ`.
- **H3. `Δ = S⋆ S` self-adjoint, `≥ 0`** — **von Neumann's `T⋆T` theorem.**
  - ✅ **Setup done** (`Spectra/Modular/TomitaTakesaki/ModularOperator.lean`, `#print axioms`-clean):
    `S = tomitaClosure M Ω` is **closed** (`tomitaClosure_isClosed`) and **densely defined**
    (`tomitaClosure_domain_dense`), and the modular form is **non-negative**
    (`modularForm_nonneg`, `modularForm_eq_norm_sq`: `⟪Sx,Sx⟫ = ‖Sx‖²`). These are exactly von
    Neumann's hypotheses + `Δ ≥ 0`.
  - ⏳ **The theorem itself — to be PROVED, not bundled** (see Tier 5 for the concrete plan).
    It is **assemblable from Mathlib's graph machinery** (the orthogonal-complement-of-the-flipped-
    graph adjoint is already there), not a build-from-nothing. The chain `M0→R1→H1→E1→H2` has reduced
    the modular operator's existence to exactly this one classical theorem. Difficulty: **hard**
    (multi-lemma assembly), but tractable.

## Tier 4 — `Δ^{it}`, `Δ^{½}`, polar decomposition, and the theorems

- **R1. `Δ^{it}` as a `OneParameterUnitaryGroup`.** ✅ **DONE**
  (`Spectra/CayleyTransform/UnitaryGroup.lean`, all `#print axioms`-clean).
  - **Engine** `Spectra.BorelCFC.borelUnitaryGroup`: any **unimodular, multiplicative, continuous**
    symbol family `g : ℝ → spectrum ℂ V → ℂ` packages, via `borelCalculus`, into a
    `OneParameterUnitaryGroup H`. Unitarity ← `borelCalculus_adjoint` + unimodularity; group law ←
    `borelCalculus_mul`; identity ← `borelCalculus_one`; **strong continuity** ←
    `tendsto_borelCalculus_apply` (dominated convergence).
  - **Modular flow** `Spectra.BorelCFC.borelModularGroup V hn : OneParameterUnitaryGroup H`, the
    instance at the **modular symbol** `modularSymbol V t z = exp(i t · log (inverseMobius z).re)`
    (= `λ^{it}` in exp form; symbol lemmas: `measurable_`/`norm_`/`modularSymbol_zero`/`_add`/
    `continuous_modularSymbol`). `modularSymbol_eq_cpow` proves it is the genuine `(↑λ)^{it}` on a
    positive pulled-back spectral value, so `borelModularGroup` is `Δ^{it}` of the operator whose
    Cayley transform is `V` (the modular flow once that operator is positive self-adjoint).
  - **Link remaining:** feed `V := cayleyTransform Δ` once `Δ` exists (H1–H3); positivity of `Δ`
    gives `0 < (inverseMobius z).re`, making `modularSymbol_eq_cpow` fire — then `borelModularGroup`
    is literally `Δ^{it}` and inhabits `ModularData.modularFlow`.
- **R2. `Δ^{½}`, `Δ^{-½}` via unbounded functional calculus.** ❌ The remaining calculus gap:
  `borelCalculus` is bounded-symbol only; `√λ`, `λ^{-½}` are unbounded. Extend it to unbounded
  symbols, or integrate against `spectralPVM hΔ`. Needed only for the polar decomposition, **not**
  for `Δ^{it}`. Difficulty: **hard**.
- **R3. Polar decomposition `S = J Δ^{½}`; extract `J`.** ❌ MISSING in Mathlib for any operator
  class. With `Δ^{½}` (R2) and the conjugate-space picture, `J` is the partial isometry of `S̃`
  composed with `Conj H ≅ H`; it lands in the bounded `Conjugation` type. Difficulty: **research**.
- **R4. The fundamental theorems.** Discharge `modularFlow_maps_into`, `modularFlow_maps_onto`,
  `modularConjugation_eq_commutant` — i.e. *construct* a `ModularData M Ω`. Capstone:
  `tomitaTakesaki_exists : IsCyclic M Ω → IsSeparating M Ω → Nonempty (ModularData M Ω)`.

---

## Tier 5 — von Neumann's `T⋆T` theorem (the concrete plan to discharge H3)

**Goal:** construct `Δ = S⋆ S` (`S = tomitaClosure M Ω`) as a self-adjoint, non-negative operator —
*proved, not axiomatized*. Mathlib already supplies the hard graph-geometry; this is an assembly.

**Mathlib pieces in hand** (all verified present):
- `LinearPMap.graph`, and `S.IsClosed` (H2) `= S.graph` closed; closed ⟹ `HasOrthogonalProjection`.
- `Submodule.adjoint g := (skewSwap-image of g)ᗮ` with `LinearEquiv.skewSwap R M N x = (-x.2, x.1)`,
  and **`LinearPMap.adjoint_graph_eq_graph_adjoint : T†.graph = T.graph.adjoint`** — i.e. the
  orthogonal complement `Γ(S)ᗮ` is exactly the (skew-swapped) graph of `S⋆`. This is the crux fact
  von Neumann's proof needs, and it is *given*.
- `Submodule.sup_orthogonal_of_hasOrthogonalProjection : Γ ⊔ Γᗮ = ⊤`, `Submodule.orthogonalProjection`,
  `Submodule.mem_adjoint_iff`.

**Proof skeleton** (each step a lemma):
1. **`V1. graphProjection`** — `Γ := S.graph` is closed (H2), so `(h, 0) ∈ H × Conj H` decomposes
   uniquely as `(x, S x) + q` with `(x, Sx) ∈ Γ`, `q ∈ Γᗮ` (`sup_orthogonal… = ⊤`).
2. **`V2. orthocomplement form`** — via `adjoint_graph_eq_graph_adjoint` + `skewSwap`, `q = (-S⋆g, g)`
   for a unique `g ∈ D(S⋆)`. Matching second components: `g = -S x`, so `S x ∈ D(S⋆)`
   (⟹ `x ∈ D(S⋆S)`); matching first: `h = x + S⋆(S x) = (1 + Δ) x`.
3. **`V3. one_add_TstarT_surjective`** — hence `1 + Δ` is **surjective**; the solution map
   `R : h ↦ x` is the first component of `orthogonalProjection Γ (h,0)`, so `‖R h‖ ≤ ‖h‖`
   (bounded, everywhere-defined inverse of `1 + Δ`).
4. **`V4. Δ symmetric & ≥ 0`** — `⟪Δx,y⟫ = ⟪Sx,Sy⟫ = ⟪x,Δy⟫` and `⟪Δx,x⟫ = ‖Sx‖² ≥ 0`
   (`modularForm_nonneg` already covers the form).
5. **`V5. Δ self-adjoint`** — symmetric `+ (1+Δ)` bijective-with-bounded-inverse ⟹ self-adjoint
   (a densely-defined symmetric operator with `(1+Δ)` onto is self-adjoint), via the project's
   `isSelfAdjoint_of_surjective_addSub` (deficiency criterion) or directly from `R`.
6. **`V6. modularOp`** — package `Δ : H →ₗ.[ℂ] H` with `IsSelfAdjoint Δ` and `Δ ≥ 0`; *this is the
   theorem that discharges H3*, with **no new axioms**.

Forming `Δ` as a `LinearPMap` (the `LinearPMap.comp` domain obstruction) is handled by `V2`: its
domain is exactly `{x ∈ D(S) : S x ∈ D(S⋆)}`, the first projection of `Γ ∩ (decomposition)`; build
via `S⋆.comp (S.domRestrict …)` or directly from the graph. Once `Δ` is self-adjoint and `≥ 0`,
`Δ^{½}` and `Δ^{it}` come from the `CayleyTransform` calculus (R1/R2), unblocking R3–R4.

---

## Discharging axioms — the standing rule (no permanent bundling)

**Bundled/axiomatized data in this development is a debt to be paid, not a resting state.** Each
must have a *discharge plan* and ultimately a *constructor*; we do not accept standing axioms.

| Bundled item | Where | Discharge route |
|---|---|---|
| `ModularData M Ω` (J, `Δ^{it}`, `Δ^{it}MΔ^{-it}=M`, `JMJ=M'`) | `Basic.lean` | `tomitaTakesaki_exists` (R4): a *constructor* from `IsCyclic`+`IsSeparating`, built on Tier 5 + R1–R3. Then `ModularData` is an *inhabited* structure, not an axiom. |
| `Δ = S⋆S` self-adjoint `≥ 0` | this milestone (H3) | **Tier 5** above — proved from Mathlib's graph machinery. |
| `Spectra.KMS.ModularTheoryData A ω` (abstract `Dynamics` + KMS@1) | `KMS/Modular.lean` | construct from the concrete `ModularData` via GNS (the `(M,Ω)`↔faithful-normal-state bridge, Tier 2 M1). |
| `State.IsNormal := True` (`KMS/Modular.lean`) | `KMS/Modular.lean` | genuine σ-weak/order-continuity definition once a predual/topology is fixed (KMS ROADMAP §4 V1). |

---

## Recommended order

0. ✅ **M0** (conjugate space), **R1** (`Δ^{it}` engine + modular flow), **H1** (`S̃`, `F`),
   **E1** (cyclic↔separating duality), **H2** (closability, the closed `S`), **H3-setup** (`S` closed +
   densely-defined, non-negative form) — **all done, sorry-free.**
1. **Tier 5 — von Neumann's `T⋆T` theorem** → discharges **H3** (`Δ = S⋆S` self-adjoint `≥ 0`). The
   single hard analytic input; now grounded as an assembly of Mathlib's graph/adjoint/orthogonal
   machinery. **This is the next target.**
2. **R2** (`Δ^{½}` via the `CayleyTransform` calculus) and **R3** (polar decomposition `S = J Δ^{½}`).
3. **R4** — the capstone `tomitaTakesaki_exists`, which *constructs* (not bundles) a `ModularData`,
   discharging the `Basic.lean` bundle.
4. In parallel: structural wins **E2–E3**, the **M1–M2** GNS bridges to `Spectra.KMS` (which discharge
   `ModularTheoryData`), and the `State.IsNormal` placeholder. See the discharge table above — the
   aim is zero standing axioms.

## Gaps worth upstreaming to Mathlib

- The conjugate Hilbert space `Conj E` + the antiunitary `E ≃ₗᵢ⋆[ℂ] Conj E` (supplied in M0;
  upstreamable). It is the clean way to give Mathlib's *linear* `LinearPMap` theory access to
  antilinear operators — preferable to a bespoke `σ`-general antilinear closure/adjoint theory.
- von Neumann's `T*T` theorem (`A†∘A` self-adjoint for closed densely-defined `A`) for `LinearPMap`.
- Polar decomposition of closed operators (bounded and unbounded).
- Borel functional calculus / spectral measure for unbounded self-adjoint operators (unbounded
  symbols) — the project's `CayleyTransform` Borel calculus covers the bounded-symbol case.
- Cyclic / separating vectors for `VonNeumannAlgebra` (supplied in `Basic.lean`; upstreamable).

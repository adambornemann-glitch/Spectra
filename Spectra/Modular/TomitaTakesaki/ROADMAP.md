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
  - ✅ **PROVED, not bundled (2026-06-29)** — `Spectra/Modular/TomitaTakesaki/VonNeumannTstarT.lean`,
    sorry-free, `#print axioms`-clean, in the root `Spectra` import + `AxiomCheck` gate:
    `modularOp_isSelfAdjoint : IsCyclic M Ω → IsSeparating M Ω → IsSelfAdjoint (modularOp M Ω)`,
    plus `modularOp_nonneg` (`Δ ≥ 0`). Assembled from Mathlib's graph machinery
    (`LinearPMap.adjoint_graph_eq_graph_adjoint` + `Submodule.adjoint`/`skewSwap` +
    `sup_orthogonal_of_hasOrthogonalProjection`) exactly as planned in Tier 5. **H3 discharged.**

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
- **R2. `Δ^{½}` via unbounded functional calculus.** ✅ **DONE (operator + isometry).** The
  unbounded calculus `pmapOfPVM U_grp f` (`Spectra/SpectralTheory/Calculus/PMapOfPVM.lean`,
  sorry-free, axiom-gated) integrates a measurable symbol against a PVM on its natural `L²` domain;
  the `√`-form identity `‖A^{½}x‖² = Re⟪x,Ax⟫` is `norm_sq_pmapOfPVM_sqrt`
  (`…/Calculus/PMapSquareRoot.lean`). The **modular square root**
  `modularSqrt := pmapOfPVM (genToGroup Δ) √` (`Spectra/Modular/Cocycle/ModularSqrt.lean`) is `≥ 0`,
  and the polar isometry `‖Δ^{½}x‖ = ‖S x‖` is `norm_modularSqrt_eq_norm_tomita`. **Still open
  (R2-completion):** `Δ^{½}` *self-adjoint* (natural domain maximal) and the *product law*
  `(Δ^{½})² = Δ` — generic spectral-calculus facts; both are the only blocker for the source
  density `Δ^{½}(D(Δ))` in R3.
- **R3. Polar decomposition `S = J Δ^{½}`; extract `J`.** ✅ **DONE**
  (`Spectra/Modular/Cocycle/PolarIsometry.lean`, sorry-free, axiom-gated). Route:
  `W = LinearEquiv.extendOfIsometry (Δ^{½}x ↦ S x)`, then `J = ofConj ∘ W`. `extendOfIsometry` takes
  the isometry (R2 `norm_modularSqrt_eq_norm_tomita`) plus two density inputs:
  - `inj`: `tomitaClosure_injective` (`ker S = 0`, from `S⋆(toConj bΩ) = b⋆Ω` via `S ≤ S₀⋆⋆` + density
    of `M'Ω`) and `modularOp_injective` (`ker Δ = 0`).
  - `denserange` (target): `tomitaClosure_range_dense` and `denseRange_tomitaOnModularDomain`
    (`S(D(Δ))` dense = *`D(Δ)` a core for `S`*), from the surjectivity of `1 + Δ`
    (`one_add_modularOp_surjective`).
  - `denserange` (source): `denseRange_modularSqrtOnModularDomain` (`Δ^{½}(D(Δ))` dense). Proved by a
    **direct spectral argument** — for `y ⊥ Δ^{½}(D(Δ))`, the cut-offs `E([0,n])y ∈ D(Δ)` give
    `∫_{[0,n]} √s dμ_y = 0`, so `μ_y((0,∞)) = 0`; `Δ ≥ 0` gives `μ_y((-∞,0)) = 0`; `ker Δ = 0` gives
    `μ_y({0}) = 0`; hence `‖y‖² = μ_y(ℝ) = 0`. **Crucially this AVOIDS the product law `(Δ^{½})² = Δ`
    and `Δ^{½}` self-adjointness** — it uses only spectral facts about the already-self-adjoint `Δ`
    (bounded-calculus multiplicativity against `E(B)`, `μ_{E(B)ξ} = μ_ξ|_B`, `E((-∞,0)) = 0`).
  - **Capstone:** `modularW : H ≃ₗᵢ[ℂ] Conj H` (the unitary `W`), `modularConjugation : H ≃ₗᵢ⋆[ℂ] H`
    (the antiunitary `J = ofConj ∘ W`), and `tomita_eq_modularConjugation_modularSqrt` — the polar
    decomposition `S = J Δ^{½}` (`toConj (J (Δ^{½} x)) = S x`).
  - *Still open downstream:* `J² = 1`, `J Ω = Ω` (the `Jrel` node, Tomita involution `S² ⊆ 1`) and the
    commutation `J M J = M'` — both R4 / `ModularData`-inhabitation. The product law `(Δ^{½})² = Δ`
    remains an open (but now non-blocking) R2 nicety.
- **R4. Inhabit `ModularData` — the fundamental theorems.** Discharge the 6 remaining fields and the
  capstone `tomitaTakesaki_exists : IsCyclic M Ω → IsSeparating M Ω → Nonempty (ModularData M Ω)`.
  **Derisked (2026-06-30, 3-agent recon — codebase inventory + literature survey + adversarial audit).
  Staged plan (each stage a gateable, sorry-free deliverable):**
  - **R4a — Ω-invariances + `J²=1`. 🟢 FIELDS 4 & 5 DONE; `J²=1` (field 3) remains.**
    `Spectra/Modular/Cocycle/ModularVacuum.lean` (sorry-free, axiom-gated): `modularOp_vacuum`
    (`ΔΩ=Ω`), `modularSqrt_vacuum` (`Δ^{½}Ω=Ω`), **`modularConjugation_fixes_vacuum` (`JΩ=Ω`, field 4)**.
    **Field 5 `Δ^{it}Ω=Ω` DONE 2026-07-01** — `Spectra/Modular/Cocycle/ModularFlowVacuum.lean`
    (`modularFlow_fixes_vacuum`, sorry-free, axiom-clean, gated, build 4106). **Route B, NOT the
    anticipated `V`-eigenvector→Dirac lemma:** the memory-noted blocker was sidestepped by the already-
    proven UNCONDITIONAL bridge `spectralCalculus_stoneGroup_eq_borelCalculus` (StoneBridge/CalculusBridge)
    + `stoneGroup_eq_genToGroup` (Stone), which recasts `modularFlow.U t` as
    `spectralCalculus (genToGroup Δ) (logExpSym t)` on `Δ`'s OWN group; the spectral atom `E_Δ({1})Ω=Ω`
    (`spectralProjection_singleton_one_vacuum`) then collapses it since `logExpSym t 1 = exp(it·log 1)=1`
    (a limit-free clone of `modularSqrt_atom_apply`). Stated unconditionally (Subsingleton case by
    `Subsingleton.elim`; Nontrivial branch supplies the `stoneGroup=genToGroup` instance).
    **Field 3 `J²=1`: FOUNDATION DONE (2026-07-01, `Spectra/Modular/Cocycle/ModularInvolution.lean`,
    sorry-free, gated, build 4107)** — the Tomita involution `S̃²=1` on the core `MΩ`
    (`sTilde_involutive_core`: `S̃(aΩ)=(star a)Ω`, the `S²⊆1` seed via `tomitaOp_apply`×2 + `star_star`,
    no `Δ`/`J`/adjoint theory) + polar helper `modularConjugation_apply_modularSqrt` (`J(Δ^{½}x)=ofConj(Sx)`).
    **CRUX OPEN (L5 `J(J(Δ^{½}x))=Δ^{½}x`, adversarially confirmed genuinely blocked):** core `MΩ` carries
    `S̃²=1` but `MΩ⊄D(Δ)`; `range Δ^{½}` carries the polar relation but not the involution — the dense sets
    don't align. Close via **(A)** closed-operator `S̃²⊆1` + `S̃(D(Δ))⊆D(S)` (conjecturally avoids Δ^{½}
    self-adjointness), or **(B)** `(Δ^{½})²=Δ` self-adjointness (open R2 node) + polar-decomposition
    uniqueness; then `DenseRange.equalizer` closes `∀x, J(Jx)=x`. *Original plan below:* All flow from
    `Ω` being a `Δ`-eigenvector
    at `1`: `SΩ = toConj Ω` (`tomitaOp_apply` at `T=1∈M`) and `S⋆(toConj Ω) = Ω`
    (`tomitaAdjoint_apply_commutant` at `b=1∈M'`) give **`ΔΩ = Ω`**; then the single spectral lemma
    `ΔΩ=Ω ⟹ μ_Ω = ‖Ω‖²δ₁ ⟹ f(Δ)Ω = f(1)Ω` (reuse `spectralPVM_proj_singleton_eq_self_of_eigen` +
    the `denseRange_modularSqrt` machinery) yields **`Δ^{½}Ω = Ω`** (field 5 prereq), **`Δ^{it}Ω = Ω`**
    (`modularFlow_fixes_vacuum`, field 5; `Δ^{it}` via the Cayley picture — `Ω` a `V`-eigenvector at
    `-i`, `modularSymbol(·,t) = 1`), and **`JΩ = Ω`** (`J_fixes_vacuum`, field 4: `JΩ = J(Δ^{½}Ω) =
    ofConj(SΩ) = Ω`). `J² = 1` (field 3, MEDIUM) needs the involution `S² ⊆ 1` + polar uniqueness; no
    shortcut isolates it from `JΔJ = Δ^{-1}` (they come as a package). Enabling lemma:
    `tomitaClosure.adjoint = tomitaOp.adjoint` (adjoint of closure = adjoint; graph argument).
  - **R4b/c/d/e — Tomita's theorem (6,7) + commutation (8): ★ port Rieffel–van Daele.** The literature
    survey is decisive: the **bounded two-real-subspaces** proof (Rieffel–van Daele, *Pacific J. Math.*
    69 (1977)) is the ONLY route avoiding operator-valued Fourier/Mellin transforms, Carlson's theorem,
    analytic-element calculus, and unbounded-operator analytic continuation. Construction: `K =
    closure(M_sa Ω)` (a closed real subspace), `iK`, projections `P, Q`, `R = P + Q ∈ [0,2]` with
    `R, 2−R` injective; `J` = unitary part of the polar decomposition of the **bounded** self-adjoint
    `P − Q` (so `J² = 1` is bounded polar algebra), and `Δ = (2−R) R^{-1}` — an **unbounded**
    functional-calculus object (`0 ∈ σ(R)` in the cyclic-separating case), built via the project's
    `pmapOfPVM` on `R`'s PVM, **not** bounded CFC. The entire analytic content reduces to ONE
    Hahn–Banach/Sakai-Radon–Nikodym lemma (RvD Lemma 4.3, on the predual) + ONE scalar Cauchy-residue
    (Lemma 4.6, reusing the project's Morera/strip tooling). **Keystone risk:** the bridge
    `(J, Δ)_ours = (J, R)_RvD` (spectral; **must land AFTER 4.3**, else circular via the `Re λ=1`
    modular line). **Long pole:** the von Neumann predual `M = (M_*)^*` behind Lemma 4.3.
    **Effort (2026-06-30 deep plan, 10-agent + 3 adversarial reviews; DISCHARGE-FIRST): FT + cocycle
    land UNCONDITIONALLY via the R1 trace-class predual ~32–42 pw ≈ 8–10 months** — no conditional
    milestone (Adam rejected the `NormalRadonNikodym` interface). Staged: P-audit (0.5) → residue 4.6
    (2–3, parallel) → bridge `Δ_R=Δ_our` (2–3) → assemble Thm 4.2 (2–2.5, *proved from* Lemma 4.3) →
    `tomitaTakesaki_exists` (1) → cocycle proper on `M₂(M)` (3–5); the discharge spine (P2 trace-class +
    P3 predual/Sakai/RN, which *proves* Lemma 4.3) runs first/underneath.
  - **R4f (downstream bonus).** With `σ_t(M)=M` in hand, the vector state's modular/KMS condition (β=1)
    becomes a clean *corollary* connecting to the existing `KMS/` Morera work — NOT a route to the
    theorem (KMS does not shortcut it; establishing KMS needs the same analytic floor).
  - *Deep breakdowns in the vault Canvases: R4/R5 in
    `Projects/Modular Theory/Fundamental Theorem and Cocycle.canvas`; the **predual sub-project** in
    `Projects/Modular Theory/Von Neumann Predual.canvas` (2026-06-30 deep plan).* RvD ingredient status:
    real subspaces + `Submodule.starProjection` **ready**; scalar residue (Lemma 4.6) **buildable**
    (Mathlib `CauchyIntegral` + `KMS/PeriodicStrip`, but there is **no `residue` object** — assemble by
    hand, ~2–3pw). **Corrections from the adversarial review:** (1) the bounded polar decomposition
    `T=U|T|` is **MISSING from Mathlib** (from-scratch partial isometry, ~3–4pw), not "easy 1–2wk";
    (2) the "single-vector Ω-relative RN that avoids trace-class" is **provably FALSE in the type III
    case** — on-the-nose surjectivity `P_𝒦(x'Ω)∈M_sa Ω` needs σ-weak Alaoglu = the full trace-class
    duality; it survives only as a **kill-criterion spike**, never a route; (3) the
    `instance WStarAlgebra (H →L[ℂ] H)` **does not exist** (`VonNeumannAlgebra/Basic.lean:64` is a
    future-tense TODO) — building it *is* the predual work. **Do NOT axiomatize Lemma 4.3, and (Adam's
    decision, 2026-06-30) do NOT ship it as a conditional theorem either.** DISCHARGE-FIRST: build the
    predual, whose non-commutative Radon–Nikodym theorem *proves* Lemma 4.3, so the fundamental theorem +
    cocycle land **UNCONDITIONALLY** — sorry-free, axiom-clean. **Single true blocker = the von Neumann
    predual** (`TraceClass H` → `B(H)=(TC)^*` σ-weak → Sakai `M=(M_*)^*` → non-comm RN), ~32–42pw.
    **Q1 SETTLED = CONCRETE:** the certified target is the concrete `M ⊆ B(H)` FT + cocycle (vector states,
    provably order-continuous ⟹ genuinely inhabits the bundles); the abstract `[WStarAlgebra]` statement is
    a later GNS corollary, off the critical path.

- **R5. The Connes RN cocycle (2×2 balanced weight) — NO research gaps; engineering.** After R4 inhabits
  `ModularData`, the chain is `E2` (σ_t as `*`-automorphism) → `M3/M1` (GNS bridge) → `AMP` (M₂(M)) →
  `BAL` (balanced state θ, Ω_θ) → `MTH` (ModularData(M₂(M),Ω_θ)) → `COC` (extract `u_t` from
  `σ^θ_t(e₂₁)=u_t⊗e₂₁`; inhabit `ConnesCocycle`, `KMS/Modular.lean`) → `CHN` (chain rule) → capstone
  **`connesCocycle_exists`**. **Parallelizable NOW, off the R4 gate:** `M1` GNS bridge
  (`FaithfulNormalState → (π(A)'', Ω)` cyclic+separating; GNS fully done, MED), `AMP` (`SpikeM2` seed →
  keystone `commutant_M2` bicommutant, MED 2–4d), `BAL` (MED 2–3d). Post-gate COC/CHN/CAP are pure
  matrix algebra (~1–2wk, low-risk). Full breakdown: same Canvas.

---

## Tier 5 — von Neumann's `T⋆T` theorem (the concrete plan to discharge H3)

**Goal:** construct `Δ = S⋆ S` (`S = tomitaClosure M Ω`) as a self-adjoint, non-negative operator —
*proved, not axiomatized*. Mathlib already supplies the hard graph-geometry; this is an assembly.

> **✅ DONE (2026-06-29) — `Spectra/Modular/TomitaTakesaki/VonNeumannTstarT.lean`, sorry-free,
> `#print axioms`-clean, root + `AxiomCheck`-gated (4082-job `lake build` green).** Headline
> `modularOp_isSelfAdjoint`. Recon found: All cited Mathlib API is **verified present** (incl. the crux
> `LinearPMap.adjoint_graph_eq_graph_adjoint` and `Submodule.adjoint`/`skewSwap`); there is **no**
> pre-existing `T⋆T` for `LinearPMap`, so the gate is genuinely needed. **Already proved sorry-free in
> the spike:** `modularDomain`, `modularOp` (Δ as a real `LinearPMap` — the `LinearPMap.comp` domain
> obstruction is *dissolved* by `S⋆.comp (S.domRestrict modularDomain)`), `modularOp_apply`,
> `modularOp_nonneg` (V4), `modularOp_isSymmetric`. **Remaining:** V1–V3 surjectivity (mechanical —
> `LinearPMap.IsClosed` is closedness in `H × Conj H` but `Submodule.adjoint` works in
> `WithLp 2 (H × Conj H)`; the only plumbing is that norm-equivalent transport — first lemma
> `graphL2_hasOrthogonalProjection`), and the new V5 lemma (below).

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
5. **`V5. Δ self-adjoint`** — symmetric `+ (1+Δ)` bijective-with-bounded-inverse ⟹ self-adjoint.
   ⚠️ **Correction (Spike A, 2026-06-29):** the project's `isSelfAdjoint_of_surjective_addSub` is
   **not** directly applicable — it requires `Δ ± iI` surjective (imaginary shifts), whereas the graph
   geometry delivers `1 + Δ` surjective; deriving the former from the latter is circular (it is the
   resolvent at `i`, which presupposes self-adjointness). V5 therefore needs **one new ~50-line lemma**:
   *a densely-defined symmetric `Δ` with `1+Δ` bijective and bounded inverse is self-adjoint* —
   structurally parallel to `isSelfAdjoint_of_surjective_addSub` but with the positivity bound
   `‖(1+Δ)x‖ ≥ ‖x‖` replacing the imaginary-shift isometry.
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
| ~~`State.IsNormal := True`~~ → **honest order-continuity (DONE 2026-06-30)** | `KMS/Modular.lean:75` | Replaced the `True` placeholder with the predual-free order-continuity predicate (`ω` preserves suprema of bounded increasing nets of positives), threading `[PartialOrder A] [StarOrderedRing A]` (the spectral order) through `FaithfulNormalState`/`ModularTheoryData`/`ConnesCocycle`. `FaithfulNormalState` is now a genuine restriction, not "faithful state." *Remaining:* proving concrete states normal (e.g. vector states) — future work, not a placeholder. Also purged the vacuous `modular_state_is_kms` ("Takesaki's Theorem" = `hmod.kms_at_one` field access). Build + AxiomCheck green (4088). |

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

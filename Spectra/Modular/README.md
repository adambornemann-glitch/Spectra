# `Spectra/Modular/` — Operator Algebras & Modular Theory

This directory formalizes the **modular theory** of operator algebras: the KMS condition, the
Tomita–Takesaki modular automorphism group, and (the multi-session target) the **Connes
Radon–Nikodym cocycle** `(Dφ : Dψ)_t`. It has two pillars plus a planned capstone:

```
Spectra/Modular/
├── KMS/                  -- ABSTRACT C*-side: the KMS condition + analytic/thermal structure
├── TomitaTakesaki/       -- CONCRETE Hilbert-space side: the modular operator Δ, conjugation J
└── Cocycle/              -- (PLANNED) the Connes RN cocycle, on the 2×2 amplification M₂(M)
```

The two pillars are *complementary descriptions of the same physics* and meet through the GNS
construction. The cocycle capstone sits on top of a *constructed* (not bundled) modular
automorphism group.

> **Ground truth is `lake build`.** This README is a map. Names below are real as of writing but
> verify against source / the symbol index (`docs/spectra-symbols.tsv`) before citing.

---

## The two pillars

### `KMS/` — abstract C\*-algebraic side  ·  *mature, sorry-free*

The equilibrium / thermal-time structure on an abstract C\*-algebra `A`, keyed on a `State A` and a
strongly-continuous automorphism flow `Dynamics A`.

| File | Content |
|---|---|
| `Condition.lean` | `IsKMSState`, `KMSFunction` (strip-analytic two-point function), bilinearity, three-lines bound, `IsGroundState`. |
| `AnalyticElements.lean` | `IsAnalyticElement`, the complex flow `σ_z`, `*`-subalgebra closure, Bratteli–Robinson **density**. |
| `ImaginaryTime.lean` | imaginary-time KMS `ω(a·σ_{iβ}b)=ω(b·a)`. |
| `Equivalence.lean` | `isKMSState_iff_imaginaryTime` (strip ⇔ imaginary-time). |
| `Generator.lean` | the infinitesimal generator `δ` (a `*`-derivation), vacuum `ω(δa)=0`, reality half of the ground-state condition. |
| `GroundState.lean` | ground states are invariant (`const_of_glue`). |
| `StateTopology.lean` / `ExtremalKMS.lean` | weak-\* state space (Banach–Alaoglu), pure states, extremal KMS states (Krein–Milman). |
| `UnitaryGroup.lean` | **GNS Liouvillian**: `invariantUnitaryGroup` (the implementation `U_ω(t)π(a)Ω=π(α_t a)Ω`), `…_generator_isSelfAdjoint`, `…_stoneEquivSpectral`, cyclic vector + `L Ω = 0`. The bridge into the Hilbert-space Stone/Yosida world. |
| `Modular.lean` | `FaithfulNormalState` (with an honest order-continuity `State.IsNormal`), the **target bundles** `ModularTheoryData` (modular flow + invariance + KMS@1) and `ConnesCocycle` (uninhabited, to be constructed — not axioms), and the conditional temperature-rescaling `modular_state_is_kms_at_beta`. |
| `PeriodicStrip/` | the strip max-principle / Phragmén–Lindelöf / Painlevé line-removal machinery. |

Roadmap: [`KMS/ROADMAP.md`](KMS/ROADMAP.md).

### `TomitaTakesaki/` — concrete Hilbert-space side  ·  *foundations sorry-free; construction in progress*

The geometric construction on a von Neumann algebra `M ⊆ B(H)` with a cyclic + separating vector
`Ω`. The antilinear Tomita operator `S(xΩ)=x⋆Ω` is handled by the **conjugate-space reduction** (an
antilinear `S : H → H` becomes a *linear* `S̃ : H →ₗ.[ℂ] Conj H`, so Mathlib's `LinearPMap`
adjoint/closure/self-adjoint API applies).

| File | Content | Status |
|---|---|---|
| `Basic.lean` | `IsCyclic`, `IsSeparating`, the easy duality, `jConj`, the **bundle** `ModularData` (J, `Δ^{it}`, Tomita + commutation theorems as fields). | ✅ foundations |
| `TomitaOperator.lean` | `tomitaOp` = `S̃` from its graph; `tomitaAdjoint` = `F`; domain = dense span. | ✅ H1 |
| `Duality.lean` | hard duality `IsSeparating M Ω → IsCyclic M.commutant Ω`, full iff. | ✅ E1 |
| `Closable.lean` | `tomitaOp_isClosable`, the closure `tomitaClosure` = the genuine `S`. | ✅ H2 |
| `ModularOperator.lean` | `S` closed + densely defined + non-negative form `‖Sx‖²` — von Neumann's hypotheses for `Δ=S⋆S`. | ✅ H3-setup |

Roadmap: [`TomitaTakesaki/ROADMAP.md`](TomitaTakesaki/ROADMAP.md).

---

## How the pieces connect (the layering)

```
   faithful normal state ω on a W*-algebra A            (abstract input, KMS side)
                    │  GNS                               Spectra.KMS.UnitaryGroup, GNS bridge (M1)
                    ▼
   (M = π(A)'', Ω)  cyclic + separating                 (concrete input, Tomita side)
                    │  Tomita operator S = J Δ^{1/2}     TomitaTakesaki: S̃ (H1) → closure (H2)
                    ▼
   Δ = S⋆S self-adjoint ≥ 0                              ◀── THE GATE: von Neumann T⋆T (Tier 5)
                    │  Borel calculus (CayleyTransform)
                    ▼
   Δ^{it}, modular flow σ_t = Ad Δ^{it};  J              R1 link + polar decomposition (R2/R3)
                    │  inhabits ModularData(M,Ω)         R4: tomitaTakesaki_exists
                    ▼
   σ_t is KMS at β = 1   ⇄   ModularTheoryData(A,ω)      the two pillars meet
                    │  2×2 amplification M₂(M)
                    ▼
   (Dφ : Dψ)_t  Connes RN cocycle                        ◀── CAPSTONE: inhabits ConnesCocycle
```

The whole tower bottlenecks on one classical theorem — **von Neumann's `T⋆T`** (Δ self-adjoint) —
after which `Δ^{it}` and `J` come from the existing `CayleyTransform` Borel calculus, and the RN
cocycle is matrix bookkeeping over an already-constructed modular flow (see below).

---

## Planned: `Cocycle/` — the Connes Radon–Nikodym cocycle

The cocycle `(Dφ : Dψ)_t` is **not** a new analytic object: it is the modular automorphism group of
the **balanced state** `θ` on the 2×2 amplification `M₂(M)`, read off the off-diagonal corner.
This reduces the RN cocycle to the *single-state* modular flow (above) plus matrix algebra.

| Planned file | Content |
|---|---|
| `Cocycle/Automorphism.lean` | `ModularData → ` bundled `*`-automorphism `σ_t` of `M` (group law, `*`-preserving). |
| `Cocycle/MatrixAmplification.lean` | `M₂(M)` as a `VonNeumannAlgebra (H ⊕ H)`; matrix units `eᵢⱼ`; corner maps; `commutant` of the amplification. |
| `Cocycle/BalancedWeight.lean` | the balanced vector `Ω_θ` / state `θ([xᵢⱼ]) = φ(x₁₁)+ψ(x₂₂)`; transport of cyclic + separating to `(M₂(M), Ω_θ)`. |
| `Cocycle/Cocycle.lean` | `u_t := ` corner of `σ^θ_t(e₂₁)`; **inhabit `ConnesCocycle`**: unitarity, cocycle law `u_{s+t}=u_s σ^ψ_s(u_t)`, intertwining `σ^φ_t = Ad(u_t)∘σ^ψ_t`. |
| `Cocycle/ChainRule.lean` | chain rule `(Dφ:Dψ)(Dψ:Dχ)=(Dφ:Dχ)`, `(Dφ:Dψ)⋆=(Dψ:Dφ)`, `u_t=1 ⟺ φ=ψ`, the KMS characterization. |

Detailed strategy lives in the vault project: `Spectra-Vault/Projects/Modular Theory/`
(`Goal - Modular Automorphism Group`, `Goal - Connes RN Cocycle`, `RN Cocycle Chain.canvas`).

---

## Standing rule: no permanent bundling

`ModularData`, `ModularTheoryData`, and `ConnesCocycle` are **bundles (a debt), not axioms.** Each
has a discharge plan and ultimately a *constructor* (`tomitaTakesaki_exists`, `connesCocycle_exists`).
See the discharge tables in the two `ROADMAP.md` files. The aim is **zero standing axioms**: every
headline result stays gated by `AxiomCheck.lean` (only `propext`/`Classical.choice`/`Quot.sound`).

## Mathlib gaps this directory could upstream

1. **Conjugate Hilbert space** `Conj E` + the antiunitary `E ≃ₗᵢ⋆[ℂ] Conj E` (in
   `SpectralTheory/Antilinear/`) — the clean way to give Mathlib's *linear* `LinearPMap` theory
   access to antilinear operators.
2. **von Neumann's `T⋆T` theorem** (`A⋆∘A` self-adjoint for closed densely-defined `A`).
3. **Polar decomposition** of closed (possibly unbounded) operators.
4. **Unbounded Borel functional calculus** (the project's `CayleyTransform` calculus covers bounded
   symbols; `Δ^{½}` needs unbounded).
5. **Cyclic / separating vectors** for `VonNeumannAlgebra`; the **KMS condition** itself.

No Lean 4 / Mathlib formalization of Tomita–Takesaki or the Connes cocycle exists elsewhere — this
directory is, as far as we know, the first.

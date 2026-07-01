# `Spectra/CayleyTransform/` — The Cayley Transform: Self-Adjoint ↔ Unitary

**Status: ✅ complete.** Every file below is sorry-free and gated in the default build; the
directory's connection into the rest of spectral theory (`StoneBridge/`, alongside it) is also
sorry-free and gated. `lake build` is green (4093 jobs) with only `propext` / `Classical.choice` /
`Quot.sound` in `#print axioms`. Full history and provenance:
`Spectra-Vault/Projects/Cayley Transform Bridge/`.

This directory formalizes von Neumann's own program (1929/1932): reduce an unbounded self-adjoint
operator `A` to a bounded unitary via the Cayley transform `V = (A-i)(A+i)^{-1}`, get the classical
spectral theorem for `V` from Riesz–Markov (no unbounded-operator theory needed at all), and pull
everything — spectrum, functional calculus, the one-parameter group `e^{itA}` — back across the
Möbius map `μ ↦ (μ-i)/(μ+i)`. Fourteen files, four layers:

```
Spectra/CayleyTransform/
├── Defs.lean               ─┐
├── Mobius.lean               │  core algebra: the transform, its Möbius shadow, its inverse
├── Inverse.lean              │
├── Image.lean               ─┘
├── Eigenvalue.lean          ─┐
├── MapsResolvent.lean         │  spectral correspondence: A's spectrum ↔ V's spectrum
├── BoundedBelow.lean        ─┘
├── RieszMarkov.lean         ─┐
├── BorelCalculus.lean         │  functional calculus of V (Riesz–Markov, bounded Borel symbols)
├── UnitaryGroup.lean        ─┘
└── Generator/
    ├── InverseAction.lean   ─┐
    ├── Resolvent.lean         │  the Stone-group route: e^{itA} from V, generator = A,
    ├── Pushforward.lean       │  entirely independently of the Yosida–Hille construction
    └── Stone.lean           ─┘
```

> **Ground truth is `lake build`.** This README is a map. Verify names against source before
> citing them elsewhere.

---

## Core algebra — the transform itself

| File | Content |
|---|---|
| `Defs.lean` | `cayleyTransform` = `I - 2i(A+iI)^{-1}`; `cayleyTransform_isometry`, `_surjective`, `_unitary`, `_mem_unitary`, spectrum on the unit circle, `cayleyTransform_isStarNormal` (the gate to Mathlib's `cfc`). |
| `Mobius.lean` | the scalar shadow `μ ↦ w := (μ-i)/(μ+i)` : ℝ ↠ circle∖{1}; `mobius_coeff_identity` (`i(1+w)=(1-w)μ`); the explicit two-sided `inverseMobius`. |
| `Inverse.lean` | recovers `A` from `V`: `dom(A) = range(I-V)`, `generator_domain_eq_range_one_minus_cayley`, `inverseCayleyOp`. |
| `Image.lean` | set-level Möbius images `cayleyImage` / `inverseCayleyImage`, transporting Borel sets between ℝ and the circle. |

## Spectral correspondence — `A`'s spectrum ↔ `V`'s spectrum

| File | Content |
|---|---|
| `Eigenvalue.lean` | `cayley_eigenvalue_correspondence` (exact match, real eigenvalue of `A` ⟺ circle eigenvalue of `V`), `cayley_shift_identity`, both directions of *approximate*-eigenvalue transfer. |
| `MapsResolvent.lean` | `cayley_maps_resolvent`: non-real `z` maps to the resolvent set; `resolvent_at_neg_i_eq_cfc` expresses `(A+iI)^{-1}` as `cfc` of `V`. |
| `BoundedBelow.lean` | quantitative transfer of "bounded below" between the Cayley shift `V-w` and `A-μ`; `norm_lower_bound_of_approx_eigenvalue_of_unit`. |

## Functional calculus of `V` — Riesz–Markov, bounded Borel symbols

| File | Content |
|---|---|
| `RieszMarkov.lean` | the classical Riesz–Markov construction: `spectralMeasure` (the scalar measure `μ_ξ` of `V`), `integral_spectralMeasure`, `spectralMeasure_real_univ = ‖ξ‖²`. |
| `BorelCalculus.lean` | the full bounded Borel functional calculus `borelCalculus` of `V` (1187 ln — the largest file): multiplicativity, adjoint, uniqueness via density/separation engines, and **`borelCalculus_eq_cfcHom`** — agreement with Mathlib's own continuous functional calculus on continuous symbols. |
| `UnitaryGroup.lean` | the generic recipe `borelUnitaryGroup`: any unimodular, multiplicative, measurable symbol family gives a `OneParameterUnitaryGroup`. Specializes to `borelModularGroup` (`modularSymbol = λ^{it}`) — the modular flow `Δ^{it}` feeds directly off this. |

## The Stone-group route — `e^{itA}` from `V`, independently of Yosida

| File | Content |
|---|---|
| `Generator/InverseAction.lean` | `cayley hA` (the bounded transform of a self-adjoint `A`); `stoneExpSymbol`, `stoneExp` = `e^{itA}` via the Borel calculus of `V`; packages the group `stoneGroup`. |
| `Generator/Resolvent.lean` | **Keystone 1**: `selfAdjointResolvent_eq_borelCalculus` — `(A-z)^{-1} = borelCalculus(V)(resolventSymbol)`, closing continuous ↔ Borel via measure-a.e. congruence. |
| `Generator/Pushforward.lean` | `borelMeasure_stoneGroup_eq_map`: the group's own spectral measure is the pushforward of `V`'s Riesz–Markov measure under `inverseMobiusReal`. |
| `Generator/Stone.lean` | **Keystone 2**: `generator_stoneGroup : generator (stoneGroup hA) = A`, proved *without ever mentioning the Yosida group* — resolvent-matching + `A ≤ generator (stoneGroup hA)` + `IsSelfAdjoint.eq_of_le`. |

---

## How the pieces connect

```
   A : H →ₗ.[ℂ] H, self-adjoint (unbounded)
                    │  Cayley transform V = (A-i)(A+i)⁻¹        Defs.lean
                    ▼
   V : H →L[ℂ] H, unitary, star-normal
                    │  Riesz–Markov spectral measure μ_ξ        RieszMarkov.lean
                    ▼
   bounded Borel calculus Φ_V(g), g : spectrum ℂ V → ℂ          BorelCalculus.lean
       │ matches cfcHom on continuous g (borelCalculus_eq_cfcHom)
                    │  symbol family t ↦ e^{it·inverseMobius(w)}
                    ▼
   stoneGroup hA : OneParameterUnitaryGroup H  (= e^{itA})      Generator/InverseAction.lean
                    │  generator_stoneGroup : generator = A      Generator/Stone.lean
                    ▼                                            (no Yosida anywhere above this line)
   StoneBridge/Basic.lean:  stoneGroup hA = genToGroup hA        ◀── P0: the two constructions of
                    │                                                e^{itA} (Cayley vs. Hille–Yosida)
                    │                                                agree, by generator-uniqueness
                    ▼
   StoneBridge/SpectralPVM.lean:  spectralPVM hA = groupPVM (stoneGroup hA)
                    │                                            ◀── the canonical spectral measure
                    │                                                IS the Cayley/Riesz–Markov one
                    ▼
   StoneBridge/SpectralTheoremCayley.lean:  spectralTheoremCayley
                    │                                            ◀── P5: the spectral theorem,
                    │                                                proved a SECOND, INDEPENDENT
                    │                                                way — existence witnessed by
                    │                                                the Cayley PVM, no genToGroup
                    ▼
   StoneBridge/CalculusBridge.lean:  pmapOfPVM ↔ spectralCalculus ↔ borelCalculus ↔ cfcHom
                                                                  ◀── P4: the library's own unbounded
                                                                      functional calculus IS Mathlib's
                                                                      cfcHom, pulled back through Cayley
```

**`StoneBridge/`** (a sibling directory, not nested under this one) is where the loop actually
closes — it is the reason this directory is complete rather than merely self-contained:

| File | Closes |
|---|---|
| `StoneBridge/Basic.lean` | `stoneGroup_eq_genToGroup` — the Cayley and Hille–Yosida constructions of `e^{itA}` are the *same group*. |
| `StoneBridge/SpectralPVM.lean` | `spectralPVM_eq_groupPVM_stoneGroup` — the canonical `spectralPVM` (used by `JointPVM`, `BornRule`, `Observable`, `pmapOfPVM`, hydrogen-spectrum work) IS the Cayley/Riesz–Markov PVM. |
| `StoneBridge/SpectralTheoremCayley.lean` | `spectralTheoremCayley` — a **second, independent** proof of the spectral theorem itself, existence witnessed by the Cayley PVM, never mentioning `genToGroup`. This is the historical point of the Cayley transform. |
| `StoneBridge/CalculusBridge.lean` | `pmapOfPVM_apply_eq_cfcHom_of_bounded` — the library's own unbounded functional calculus equals Mathlib's `cfcHom`, pulled back through Cayley. |

---

## What's deliberately out of scope here

- **The Tomita–Takesaki modular flow's generator** (`Spectra/Modular/`, RN-Cocycle project's
  "FIELD 5"): `modularFlow` already builds `Δ^{it}` via `borelModularGroup` (`UnitaryGroup.lean`
  above), but identifying its *generator* with `Δ` (mirroring `Generator/Stone.lean`'s proof
  pattern) is tracked as its own item in the Modular Theory project, not here.
- **A literal `Equiv`-style bijection** self-adjoint operator ↔ `ProjValMeasure` (mirroring
  `stoneEquiv`/`stoneEquivSpectral`'s packaging of Stone's theorem). `spectralTheorem` is stated as
  `∃!`, which `spectralTheoremCayley` reproves independently; a full `Equiv` would need a *reverse*
  direction (`P ↦ ∫λ dP(λ)`) generalizing `pmapOfPVM` beyond `OneParameterUnitaryGroup` to a raw
  `ProjValMeasure`. Explicitly deferred, not started.

## Mathlib gaps this directory could upstream

1. **The Cayley-transform route to the spectral theorem itself** — deriving the unbounded
   self-adjoint spectral theorem from Riesz–Markov on the bounded unitary transform is the
   textbook approach (Reed–Simon, Rudin) and does not exist in Mathlib.
2. **Unbounded Borel functional calculus** built from a bounded one via Cayley pullback
   (`StoneBridge/CalculusBridge.lean`) — no analogue in Mathlib today.
3. **`cfcHom` for unbounded self-adjoint operators**, pulled back through a bounded normal
   reduction — Mathlib's `cfc`/`cfcHom` machinery is bounded-operator-only.

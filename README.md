# Spectra

**A Lean 4 formalization of spectral theory and mathematical quantum mechanics, built on [Mathlib](https://github.com/leanprover-community/mathlib4).**

Spectra develops the operator-theoretic backbone of quantum mechanics — the spectral
theorem, Stone's theorem, the resolvent and functional calculus — and then *uses* it to
formalize genuine physics: the Born rule, the uncertainty principle, Bell/CHSH inequalities,
the Dirac equation, KMS states and modular theory, and information geometry. Its conventions
follow [PhysLean / PhysLib](https://physlib.io) and Mathlib closely, so anyone fluent in those
libraries can read it without a ramp-up.

| | |
|---|---|
| **Toolchain** | `leanprover/lean4:v4.31.0-rc1` (pinned in [`lean-toolchain`](lean-toolchain)) |
| **Depends on** | Mathlib (pinned in [`lake-manifest.json`](lake-manifest.json)) |
| **License** | MIT — see [`LICENSE`](LICENSE) |
| **Size** | 279 source files, ≈78,000 lines |
| **Build status** | `sorry`-free default build, enforced by the [`AxiomCheck`](AxiomCheck.lean) gate (CI runs `lake build`) |

---

## Overview

The library is organized as a tower. At the bottom sits a self-contained theory of **unbounded
self-adjoint operators on complex Hilbert space** — resolvents, the Cayley transform, Yosida
approximation — culminating in two independent proofs of **Stone's theorem** and a proof of the
**spectral theorem** in resolvent / projection-valued-measure form. On top of that foundation,
each physics module is built as a *theorem*, not an axiom: the Born rule is derived from the
spectral measure, the uncertainty principle from the Cauchy–Schwarz inequality on the GNS inner
product, Ehrenfest's theorem from Stone's differentiation, and so on.

A deliberate design choice runs through the whole project: **the hard analytic content is
proved, not assumed.** There are no bespoke `axiom` declarations standing in for the difficult
step, no `native_decide`, and no `sorry` anywhere the build can reach it.

---

## What's formalized

Every result below is **proved and `sorry`-free in the default build** unless explicitly marked
otherwise. Declaration names are given so you can `grep` for them.

### The spectral-theory core

| Result | Statement | Where |
|---|---|---|
| **Spectral theorem** (`spectralTheorem`) | Every self-adjoint `A` admits a *unique* projection-valued measure `E` with `⟪ξ, (A−z)⁻¹ξ⟫ = ∫ (s−z)⁻¹ d⟪ξ, E(·)ξ⟫` for `Im z ≠ 0`. | `SpectralTheory/ResolventForm.lean` |
| **Stone's theorem** (`stoneEquiv`) | `OneParameterUnitaryGroup H ≃ {self-adjoint operators on H}`, generator ↔ group. | `Stone/Basic.lean` |
| **Stone, second construction** (`stoneEquivSpectral`) | The same equivalence built from the Cayley transform + Borel calculus, *proved equal* to `stoneEquiv`. | `StoneBridge/Basic.lean` |
| **Weak spectral moments** (`weak_first_moment`, `weak_second_moment`) | For `φ ∈ dom A`: `∫ s dμ_φ = ⟪φ, Aφ⟫` and `∫ s² dμ_φ = ‖Aφ‖²`. | `SpectralTheory/Weak.lean` |
| **Stone's formula** (`stonesFormula_spectralPVM`) | Spectral projections recovered from boundary limits of the resolvent. | `SpectralTheory/ResolventForm.lean` |
| **Bochner's theorem** (`bochner_theorem`) | A continuous `f : ℝ → ℂ` is positive-definite iff it is the Fourier–Stieltjes transform of a *unique* finite measure. Proved via the GNS construction (`gns_theorem`). | `Bochner/Basic.lean` |
| **Herglotz / Helly** (`helly_selection`) | Helly's selection theorem and the Herglotz–Nevanlinna integral representation. | `Herglotz/` |

This core (`Operator`, `Resolvent`, `SpectralTheory`, `Stone`, `CayleyTransform`, `Bochner`,
`Herglotz`, `Kernel`, `Fourier`, `ProjValMeasure`, `OneParameterUnitaryGroup`) is the most
heavily-tested part of the library and is entirely `sorry`-free.

### Quantum mechanics

| Result | Statement | Where |
|---|---|---|
| **Born rule** | Outcome probabilities `‖E_B ψ‖²`; expectation `⟪ψ, Aψ⟫`; variance `‖(A−⟨A⟩)ψ‖²`, built on the spectral PVM. | `QuantumMechanics/BornRule/` |
| **Uncertainty** (`heisenberg_uncertainty`, `schrodinger_uncertainty`) | Heisenberg `σ_A σ_B ≥ ℏ/2` under the CCR, and the stronger Schrödinger–Robertson bound with the covariance term. | `QuantumMechanics/Uncertainty/` |
| **Ehrenfest's theorem** (`ehrenfest_theorem`) | `d/dt ⟪ψ(t), Bψ(t)⟫ = ⟪iAψ, Bψ⟫ + ⟪ψ, B(iAψ)⟫` under Schrödinger flow. | `QuantumMechanics/Ehrenfest.lean` |
| **First law / unitary invariance** (`first_law`) | The entire energy distribution `μ_ψ` is invariant under the unitary flow it generates. | `QuantumMechanics/Unitarity/FirstLawIff.lean` |
| **CHSH / Bell** (`CHSH_lhv_bound`, `tsirelson_bound'`) | Local hidden-variable models obey `|S| ≤ 2`; quantum states obey Tsirelson's `|S| ≤ 2√2`, and the gap is achieved. | `QuantumMechanics/BellsTheorem/` |
| **Free Dirac operator** (`diracHamiltonian_isSelfAdjoint`, `diracHamiltonian_mass_gap`) | `H_D = α·p + βmc²` is self-adjoint on `H¹(ℝ³;ℂ⁴)`; the dispersion relation `D² = (\|p\|²+m²)I` and the mass gap of width `2mc²` are proved. | `QuantumMechanics/DiracEquation/` |
| **Kato–Rellich & Hardy** (`kato_rellich`, `hardy_inequality`) | Relative-bound self-adjointness of `A+V`; Hardy's inequality `∫\|ψ\|²/\|x\|² ≤ 4∫\|∇ψ\|²` in 3D, giving the Coulomb potential relative bound 0 w.r.t. `−Δ`. | `QuantumMechanics/Perturbation/` |

### Information geometry

| Result | Statement | Where |
|---|---|---|
| **Fisher metric** (`fisherMatrix`) | The Fisher information `g_{ij} = E_θ[s_i s_j]` as a Riemannian metric on a statistical manifold. | `InformationGeometry/Fisher/` |
| **KL Hessian = Fisher** (`klDiv_hessian_eq_fisher`) | `∂²D(θ‖θ')/∂θ'ⁱ∂θ'ʲ \|_{θ'=θ} = g_{ij}(θ)`. | `InformationGeometry/Divergence.lean` |
| **Cramér–Rao** (`cramerRao_scalar`) | `Var_θ(T) ≥ (∂_i τ)² / g_{ii}` for regular unbiased estimators; quantum Schrödinger–Cramér–Rao bound. | `InformationGeometry/CramerRao/` |
| **Amari–Chentsov** (`cubicTensor`) | The totally-symmetric cubic tensor and the dual `α`-connections (`Γ⁽¹⁾ + Γ⁽⁻¹⁾ = 2Γ⁽⁰⁾`). | `InformationGeometry/Connection/` |

### Modular theory & KMS

| Result | Statement | Where |
|---|---|---|
| **KMS condition** (`IsKMSState`) | The strip/boundary definition of a `(α, β)`-KMS state, plus invariance. | `Modular/KMS/Condition.lean` |
| **KMS ⇔ imaginary time** (`isKMSState_iff_imaginaryTime`) | Equivalence of the strip condition and the imaginary-time form (via density of analytic elements + Hadamard three-lines, no Montel). | `Modular/KMS/Equivalence.lean` |
| **Extremal KMS states** | The KMS state set is weak-\* compact convex; extremal states exist (Krein–Milman). | `Modular/KMS/ExtremalKMS.lean` |
| **Tomita–Takesaki seed** | Cyclic/separating vectors and commutant duality (easy direction) proved. The modular data `(J, Δ^{it})` is bundled as an **interface awaiting a constructor** — see below. | `Modular/TomitaTakesaki/Basic.lean` |

### Sobolev spaces & analysis

`meyers_serrin_approx` (the `H = W` theorem), `sobolev_embedding_L6` (`H¹(ℝ³) ↪ L⁶`, the
scaling-correct exponent), the du Bois-Reymond lemma, mollification, and integration by parts —
all in `SobolevSpaces/`, all `sorry`-free.

### Headed for Mathlib

`Spectra/Mathlib/` holds general-purpose infrastructure written to be upstreamed, kept free of
Spectra-specific assumptions: the **Sewing Lemma** (three control regimes, with existence,
uniqueness, and additivity), **p-variation**, and **Young integration** (`youngIntegral`, with
additivity, linearity, and integration by parts), plus a characteristic-function uniqueness
bridge. Two refinements remain work-in-progress and are held out of the build (Riemann–Stieltjes
consistency; continuity of p-variation).

---

## Library architecture

```
Foundations
  Operator/                symmetric (unbounded) & unitary operators, commutators
  Resolvent/               (A−z)⁻¹: identities, analyticity, spectrum, integral form
  ProjValMeasure/          projection-valued measures via diagonal scalar measures
  OneParameterUnitaryGroup/  generators of strongly continuous unitary groups

Spectral theorem & Stone's theorem
  Stone/  CayleyTransform/  StoneBridge/  SpectralTheory/
  Bochner/                 GNS construction → Bochner's theorem
  Herglotz/  Kernel/  Fourier/   integral-representation machinery

Applications
  QuantumMechanics/        Born rule, uncertainty, Bell/CHSH, Dirac, hydrogen, perturbation
  InformationGeometry/     Fisher metric, Cramér–Rao, connections, geometric flows
  Modular/                 KMS condition, modular theory, Tomita–Takesaki seed
  SobolevSpaces/  SphericalHarmonics/   supporting analysis

Upstream-bound
  Mathlib/                 Sewing lemma, p-variation, Young integration (general infrastructure)
```

The directory path and namespace always match: `Spectra/Resolvent/Defs.lean` declares
`namespace Spectra.Resolvent`. The root module [`Spectra.lean`](Spectra.lean) imports every file
that is part of the build.

---

## Proof status

Spectra takes the [`CONTRIBUTING.md`](CONTRIBUTING.md) rule seriously: *a `sorry` may live only in
a clearly work-in-progress file, never in a file that a finished result imports.* A source audit
confirms this is upheld:

- **The default build target — everything reachable from [`Spectra.lean`](Spectra.lean) — is
  `sorry`-free and `admit`-free, and contains no bespoke `axiom` declarations, no `native_decide`,
  and no `opaque`/`unsafe` shortcuts.** All headline results above are proved to the kernel.
- The genuine `sorry`s in the tree live **only in modules with no active importer**, deliberately
  commented out of the root so they are not compiled:
  - `QuantumMechanics/Hydrogen/Spectrum/`, `…/RadialProblem/Equation/`, `…/Laplacian/{FreeGreens,Spherical}` — the assembly of the hydrogen discrete spectrum `E_n = −Z²/2n²`. The *operator scaffolding* it will rest on (the self-adjoint Laplacian, the radial/angular decomposition, Laguerre polynomials) **is** proved and in the build; the spectral assembly is not yet finished.
  - `QuantumMechanics/Perturbation/HardySharp.lean` — sharpness of the Hardy constant (the inequality itself is proved and in the build).
  - `Mathlib/StochasticCalc/YoungIntegration/Integral/Consistency.lean` and `…/PVariation/TODO.lean` — the two upstream refinements noted above.
- **Interface bundles.** A few advanced structures are stated as bundles of defining properties
  whose *constructor* is future work — most notably `ModularData` (the Tomita–Takesaki modular
  operator and conjugation), which is blocked on Mathlib infrastructure (antilinear unbounded
  operators, polar decomposition, Borel calculus for unbounded operators). These are honest
  output types, not proofs in disguise: downstream code may *assume* a `ModularData` and reason
  from its fields, but the library does not yet *construct* one. The same pattern applies to the
  `State.IsNormal` predicate in the (non-built) `KMS/Modular.lean`, which is currently a
  placeholder pending a chosen predual in Mathlib.

> **Known cleanup:** a handful of docstrings still describe a `sorry` that has since been
> discharged (e.g. the file headers of `SphericalHarmonics/Basic.lean`, `Ehrenfest.lean`, and the
> "Sorry strategy" note in `HardyInequality.lean`). These understate completeness and are slated
> for removal; the proofs are finished.

This is now **enforced**, not merely audited. [`AxiomCheck.lean`](AxiomCheck.lean) runs Mathlib's
`assert_no_sorry` on every headline result as a `@[default_target]`, so a `sorry` reaching any of
them fails `lake build`; [`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs that build on
every push and pull request. For transparency the gate also `#print axioms` the crown jewels —
`spectralTheorem`, `stoneEquiv`, `bochner_theorem`, `tsirelson_bound'` — which depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

---

## Building

Spectra uses the standard Lean 4 / Lake toolchain; `elan` installs the pinned compiler
automatically.

```sh
# 1. install elan (https://github.com/leanprover/elan), then:
git clone <your-fork-url> Spectra
cd Spectra
lake exe cache get   # fetch prebuilt Mathlib artifacts — avoids recompiling Mathlib
lake build           # build the Spectra library
```

The recommended editor is **VS Code with the Lean 4 extension** for the interactive goal view and
hover docstrings.

---

## Contributing

Contributions of every size are welcome — see [`CONTRIBUTING.md`](CONTRIBUTING.md) for the workflow
and [`STYLE.md`](STYLE.md) for conventions. The non-negotiables: the MIT copyright header, a module
docstring (`# Title`, `## Main definitions`, `## Main statements`, `## References`), a `/-- … -/`
docstring on **every** declaration, and a clean `lake build` with no new `sorry` in finished files.
Small, focused pull requests are strongly preferred.

---

## License

Spectra is released under the MIT License — see [`LICENSE`](LICENSE).
Copyright © 2026 Spectra Project, Adam Bornemann.

---

## References

The formalization follows standard sources, cited per-file in `## References` blocks. The main
ones: Reed & Simon, *Methods of Modern Mathematical Physics*; Kato, *Perturbation Theory for
Linear Operators*; Bratteli & Robinson, *Operator Algebras and Quantum Statistical Mechanics*
(KMS / modular theory); Amari & Nagaoka, *Methods of Information Geometry*; and Friz & Victoir,
*Multidimensional Stochastic Processes as Rough Paths* (sewing / Young integration).

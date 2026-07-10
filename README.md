# Spectra

**A Lean 4 formalization of operator theory, spectral theory, and mathematical quantum mechanics, built on [Mathlib](https://github.com/leanprover-community/mathlib4).**

Spectra develops the operator-theoretic backbone of quantum mechanics — unbounded self-adjoint
operators, the spectral theorem, Stone's theorem, resolvents and functional calculus, modular
theory — and *uses* it to formalize real physics: the Born rule, uncertainty, Bell inequalities,
the Dirac equation, and the hydrogen atom's spectrum. The long-range target is a rigorous route to
**density functional theory (DFT/MDFT)**; everything below is a step on that road or a cross-check
along it. Conventions follow [PhysLean / PhysLib](https://physlib.io) and Mathlib.

| | |
|---|---|
| **Toolchain** | `leanprover/lean4:v4.31.0-rc1` (pinned in [`lean-toolchain`](lean-toolchain)) |
| **Depends on** | Mathlib (pinned in [`lake-manifest.json`](lake-manifest.json)) |
| **License** | Apache 2.0 — see [`LICENSE`](LICENSE) |
| **Size** | ~370 source files, ~107,000 lines |
| **Build status** | `sorry`-free default build, enforced by the [`AxiomCheck`](AxiomCheck.lean) gate (CI runs `lake build`) |
| **Trust gates** | *proofs*: the [`AxiomCheck`](AxiomCheck.lean) axiom/`sorry` gate; *statements*: [341 numeric checks](NumericChecks/README.md) that constants, signs and normalizations match the intended physics, plus the [`ForensicCheck`](ForensicCheck.lean) gate against unused / over-strong hypotheses |

---

## Overview

The library is a tower. At the base is a self-contained theory of **unbounded operators on complex
Hilbert space** — symmetric and self-adjoint operators, closability and the double adjoint,
deficiency indices, and von Neumann's self-adjoint extension theory. On that base sits the
**spectral theorem** (in resolvent / projection-valued-measure form, proved two independent ways)
and **Stone's theorem**, then the functional calculus, the **essential spectrum with Weyl's
theorem**, and **Tomita–Takesaki modular theory**. The physics layers — the Born rule, Bell/CHSH,
the Dirac operator, and the **hydrogen atom's spectrum** — are then built as *theorems*, not
axioms.

A single discipline runs throughout: **the hard analytic content is proved, not assumed.** There
are no bespoke `axiom` declarations standing in for the difficult step, no `native_decide`, and no
`sorry` anywhere the build can reach — a property the CI gate enforces on every commit (see
[Proof status](#proof-status)).

---

## What's formalized

Every result named below is **proved and `sorry`-free in the default build**; each is guarded by
name in [`AxiomCheck.lean`](AxiomCheck.lean), so the claim is machine-checked. Names are given so
you can `grep` for them.

### Operator theory on Hilbert space  (`Operator/`)

A full treatment of unbounded operators, culminating in von Neumann's extension theory:

- **Closability & the double adjoint** — `T** = T̄` for symmetric `T` (`adjoint_adjoint_eq_closure`),
  bounded ⟺ closed on a full domain, the `HasCore`/graph-closure bridge.
- **Deficiency indices** `n±(A) = dim ker(A* ∓ i)` and their orthogonal-complement descriptions.
- **Von Neumann's self-adjoint extension theorem** — a symmetric operator admits a self-adjoint
  extension iff `N₊ ≃ₗᵢ N₋` (`exists_le_isSelfAdjoint_iff_nonempty_deficiencyEquiv`), the explicit
  extension `A_V` (`vonNeumannExtension`), and the **classification** `V ↦ A_V` as a bijection
  (`selfAdjointExtensionEquiv`); essential self-adjointness ⟺ a *unique* self-adjoint extension
  (`isEssentiallySelfAdjoint_iff_existsUnique_le_isSelfAdjoint`).
- **The first and second von Neumann formulas** — `D(A*) = D(Ā) ⊔ N₊ ⊔ N₋` (`vonNeumannFormula`,
  graph-orthogonal and unique), and the boundary-form classification of *symmetric* extensions
  (`exists_eq_vonNeumannExtensionOn`).
- **Kato–Rellich** (`kato_rellich`) and essential self-adjointness of sums on a common domain.
- **Numerical range** — `spectrum ⊆ closure(numerical range)` (`spectrum_subset_closure_numericalRange`),
  via a genuine resolvent construction.

### The spectral theorem, functional calculus & Stone's theorem

- **Spectral theorem** (`spectralTheorem`) — every self-adjoint `A` admits a *unique* PVM with
  `⟪ξ,(A−z)⁻¹ξ⟫ = ∫ (s−z)⁻¹ d⟪ξ,E(·)ξ⟫`, `Im z ≠ 0`. Proved **twice**: via Stone/Yosida and,
  independently, via the Cayley transform + Riesz–Markov (`spectralTheoremCayley`).
- **Stone's theorem** (`YosidaHille.stoneEquiv`, `stoneEquivSpectral`) — `OneParameterUnitaryGroup H
  ≃ {self-adjoint operators}`, built both ways and proved equal.
- **Functional calculus** — the bounded/Borel calculus and the unbounded `∫ f dP`
  (`pmapOfPVM`), identified with Mathlib's `cfcHom` through the Cayley transform.
- **Weak moments** (`weak_first_moment`, `weak_second_moment`), **Stone's formula**, and
  **resolvent meromorphy** on the resolvent set.

### Essential spectrum & Weyl's theorem  (`SpectralTheory/Essential/`)

`σ_ess` invariance under relatively compact perturbation
(`essSpectrum_eq_of_isCompactOperator_perturb`), and `σ_ess(−½Δ) = [0,∞)` on `L²(ℝ³)`
(`essSpectrum_halfLaplacian`, `essSpectrum_laplacian`) — the engine for Schrödinger operators.

### Bochner, Herglotz & Fourier

Bochner's theorem via a genuine **GNS construction** (`bochner_theorem`, `gns_theorem`), Herglotz /
**Helly selection** (`helly_selection`), and Fourier uniqueness (`fourier_uniqueness`).

### Modular theory — Tomita–Takesaki & KMS  (`Modular/`)

The modular apparatus is **constructed**, not postulated:

- **KMS condition** (`IsKMSState`) and its imaginary-time equivalence (`isKMSState_iff_imaginaryTime`).
- **Modular operator** `Δ = S⋆S`, self-adjoint and `≥ 0` (`modularOp_isSelfAdjoint`,
  `modularOp_nonneg` — the von Neumann `T⋆T` milestone), the **modular flow** `Δ^{it}`
  (`modularFlow_unitary`, `modularFlow_group_law`), the **square root** `Δ^{½}` with `(Δ^{½})² = Δ`,
  and the **polar decomposition** `S = J Δ^{½}` with the antiunitary **modular conjugation** `J`
  (`tomita_eq_modularConjugation_modularSqrt_full`, `modularConjugation`).
- Vacuum invariance (`Δ Ω = Ω`, `J Ω = Ω`, `Δ^{it} Ω = Ω`) and the reciprocals `Δ⁻¹`, `Δ^{-½}`.

The final commutation theorem (`JMJ = M′`, `Δ^{it}MΔ^{-it} = M`) is the current endgame; the
objects it is stated in terms of now all exist and carry their defining properties.

### Operator algebras & quantum information  (`QuantumMechanics/Channels/`, `Spaces/`)

- **Trace-class operators** — polar decomposition `T = U|T|`, the trace norm, the Hilbert–Schmidt
  ideal, the complex trace with cyclicity `tr(AB) = tr(BA)`, the triangle inequality, and
  `TraceClass H` as a **ℂ-Banach space** (`TraceClass.instCompleteSpace`).
- **Quantum channels** — complete positivity (`IsCompletelyPositive`) and the `QuantumChannel`
  bundle.
- **Hilbert tensor products** `E ⊗̂ F` — cross norm `‖A ⊗̂ B‖ = ‖A‖·‖B‖`, the tensor Hilbert basis,
  the tensor powers `⨂ⁿ H`, and the **full Fock space** `fullFock`.
- **Bosonic & fermionic Fock spaces** — the symmetrizer/antisymmetrizer as self-adjoint idempotent
  contractions, the symmetric/antisymmetric sectors with their permutation-invariance
  characterizations, **Pauli exclusion** at the tensor level (`altProj_tprod_eq_zero`),
  `boseFock`/`fermiFock`, and diagonal isometries of Hilbert sums (`lpCongrRight`).
- **Fock-space kinematics** — the vacuum, orthogonal sector embeddings, dense finite-particle
  cores, the **self-adjoint number operator** (`numberOp_isSelfAdjoint`), exponential vectors
  with `⟪ε(f), ε(g)⟫ = exp ⟪f, g⟫` (`inner_expVec_expVec`), the polarization identity, and the
  totality theorem `expVec_total` — the closed span of the coherent vectors is everything.
- **Krein spaces** — fundamental symmetries `J`, the indefinite Krein form, the fundamental
  decomposition `H₋ = H₊ᗮ`, the J-adjoint calculus, and the **Krein–Fock lift**: `J` second-quantizes
  to `fockSymmetry` on `fullFock` — the Gupta–Bleuler indefinite metric, sector by sector.

### Quantum mechanics  (`QuantumMechanics/`)

- **Born rule & the multivariate spectral theorem** — strong commutativity ⟺ a joint PVM
  (`stronglyCommute_iff_jointPVM`) and the correlation identity
  `∫ xy dμ = ⟪ξ,A(Bξ)⟫.re` (`jointBornMeasure_correlation`), the bridge to Bell/CHSH.
- **Uncertainty** (`heisenberg_uncertainty`), **Ehrenfest** (`ehrenfest_theorem`), the Schrödinger
  equation, the **first law** / unitary invariance (`first_law`), and the Pauli algebra.
- **Bell inequalities** — the classical CHSH bound (`CHSH_lhv_bound`), **Tsirelson's** `2√2`
  (`tsirelson_bound'`), Bell's original 1964 inequality, Wigner's form, Clauser–Horne, and the
  Popescu–Rohrlich box hitting the algebraic maximum `4` (`prBox_chsh_eq_four`).
- **Dirac operator** — self-adjointness (`diracHamiltonian_isSelfAdjoint`) and the mass gap
  (`diracHamiltonian_mass_gap`).

### The hydrogen atom  (`QuantumMechanics/Hydrogen/`) — the showcase

The Coulomb Hamiltonian's spectrum, assembled end to end:

- **Self-adjointness** via Kato–Rellich, powered by **Hardy's inequality** with the sharp constant
  (`hardy_inequality`, `hardy_constant_sharp`, `coulomb_kato_rellich`, `hydrogen_isSelfAdjoint`).
- **Continuous spectrum** `σ_ess(H) = [0,∞)` and **no positive eigenvalues** (Kato)
  (`hydrogen_continuous_spectrum`, `hydrogen_no_positive_eigenvalues`).
- **Bound states** — radial quantization and explicit eigenfunctions (`RadialEq.radial_quantization`,
  orthonormality, uniqueness), the eigenfunction equation `H ψ_{nℓm} = Eₙ ψ_{nℓm}`, the `n²`-fold
  degeneracy and its spectral projection `E({Eₙ})`, and **resolvent meromorphy** — simple poles at
  each `Eₙ = −Z²/2n²` with residue `−E({Eₙ})` (`hydrogen_meromorphicOn`, `hydrogen_residue_eigenvalue`).

### Information geometry  (`InformationGeometry/`)

The Fisher metric, **Cramér–Rao** (`cramerRao_scalar`), `∂²D_KL = Fisher` (`klDiv_hessian_eq_fisher`),
the Amari–Chentsov tensor and dual connections, an information-geometric Stone theorem, and the
classical–quantum dichotomy (`classical_quantum_dichotomy`).

### Analysis infrastructure  (`Spaces/Sobolev/`, `SphericalHarmonics/`, `Mathlib/`)

Sobolev spaces (`meyers_serrin_approx`, the scaling-correct `sobolev_embedding_L6`, density chains),
spherical harmonics, and `Mathlib/`: small **upstreamable** bridges — `CharFunBridge` and the
Hilbert tensor product (which closes Mathlib's "complete space of tensor products" TODO).

---

## Library architecture

```
Operator theory
  Operator/               symmetric/self-adjoint operators, closability, double adjoint,
                          deficiency indices, von Neumann extension theory, numerical range
  Resolvent/              (A−z)⁻¹: identities, analyticity, spectrum, meromorphy
  ProjValMeasure/         projection-valued measures (+ pushforward)
  OneParameterUnitaryGroup/

Spectral theorem & Stone's theorem
  YosidaHille/  CayleyTransform/  StoneBridge/  SpectralTheory/   (incl. Essential/, Calculus/)
  Bochner/                GNS construction → Bochner's theorem
  Herglotz/  Kernel/  Fourier/

Modular theory
  Modular/KMS/  Modular/TomitaTakesaki/  Modular/Cocycle/   (Δ, Δ^{it}, Δ^{½}, S = JΔ^{½})

Operator algebras / quantum information
  QuantumMechanics/Channels/   trace-class operators, quantum channels
  Spaces/Tensor/  Spaces/Fock/  Hilbert tensor products, Fock space

Applications
  QuantumMechanics/       Born rule + joint PVM, uncertainty, Bell/CHSH, Dirac, hydrogen
  InformationGeometry/    Fisher metric, Cramér–Rao, connections, flows
  Spaces/Sobolev/  SphericalHarmonics/    supporting analysis

Upstream-bound
  Mathlib/                CharFunBridge, Hilbert tensor product, completion functoriality
```

The directory path and namespace match: `Spectra/Operator/Symmetric.lean` lives in
`namespace Spectra.Operator`. The root [`Spectra.lean`](Spectra.lean) imports every module in the
build. (`Scratch/` holds throwaway axiom-probes and is not part of the library.)

---

## Proof status

Spectra keeps the [`CONTRIBUTING.md`](CONTRIBUTING.md) rule: a `sorry` may live only in a clearly
work-in-progress file, never in one a finished result imports. A source audit and the CI gate
confirm it holds:

- **The default build is `sorry`-free, `admit`-free, and free of bespoke `axiom`s,
  `native_decide`, and `opaque`/`unsafe` shortcuts.** [`AxiomCheck.lean`](AxiomCheck.lean) runs
  `assert_no_sorry` on every headline result above, as a `@[default_target]`, so a `sorry`
  reaching any of them fails `lake build`. `#print axioms` on the crown jewels (spectral theorem,
  Stone, Bochner, Tsirelson, the trace-class Banach structure, the von Neumann formulas, the
  modular reciprocals, the tensor product) reports only `propext`, `Classical.choice`, `Quot.sound`.
- **The single `sorry` in the tree** sits in `Scratch/SpikeM2.lean`, a probe file with no active
  importer — not compiled by the build.
- **Ongoing endgames**, stated in terms of objects that already exist and are proved: the
  Tomita–Takesaki commutation theorem (`JMJ = M′`); a few hydrogen analytic tracks not yet in the
  enforced gate (Coulomb relative compactness via integral kernels); and the `QuantumMechanics/Logic/`
  quantum-logic development. These are honest works-in-progress, not placeholders — nothing
  downstream assumes them.

A CI workflow ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs the build+gate, the
statement-level [`NumericChecks`](NumericChecks/README.md) suite, and a `scripts/check_lengths.py`
length ratchet on every push and pull request. A companion `scripts/check_compile_time.py` times
each file's isolated elaboration and flags anything slower than 5s against a baseline
([`scripts/compile-time-baseline.txt`](scripts/compile-time-baseline.txt)); see
[CONTRIBUTING.md](CONTRIBUTING.md#compile-time-monitoring) for how to run it.

### Statement-level checks — the second gate

`AxiomCheck` proves the *proofs* are honest, but a machine cannot tell whether a **statement**
encodes the intended mathematics: a dropped factor of 2, a flipped sign, or a wrong normalization
is proved just as rigorously as the correct claim, and passes the axiom gate. The
[`NumericChecks/`](NumericChecks/README.md) suite closes that gap. It is pure-stdlib Python (no
numpy) that transcribes the library's definitions *literally* — each check cites the Lean
`file:line` it validates — and compares them against high-precision numerics computed by an
**independent route**, on finite models where the two sides take genuinely different values (so an
expression-identity bug cannot fake a pass). A failure points at a statement-level bug in a named
declaration.

The 341 checks span the whole tower: hydrogen (Laguerre normalization/orthogonality, `Eₙ`,
Bohr/Balmer against the H-α line), the Hardy constant and its sharpness, Cramér–Rao and the
quantum Fisher metric, CHSH/Tsirelson, and — validating the newest operator-algebra layers on
concrete matrix models — **Tomita–Takesaki** (`Δ = S⋆S` built from the abstract antilinear Tomita
graph *equals* the closed form `ρ(·)ρ⁻¹`; `S = JΔ^½`, `J M J = M′`, `log Δ = [log ρ, ·]`), the
**KMS** `β`-convention boundary condition, the `M₂(M)` commutant identity, the **Cayley/resolvent/
Weyl/Stone** conventions, and **Schrödinger–Robertson** uncertainty. The suite is mutation-tested
(deliberately injected sign/factor bugs are caught) and its scope, conventions, and known
limitations are documented in [`NumericChecks/README.md`](NumericChecks/README.md). Run it with
`python3 NumericChecks/run_all.py` (~11 s).

### Hypothesis hygiene — the forensic gate

`NumericChecks` catches a statement that computes the *wrong value*; a complementary failure is a
statement that assumes *more than it proves*. The [`ForensicCheck`](ForensicCheck.lean) gate — the
statement-level analogue of `AxiomCheck`, and likewise a `@[default_target]` — scans every theorem
in `Spectra.*` and fails `lake build` if any carries a normally-named but **unused** hypothesis: a
declared `Prop`-hypothesis whose proof term never touches it, which makes the statement over-strong
or (if the hypothesis is unsatisfiable) vacuously true. Hypotheses kept on purpose are exempted by
the `_`-prefix convention — the author's own signal that an argument is intentionally unused. The
engine ([`Forensic.lean`](Forensic.lean)) also computes each headline theorem's **transitive
assumption cone**: the set of `Spectra` lemmas its proof rests on (Mathlib is the trusted boundary),
the marginal assumptions the whole tower leans on (ambient Hilbert/measure structure quotiented
out), the base leaves, and the axiom foundation — written to `docs/spectra-forensic.json` by
`scripts/forensic_report.sh`.

---

## Building

```sh
# install elan (https://github.com/leanprover/elan), then:
git clone <your-fork-url> Spectra
cd Spectra
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build           # builds the library and runs the axiom gate
```

The recommended editor is **VS Code with the Lean 4 extension**.

---

## Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the workflow and [`STYLE.md`](STYLE.md) for
conventions. The non-negotiables: the Apache 2.0 copyright header, a module docstring, a `/-- … -/`
docstring on every declaration, a clean `lake build` with no new `sorry` in finished files, and —
when you add a headline result — an `assert_no_sorry` line in [`AxiomCheck.lean`](AxiomCheck.lean).

---

## License

Apache 2.0 — see [`LICENSE`](LICENSE). Copyright © 2026 Spectra Formalization Project.

---

## References

Cited per-file in `## References` blocks. Principal sources: Reed & Simon, *Methods of Modern
Mathematical Physics* (I–IV); Kato, *Perturbation Theory for Linear Operators*; Bratteli &
Robinson, *Operator Algebras and Quantum Statistical Mechanics* and Takesaki, *Theory of Operator
Algebras* (KMS / Tomita–Takesaki); Simon, *Trace Ideals and Their Applications*; and Amari &
Nagaoka, *Methods of Information Geometry*.

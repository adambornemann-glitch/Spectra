# Spectra — TODO

Working notes that travel with the repo (the live planning notes otherwise live in the
machine-local Claude memory). Last updated 2026-06-14.

---

## NEXT UP — (b) Wire the concrete Dirac operator into the abstract spectrum theorems

**Context.** `QuantumMechanics/DiracEquation/` is two disconnected layers:

- **Concrete** — `FreeHamiltonian.lean` builds the honest self-adjoint free Dirac operator
  `H_D = -iα·∇ + βmc²` on `L²(ℝ³;ℂ⁴)` and its Stone evolution `diracUnitaryGroup mc2`, with
  `generator (diracUnitaryGroup mc2) = diracHamiltonian mc2` (all sorry-free). **Used by nothing.**
- **Abstract** — `Operators.lean` defines a `DiracHamiltonian` structure wrapping an *unconstrained*
  `OneParameterUnitaryGroup`. Its physics theorems (`dirac_unbounded_below/above`,
  `dirac_not_semibounded`) carry **undischarged** hypotheses `h_spectrum_below/above`, and the
  structure is **never instantiated**.

(b) connects them so the abstract theorems become statements about the real operator.

### The clean 4-step route

**Step 1 — Instantiate (mechanical).**
Build `DiracHamiltonian DiracSpinorL2 DiracConstants M` with `U_grp := diracUnitaryGroup mc2`.
Because `generator (diracUnitaryGroup mc2) = diracHamiltonian mc2`, after this `generator H_D.U_grp`
*is* the concrete operator and `(generator H_D.U_grp).domain = SobolevDiracH1`, so every
`Operators.lean` / `Unitarity/FirstLawEqiv.lean` theorem becomes a statement about the real operator.
- `K := DiracConstants` (carries ℏ, c, m + positivity; `restEnergy = m·c²`).
- `matrices : M` is opaque/unconstrained — pass `standardGammaMatrices` (`Current.lean:97`) or `Unit`;
  OR first improve the structure to actually carry the Clifford witness (see Cleanup below).

**Step 2 — Reusable bridge lemma (find-or-prove; general, not Dirac-specific).**
`generator_has_arbitrarily_negative_energy` (`SpectralTheory/Algebra.lean:579`) needs
`∀ N, ∃ φ, spectralProjection U_grp (Iic N) measurableSet_Iic φ ≠ 0`.
Discharge it with the standard one-direction fact — **energy expectation below N ⟹ spectral mass
below N**:

> `φ ∈ (generator U).domain → (⟪generator U φ, φ⟫_ℂ).re < N·‖φ‖² → spectralProjection U (Iic N) φ ≠ 0`

(contrapositive: if all spectral mass were in `[N,∞)`, then `⟪Aφ,φ⟫ ≥ N‖φ‖²`). This avoids the full
PVM↔Fourier-multiplier identification — we only need this one direction.
`spectralProjection` is `SpectralTheory/Measure/Convergence.lean:157`. **Check
`SpectralTheory/Measure/GeneratorLink.lean` and `Algebra.lean` first** — the engine internals
(`spectralProjection_energy_upper_bound`, `spectralProjection_finite_approx_below`) may already give
this.

**Step 3 — Negative-energy wavepacket (the real new analysis; medium-large).**
For each `N`, build a nonzero `ψ_N ∈ SobolevDiracH1` with `(⟪H_D ψ_N, ψ_N⟫_ℂ).re < N·‖ψ_N‖²`; Step 2
then gives `h_spectrum_below`. Symmetric (`Ici`/above) for the upper bound.
- **Full Fourier symbol of `H_D`** is `Ĥ(ξ) = 2π(α·ξ) + mc²·β = diracMomentumOp (2π•ξ) mc²`.
  NOTE: the existing `diracKineticSymbol ξ = 2π·diracMomentumOp(ξ,0)` is **kinetic-only** — the mass
  term `mc²·β` must be added (small new symbol plumbing). `diracMomentumOp_sq` (`Dispersion.lean:75`)
  ⇒ `Ĥ(ξ)² = E(ξ)²•1` with `E(ξ) = √((2π‖ξ‖)² + (mc²)²)`, so eigenvalues `±E(ξ)`.
- **Projector** `P₋(ξ) = ½(1 − Ĥ(ξ)/E(ξ))` (rank 2). Set `ψ̂(ξ) := g(ξ)·P₋(ξ)v₀`, `v₀ : ℂ⁴` fixed,
  `g` an L² bump on a high-momentum annulus where `E(ξ) ≥ E₀`. Then `Ĥ(ξ)ψ̂(ξ) = −E(ξ)ψ̂(ξ)` exactly,
  so `⟪H_D ψ,ψ⟫ = −∫ E(ξ)‖ψ̂(ξ)‖² ≤ −E₀‖ψ‖²`. Pick the annulus so `−E₀ < N`.
- **Plancherel bridge**: `⟪H_D ψ,ψ⟫ = ⟪spinorFourierL2 (H_D ψ), spinorFourierL2 ψ⟫`. Need
  `spinorFourierL2 (H_D ψ) = (ξ ↦ Ĥ(ξ)·)(spinorFourierL2 ψ)`: kinetic part via existing
  `fourier_diracKineticFn_symbol`; mass part via a tiny new lemma
  `spinorFourierL2 ∘ matrixOp M = matrixOp M ∘ spinorFourierL2` (𝓕 is componentwise, matrixOp mixes
  components linearly — trivial).
- `ψ ≠ 0` (generic `v₀` with `P₋(ξ)v₀ ≠ 0`) and `ψ ∈ H¹` (`g` compact-support ⇒ `ψ̂` compact-support).

**Step 4 — Specialize + state the spectrum.**
With `h_spectrum_below/above` discharged, `dirac_unbounded_below/above`/`dirac_not_semibounded`
(`Operators.lean:134/145/163`) become genuine for the concrete operator. Then state
`σ(diracHamiltonian mc2) = (−∞,−mc²] ∪ [mc²,∞)` + mass gap — this needs the **full** spectral
characterization (both directions of the PVM↔Fourier bridge), a larger follow-on. NB
`sector_orthogonal` (`Unitarity/FirstLawEqiv.lean:401`) only proves cutoff-disjointness, NOT the gap.

### Open questions to resolve first
1. Does `SpectralTheory/Measure/GeneratorLink.lean` already have the Step-2 energy⟹spectral-mass lemma?
   If yes, (b) is mostly Step 1 + Step 3.
2. Exact signatures of `spectralProjection_energy_upper_bound` / `spectralProjection_finite_approx_below`.
3. Confirm + add `spinorFourierL2 ∘ matrixOp = matrixOp ∘ spinorFourierL2`.
4. Decide `K`/`M`: minimal (`Unit`) vs meaningful (`DiracConstants`, `GammaMatrices`).

### Effort
Step 1 small · Step 2 small–medium (likely reuses engine internals) · Step 3 medium–large (genuine
new analysis) · Step 4 spectrum large (defer).

---

## Status snapshot (DiracEquation)

- **Sorry-free** and axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only). Completeness audit
  2026-06-14 found **no false/vacuous theorems**.
- `FreeHamiltonian.lean`: free Dirac op self-adjoint (Kato–Rellich), surjectivity of `D₀ ± iμ` via
  the matrix resolvent multiplier — done 2026-06-14.
- Matrix layer (`CliffordAlgebra`, `Dispersion`, `Spin`, `Chirality`, `GammaTrace`, `Current`): real,
  entrywise-verified; lives at the 4×4 matrix level, **not yet lifted to the L² operator**.
- `Current`/`Conservation`: local current conservation `∂ᵤjᵘ = 0` proved (conditional on the Dirac
  equation as a hypothesis). Global probability conservation + Born rule are in
  `QuantumMechanics/BornRule/Conservation.lean` (**sorry-free**).
- Docstrings cleaned 2026-06-14 (removed overclaims/stale markers).

### DiracEquation enrichment (lower priority, after (b))
- Lift chirality projectors `P_L/P_R` to an L² subspace decomposition of `DiracSpinorL2` (+ `Tr P_L = 2`).
- Spin operator `S = (ℏ/2)Σ` and total angular momentum conservation `[H_D, J] = 0` (the stated but
  unformalized payoff of `Spin.lean`).
- Current reality `(jᵘ).im = 0` from `gamma0_gamma_selfadjoint` (`Current.lean:222`).
- Instantiate `Conservation`/`BornRule` on actual solutions `e^{-itH_D}ψ` (not a free `h_dirac`).
- Cleanup: `CliffordOperators.lean` is orphaned (FreeHamiltonian builds `H_D` from `matrixOp`
  directly); `scalarResolventSolve` (`DiracFourier.lean:221`), `diracAdjoint`/`SpinorField'`,
  `spinAt` are unused. Either wire in or mark as standalone. Constrain or delete `Operators.lean`'s
  opaque `matrices`/`constants` fields.

---

## Other outstanding work elsewhere (real `sorry`s)

- `QuantumMechanics/Hydrogen/Spectrum.lean` — 10 sorries (sector decomposition, eigenvalue equation,
  continuous spectrum). Mostly untyped scaffolds; do not fake.
- `QuantumMechanics/Hydrogen/RadialProblem/RadialEquation.lean` — 3 (named analytic gaps).
- `QuantumMechanics/Hydrogen/RadialProblem/SphericalLaplacian.lean` — 2 (‖·‖-origin localization +
  full separation).
- `QuantumMechanics/Hydrogen/Laplacian.lean` — 1 (`freeGreensFunction`).
- `QuantumMechanics/Perturbation/HardySharp.lean` — 1.
- `Mathlib/StochasticCalc/…` — a few (`PVariation/TODO.lean`, `YoungIntegration/.../Consistency.lean`,
  `SewingLemma/.../RefiCo.lean`); separate stochastic-calculus track.

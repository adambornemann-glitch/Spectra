# NumericChecks

Numeric validation of Spectra's formalized statements, in pure-stdlib Python
(no numpy/scipy — runs anywhere `python3` does).

## Why

Lean guarantees the *proofs* are correct; it cannot tell you whether the
*statements* formalize the intended physics. A wrong normalization constant, a
dropped factor of 2, or a sign error in a definition would be proved
"correctly" and pass `AxiomCheck`. These scripts transcribe the library's
definitions literally (each `lean_*` function cites its `file:line`) and check
the theorem statements against high-precision numerics, so a failure points at
a *statement-level* bug in a specific Lean declaration.

## Design rule: independent routes

A check is only as good as the independence of its two sides. Every check
here computes the quantities a theorem *relates* via separate numeric routes —
scores by finite-differencing log-densities, Fisher information by integrating
those FD scores, estimator means/variances by quadrature, derivatives both by
textbook identities *and* by pure finite differences on the literal Lean
transcriptions — and prefers models where the related quantities take
*different* values (e.g. Cramér–Rao on N(θ, σ=2): g = 1/4 while Var = 4), so
that an expression-identity bug cannot fake a pass. Checks that would reduce
to `x ≤ x` or mirror an algebraic-identity theorem are replaced by external
anchors (e.g. the H-α line at 656.11 nm instead of re-deriving Bohr algebra).

## Run

```sh
python3 run_all.py          # everything (~1 min)
python3 check_hydrogen.py   # one suite
```

Exit code 0 iff all checks pass.

## Suites

| Suite | Checks | What it validates |
|---|---|---|
| `selftest.py` | 17 | The toolkit itself (quadrature, Laguerre, ₁F₁, Legendre) against textbook values. If this fails, trust nothing else. |
| `check_hydrogen.py` | 86 | `laguerrePolynomial` (explicit sum w/ `realBinom`) ≡ standard convention; `laguerre_recurrence`, `laguerre_differential_eq`, `laguerre_orthogonality` (+ diagonal norm Γ(n+α+1)/n!); `radialNormalization` (∫R²r²dr = 1); radial orthogonality; `radial_eigenvalue_eq` (H_ℓR = EₙR pointwise) via analytic derivatives **and** via identity-free finite differences on the literal transcription; **independent** energy quadrature ⟨T⟩+⟨V⟩ = −1/(2n²) + virial theorem; ground state R₁₀ = 2e⁻ʳ, E₁ = −1/2; Bohr/Balmer + **H-α reality anchor (656.11 nm)**; L_m^α(0) Gamma identity; `freeGreensFunction` (Helmholtz eq., total mass −1/z, complex Laplace sin integral); boundary limit r→0. |
| `check_hardy.py` | 43 | `hardy_inequality` constant 4 on assorted H¹ radial functions; `hardy_constant_sharp` via the Emden–Fowler family (ratio ↑ 4, matches the closed form implied by `gN'`); `gN'` really is d/dr `gN`; `hardy_operator_bound` with C(ε)=1/ε at fixed instances **and** over each profile's worst dilation, plus the structural test that min-over-dilation is ε-invariant ⟺ C ∝ 1/ε; `coulomb_relatively_bounded_H2` with C=Z²/ε; `coulomb_norm_eq`. |
| `check_infogeom.py` | 45 | `gaussianShiftModel_fisherMatrix` = RᵀR by genuine 2D quadrature of ∫sᵢsⱼp (asymmetric R, so RRᵀ would fail); `scoreFun` ≡ FD of log p in θ; density normalization; score mean zero; `classicalBitData` metric ≡ 4 and `bitCubic` = 16·cot 2α with FD scores; `qubitData` metric = diag(1, sin²α) against the SLD metric of the Bloch family; `cramerRao_scalar` on four models with all ingredients on independent routes (FD score → Fisher; quadrature+FD → τ'; quadrature → Var): efficient cases with g = 1/4, 4, 1/θ², 4 (equality attained) and one strictly inefficient estimator (positive gap). |
| `check_misc.py` | 46 | CHSH classical bound 2 (corners + 20k random); `tsirelson_bound` 2√2 attained on the Bell state and never exceeded on a 24⁴ angle grid; dichotomic bound; `kummerM_ode` residuals via contiguous identities **and** via pure FD on the series; Kummer e^{ρ/2} growth; Dirac `diracMomentumOp_sq`/`_hermitian`/`_factor` (D² = (|p|²+m²)I etc.); `heisenberg_uncertainty` (Gaussian equality σₓσₚ = 1/2, excited states above); `poissonKernel_fourier` = e^{−ε|t|}; spherical harmonic eigenvalue ℓ(ℓ+1) and orthonormality. |

Total: **237 checks**, all passing as of 2026-07-02.

## Mutation testing

The suites were sanity-tested by injecting deliberate bugs and confirming
they fail:

| Mutation | Result |
|---|---|
| Cramér–Rao bound computed as τ'²·g instead of τ'²/g | **caught** (4 failures, incl. the bare inequality on the g=4 model) |
| Hydrogen decay e^{−r/n} → e^{−r/(2n)} | **caught** (45 failures) |
| Fisher expected value RRᵀ instead of RᵀR | **caught** (4 failures; R is asymmetric by design) |
| Hardy intercept C = 1/ε² (wrong ε-scaling) | **caught** (2 failures via the ε-invariance test) |
| Hardy intercept C = 1/(2ε) | **not caught — correctly**: the halved-intercept inequality appears to be *true* (all profiles give min dilation ratio ≥ ~1.9), so Lean's C(ε)=1/ε is a valid-but-not-sharp constant. Numerics can falsify wrong statements, not detect slack in true ones. |

## Conventions verified

- Atomic units, H = −½Δ − Z/r (half-Laplacian), Eₙ = −Z²/(2n²).
- "Mathematician's" Laguerre L_n^α (L₁ = 1+α−x), weight x^α e^{−x} on (0,∞).
- Hardy constant **4** on the gradient side: ∫|ψ|²/|x|² ≤ 4∫|∇ψ|².
- ℏ = 1 uncertainty ℏ/2; natural-units Dirac dispersion E² = |p|² + m².

## Caveats

- Representation-dependent details (Dirac matrix rep, spherical-harmonic
  phase) are checked against the standard convention; the Lean theorems are
  representation-invariant, so this validates content, not the specific basis.
- `classicalBitData`/`qubitData` are *definitions* of `GeometricData`; the
  checks confirm they match the Fisher/SLD metrics of the intended families
  (Bernoulli (cos²α, sin²α) and Bloch pure states, respectively).
- Tolerances are set to quadrature/finite-difference accuracy (1e-6 – 1e-12);
  any real constant/sign/normalization error fails by many orders of
  magnitude.

## Toolkit (`nclib/`)

- `quadrature.py` — tanh-sinh (finite intervals, endpoint singularities OK)
  and exp-sinh (0,∞) double-exponential rules, complex-valued integrands
  supported.
- `special.py` — generalized Laguerre (recurrence), Kummer ₁F₁ (series),
  associated Legendre / spherical harmonic θ-factor.
- `harness.py` — `check` / `check_le` with per-check Lean declaration
  citations, summary report, exit code.

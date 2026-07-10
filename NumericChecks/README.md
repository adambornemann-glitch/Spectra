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
| `selftest.py` | 36 | The toolkit itself (quadrature, Laguerre, ₁F₁, Legendre, complex linear algebra, Hermitian functional calculus, **Hermitian eigenvectors** with degeneracy) against textbook values. If this fails, trust nothing else. |
| `check_hydrogen.py` | 86 | `laguerrePolynomial` (explicit sum w/ `realBinom`) ≡ standard convention; `laguerre_recurrence`, `laguerre_differential_eq`, `laguerre_orthogonality` (+ diagonal norm Γ(n+α+1)/n!); `radialNormalization` (∫R²r²dr = 1); radial orthogonality; `radial_eigenvalue_eq` (H_ℓR = EₙR pointwise) via analytic derivatives **and** via identity-free finite differences on the literal transcription; **independent** energy quadrature ⟨T⟩+⟨V⟩ = −1/(2n²) + virial theorem; ground state R₁₀ = 2e⁻ʳ, E₁ = −1/2; Bohr/Balmer + **H-α reality anchor (656.11 nm)**; L_m^α(0) Gamma identity; `freeGreensFunction` (Helmholtz eq., total mass −1/z, complex Laplace sin integral); boundary limit r→0. |
| `check_hardy.py` | 43 | `hardy_inequality` constant 4 on assorted H¹ radial functions; `hardy_constant_sharp` via the Emden–Fowler family (ratio ↑ 4, matches the closed form implied by `gN'`); `gN'` really is d/dr `gN`; `hardy_operator_bound` with C(ε)=1/ε at fixed instances **and** over each profile's worst dilation, plus the structural test that min-over-dilation is ε-invariant ⟺ C ∝ 1/ε; `coulomb_relatively_bounded_H2` with C=Z²/ε; `coulomb_norm_eq`. |
| `check_infogeom.py` | 45 | `gaussianShiftModel_fisherMatrix` = RᵀR by genuine 2D quadrature of ∫sᵢsⱼp (asymmetric R, so RRᵀ would fail); `scoreFun` ≡ FD of log p in θ; density normalization; score mean zero; `classicalBitData` metric ≡ 4 and `bitCubic` = 16·cot 2α with FD scores; `qubitData` metric = diag(1, sin²α) against the SLD metric of the Bloch family; `cramerRao_scalar` on four models with all ingredients on independent routes (FD score → Fisher; quadrature+FD → τ'; quadrature → Var): efficient cases with g = 1/4, 4, 1/θ², 4 (equality attained) and one strictly inefficient estimator (positive gap). |
| `check_misc.py` | 46 | CHSH classical bound 2 (corners + 20k random); `tsirelson_bound` 2√2 attained on the Bell state and never exceeded on a 24⁴ angle grid; dichotomic bound; `kummerM_ode` residuals via contiguous identities **and** via pure FD on the series; Kummer e^{ρ/2} growth; Dirac `diracMomentumOp_sq`/`_hermitian`/`_factor` (D² = (|p|²+m²)I etc.); `heisenberg_uncertainty` (Gaussian equality σₓσₚ = 1/2, excited states above); `poissonKernel_fourier` = e^{−ε|t|}; spherical harmonic eigenvalue ℓ(ℓ+1) and orthonormality. |
| `check_modular.py` | 29 | **Tomita–Takesaki** on the canonical finite model `M = M_n(ℂ)` acting on the Hilbert–Schmidt space, `Ω = ρ^{½}`: modular operator `Δ = S⋆S` built from the abstract antilinear Tomita graph `S(xΩ)=x⋆Ω` (via realification) **vs** the closed form `ρ(·)ρ⁻¹`; `modularOp_nonneg` `Re⟨Δξ,ξ⟩ = ‖Sξ‖²`; `(Δ^{½})²=Δ`; `Δ⁻¹`, `Δ^{-½}`; `J` antiunitary + `J²=1`; polar `S=JΔ^{½}` + `S²=1`; commutation `JL_aJ=R_{a⋆}` (`JMJ=M'`); vacuum fixed by `Δ, Δ^{½}, Δ^{it}`; modular flow unitary + group law + `σ_t(M)=M`; **modular Hamiltonian** `log Δ = [log ρ,·]` and `Δ^{it}=e^{it·logΔ}`; `ω(a)=⟨Ω,aΩ⟩=Tr(ρa)`. |
| `check_kms.py` | 10 | **KMS on the Gibbs model** `ρ_β = e^{-βH}/Z`, `α_t(b)=e^{itH}be^{-itH}`, `F(z)=Tr(ρ_β a σ_z(b))`: lower boundary `F(t)=ω(a·α_t b)`; **the β-convention upper boundary** `F(t+iβ)=ω(α_t(b)·a)` (left side = analytic continuation, right side = plain product — disjoint matrix expressions), with a guard that `−iβ` fails; holomorphicity `∂F/∂z̄=0`; imaginary-time `ω(a·σ_{iβ}b)=ω(ba)`; invariance `ω(α_t a)=ω(a)`; generator `δ(a)=i[H,a]` (FD vs commutator); `ω(δa)=0`; temperature rescaling `rescale(β/β₂)`. |
| `check_cocycle.py` | 10 | **M₂(M) amplification**: `blockOp` composition = matrix multiplication; `blockOp_star`; matrix units. **The subtle centralizer identities** on a *proper* algebra `M=M_k⊗I_m`: `dim centralizer(M₂(M)) = m²` (scalar blocks `M'⊗1₂`) — **not** `4m²` (`M₂(M')`), computed by a null-space route independent of the closed form; the reverse `centralizer(M⊗1₂)=M₂(M')` at `dim 4m²`; explicit ⊇ and the `M₂(M')⊄centralizer` witness. |
| `check_spectral.py` | 19 | **Cayley/resolvent/Weyl/generator**: `C = I−2i(A+iI)⁻¹ = (A−iI)(A+iI)⁻¹`, unitary/isometry; `C(Aψ+iψ)=Aψ−iψ`; `(I∓C)(Aψ+iψ)=2iψ / 2Aψ`; Möbius eigenvalue correspondence `μ∈σ(A)⇔(μ−i)/(μ+i)∈σ(C)` (via `det`); `−1∈σ(C)⇔0∈σ(A)`; `σ(C)⊆` unit circle; resolvent identity `R(z)−R(w)=(z−w)R(z)R(w)`; `R(z)⋆=R(z̄)`; continuity bound; Neumann series; Stone generator `(U(t)ψ−ψ)/(it)→Aψ`; Weyl criterion via `min‖(A−λ)ψ‖=dist(λ,σ)`. |
| `check_uncertainty.py` | 21 | **Schrödinger–Robertson** `Var(A)Var(B) ≥ ¼‖⟨[A,B]⟩‖²+Cov²` (three disjoint routes; **exact saturation** at pure qubit states) and the weaker Robertson bound; `Cov=½Re⟨{A,B}⟩−⟨A⟩⟨B⟩`; Pauli algebra (`σ_x²=I`, `[σ_x,σ_y]=2iσ_z`, `{σ_x,σ_y}=0`); Ehrenfest `d/dt⟨B⟩=⟨iAψ,Bψ⟩+⟨ψ,B iAψ⟩`; energy-expectation conservation + spectral-measure invariance under `e^{itA}`; Hilbert tensor cross-norm `‖x⊗y‖=‖x‖‖y‖`, `⟨x⊗y,x'⊗y'⟩=⟨x,x'⟩⟨y,y'⟩`; quantum-Fisher `G=4Cov` PSD, RLD Pythagorean `|g+iω|²=g²+ω²`, bilinear bound, `RᵀR=G`. |
| `check_entropy.py` | 32 | **Von Neumann entropy / Klein / Gibbs / cross-entropy** on faithful non-commuting `ρ,σ` (3×3). `S(ρ)=tr(−ρ log ρ)` by **three** routes — eigenvalue sum `Σ negMulLog λᵢ`, operator `Re tr(cfc negMulLog ρ)`, literal `Re tr(−ρ log ρ)` — validating `vonNeumannEntropy_eq_tsum`; pure-state `S=0`; `S(I/d)=log d` sign/base anchor. Cross entropy `−Tr(ρ log σ)` by **two** disjoint routes (the literal spectral-measure form `Σᵢλᵢ Σⱼ\|⟨eᵢ,fⱼ⟩\|²(−log sⱼ)` vs `−Re tr(ρ log σ)`); the chain `S(ρ) ≤ measuredCrossEntropy = Σ−λᵢ log sᵢ ≤ crossEntropy` (Gibbs leg + Jensen bridge, genuine slack since `ρ≠σ`); `D(ρ‖σ)>0` strict, `crossEntropy(ρ,ρ)=S(ρ)` (Klein equality case); the scalar `Real.klein_scalar`; four falsification guards. |
| `check_traceclass.py` | 29 | **Uhlmann fidelity / Schatten norms / polar / BKM**. `F(ρ,σ)=‖√ρ√σ‖₁` = the textbook `tr√(√ρσ√ρ)` (two Hermitian matrices, same spectrum); `F(ρ,ρ)=tr ρ` (unnormalized), `F(ρ,σ)=F(σ,ρ)` (SVDs of the two *different* matrices `√ρ√σ`, `√σ√ρ`), `F≤√(trρ·trσ)`, `F≤1`, pure-state anchor `F=√⟨ψ\|σ\|ψ⟩`. `traceNorm_adjoint ‖A⋆‖₁=‖A‖₁` via singular values of `AA⋆` vs `A⋆A` (**value** pinned ≠ `Σσ²`); Schatten–Hölder `‖XY‖₁≤‖X‖₂‖Y‖₂` (+ rank-one sharpness); `‖√ρ‖₂=√trρ`; polar `U\|A\|=A`, `\|A⋆\|=U\|A\|U⋆`. **BKM**: kernel `tr(Aτ⁻¹Bτ⁻¹)` symmetric/PSD/bilinear, and the metric `∫₀^∞ Re tr(A(ρ+s)⁻¹B(ρ+s)⁻¹)ds` by **double-exponential quadrature = the Kubo–Mori closed form** `Σ Ãₖₗ B̃ₗₖ (log pₖ−log pₗ)/(pₖ−pₗ)`; three guards. |
| `check_fock.py` | 54 | **Fock / coherent states / (anti)symmetrizers / number op** (tensor powers + `Sₙ` permutation rep built in-file, sanity-checked). `⟨f^⊗n,g^⊗n⟩=⟨f,g⟩ⁿ`; `expCoeff=(√n!)⁻¹`; sector overlap `⟨εfₙ,εgₙ⟩=⟨f,g⟩ⁿ/n!`; the **coherent formula** `⟨ε(f),ε(g)⟩=exp⟨f,g⟩` and `‖ε(f)‖²=exp‖f‖²` (truncated tensor sum → transcendental exp); `symProj`/`altProj` idempotent, self-adjoint, ranks `C(d+n−1,n)`/`C(d,n)`, mutually orthogonal; **Pauli** `altProj(v⊗v)=0` (non-trivially); Slater norm `‖altProj(⊗ON)‖²=1/n!`; `numberOp` eigen-action `N=n` per sector, self-adjoint, `≥0`; exp-Gram positive-definiteness ⇒ linear independence of `ε(fᵢ)`; three guards (incl. the pre-correction `1/n!`→₀F₁ bug). |
| `check_krein_gauge.py` | 72 | **Krein spaces + lattice gauge / Yang–Mills**. Krein: `FundamentalSymmetry` `J†=J`, `J²=1`, indefinite; `kreinInner` two slot forms `⟨Jx,y⟩=⟨x,Jy⟩`; `posProj=(I+J)/2` (vs the *spectral* projector, non-diagonal `J`); `negPart=posPart⊥`; definiteness on `H±`; `kreinAdjoint J A†J`, involutive, `IsKreinSelfAdjoint ⟺ (JA)†=JA` (true+false models); Fock `[ξ,η]=Σ⟨J^⊗nξₙ,ηₙ⟩`. Gauge (algebraic): plaquette holonomy `ABC⁻¹D⁻¹` (dense inverse vs `†`); `−n≤Re tr U≤n` (tight at `±I`); `plaquetteAction=n−Re tr U_P ∈[0,2n]`; `wilsonAction=βΣ≥0`, `≤β·P·2n`; `\|A_ij\|≤1`. Measure surrogates (finite-subgroup): Haar probability + **left-invariance over Q₈**; partition function `0<Z≤1`; reflection positivity `∫conj(f∘Θ)·f=\|⟨f⟩\|²≥0` (Z₂). QFT `rankOneProjection=\|v⟩⟨v\|`; four guards. |

Total: **532 checks**, all passing (237 → 341 with the modular/KMS/cocycle/spectral/uncertainty
expansion of 2026-07-04; 341 → 532 with the entropy/trace-class/Fock/Krein-gauge expansion of
2026-07-07, which covers the recent Klein-inequality, Uhlmann-fidelity, BKM-metric, coherent-state,
and lattice-Yang–Mills keystones).

## Every check is *live* (automated mutation testing)

A check that passes is worthless unless it would *fail* on a wrong statement. `mutation_test.py`
proves this automatically and exhaustively: for **every** `check`/`check_le` call in every suite it
re-runs the suite with that one check's computed value corrupted (via an opt-in `NC_MUTATE` hook in
`harness.py` that has zero effect on a normal run) and confirms the suite then fails. A green run
certifies that all **532 checks are live** — none is comparing a quantity to itself, and no tolerance
is loose enough to swallow a real discrepancy. This is the automated, always-runnable form of the
by-hand mutation table below.

```sh
python3 mutation_test.py                     # every check in every suite (~1–2 min)
python3 mutation_test.py check_entropy.py     # one suite
```

In addition, each new suite carries **embedded falsification guards** — checks that *pass iff a
documented wrong transcription fails* (sign flips, `ρ↔σ` swaps, dropped square roots, `τ`↔`τ⁻¹`,
`1−U_P`↔`1+U_P`, the pre-correction Fock coefficient, `exp(+S)`, non-subgroup averaging). These make
the most important mutations permanent, in-suite regression tests rather than one-off experiments.

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
| Modular `Δ=S⋆S` computed as `ρ⁻¹(·)ρ` (ρ↔ρ⁻¹ swapped) | **caught** (route deviation 3.1 vs 1e-15) — the abstract-graph route and the closed form diverge |
| Modular Hamiltonian `log Δ` as `{log ρ,·}` (anti- instead of commutator) | **caught** (deviation 3.3) |
| KMS upper boundary with `−iβ` instead of `+iβ` | **caught** (deviation 3.4; +iβ control 1e-15) |
| Cocycle centralizer claimed `M₂(M')` (dim 4m²=16) instead of `M'⊗1₂` (dim m²=4) | **caught** (dimension 4 ≠ 16) |
| Cayley `C = I+2i(A+iI)⁻¹` (wrong `i`-sign) | **caught** — mutated `C` is not unitary (deviation 5.2) |
| Schrödinger–Robertson with an inflated `(3·Cov)²` term | **caught** — the (saturated) bound would exceed `Var·Var` |
| Klein relative entropy with the cross term mis-signed (`+Tr(ρ log σ)`) | **caught** (embedded guard) — `D` goes negative |
| Cross entropy `ρ↔σ` swapped | **caught** (embedded guard) — argument order changes the value |
| Gibbs bound using σ's eigenvalues instead of its ρ-diagonal | **caught** (embedded guard) — different number on non-commuting σ |
| Fidelity with the square roots dropped (`‖ρσ‖₁`) | **caught** (embedded guard) — ≠ `‖√ρ√σ‖₁` |
| BKM kernel with `τ` instead of `τ⁻¹` | **caught** (embedded guard) — `tr(AτBτ) ≠ tr(Aτ⁻¹Bτ⁻¹)` |
| Coherent coefficient `(n!)⁻¹` instead of `(√n!)⁻¹` | **caught** (embedded guard) — sum is `₀F₁`, not `exp` |
| Fermionic antisymmetrizer with the sign dropped | **caught** (embedded guard) — Pauli `altProj(v⊗v)=0` fails |
| Number operator with the `n²` eigenvalue law | **caught** (embedded guard) — differs at sector 3 (9 ≠ 3) |
| Wilson density `1+U_P` instead of `1−U_P` | **caught** (embedded guard) — vacuum action `2n ≠ 0` |
| Boltzmann weight `exp(+S)` instead of `exp(−S)` | **caught** (embedded guard) — `Z ≥ 1` violates `Z ≤ 1` |
| Haar "invariance" averaged over a non-subgroup subset | **caught** (embedded guard) — reindexing is not measure-preserving |
| **Every** individual check, computed value corrupted | **caught** — `mutation_test.py` confirms all 532 are live |

## Conventions verified

- Atomic units, H = −½Δ − Z/r (half-Laplacian), Eₙ = −Z²/(2n²).
- "Mathematician's" Laguerre L_n^α (L₁ = 1+α−x), weight x^α e^{−x} on (0,∞).
- Hardy constant **4** on the gradient side: ∫|ψ|²/|x|² ≤ 4∫|∇ψ|².
- ℏ = 1 uncertainty ℏ/2; natural-units Dirac dispersion E² = |p|² + m².
- Modular: `Δ = S⋆S` with `S(xΩ)=x⋆Ω`, `Δξ=ρξρ⁻¹` on `Ω=ρ^{½}`; `S=JΔ^{½}`; `generator(Δ^{it})=+log Δ`.
- KMS (Bratteli–Robinson): strip `0<Im z<β`, lower `ω(a·α_t b)`, upper `ω(α_t(b)·a)` at `Im=β`.
- Cayley `C = I−2i(A+iI)⁻¹`, Möbius `μ↦(μ−i)/(μ+i)`; Schrödinger–Robertson keeps the `+Cov²` term.
- Entropy: `S(ρ)=tr(−ρ log ρ)=Σ negMulLog λᵢ` (natural log; `negMulLog x = −x log x`), `crossEntropy(ρ,σ)=−Tr(ρ log σ)`, `measuredCrossEntropy=Σ−λᵢ log sᵢ` with `sᵢ=re⟨eᵢ,σeᵢ⟩` (σ's ρ-diagonal); Klein `S(ρ)≤crossEntropy` (faithful σ).
- Fidelity `F(ρ,σ)=‖√ρ√σ‖₁` (the **root** Uhlmann fidelity `= tr√(√ρσ√ρ)`, not `F²` or Bures); trace norm `‖·‖₁=Σσᵢ`, HS norm `‖·‖₂=√Σσᵢ²`; BKM kernel `tr(Aτ⁻¹Bτ⁻¹)`, metric `∫₀^∞ …ds`.
- Fock: inner product **conjugate-linear in the first slot**; **no** `n!` weight on tensor powers (`⟨f^⊗n,g^⊗n⟩=⟨f,g⟩ⁿ`); coherent coefficient `(√n!)⁻¹`; `symProj`/`altProj` are `(n!)⁻¹`-**averages** over `Sₙ`.
- Krein: `J†=J`, `J²=1`; `kreinInner x y = ⟨Jx,y⟩`; `posProj=(I+J)/2`; `kreinAdjoint A⁺=J A† J`; Fock `Γ_n(J)=J^⊗n`, `Γ_0=1` (vacuum unsigned).
- Gauge: `n=`matrix dimension; plaquette holonomy `ABC⁻¹D⁻¹`; `plaquetteAction=n−Re tr U_P`; Wilson `S=βΣ_p`, Boltzmann `exp(−S)`; Haar = uniform (probability) measure.

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
- `linalg.py` — dense **complex** linear algebra (no numpy): matmul/dagger/
  trace/kron/partial-trace, complex inverse/det, a real-symmetric **Jacobi**
  eigensolver, and Hermitian functional calculus (`√`, `log`, `exp`, powers,
  `e^{iKt}`, `ρ^{it}`) via the real `[[Re,−Im],[Im,Re]]` embedding — so no
  complex eigensolver is ever needed. `herm_eig` returns the **complex
  eigenvectors** (Gram–Schmidt per degenerate cluster, off the real embedding)
  for the spectral-measure / fidelity / BKM routes. Also singular values /
  Schatten norms, `abs_op`/`herm_sqrt` (CFC `|A|`, `√`), realification of
  (anti)linear maps (the modular `S⋆S` route), and a commutant-dimension
  (null-space) routine. Every primitive is cross-checked in `selftest.py`
  (e.g. functional calculus vs a truncated power series; `herm_eig`
  reconstruction, orthonormality, and degeneracy robustness).
- `harness.py` — `check` / `check_le` with per-check Lean declaration
  citations, summary report, exit code, and the opt-in `NC_MUTATE` corruption
  hook (no effect unless set) that `mutation_test.py` drives.
- `mutation_test.py` — the automated liveness prover: corrupts each check in
  turn and confirms the suite fails, certifying no check is vacuous.

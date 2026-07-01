# KMS / Tomita–Takesaki — Formalization Roadmap

A map of what remains to make the `Spectra.KMS` development complete, with a verified
inventory of which Mathlib tools help and which are missing. All Mathlib references below
were checked against the local source tree (`leanprover/lean4:v4.31.0-rc1`,
`.lake/packages/mathlib/Mathlib/...`) — declaration names and module paths are real unless
explicitly flagged "MISSING".

> How to read: items are grouped into tiers by tractability. Each carries a **difficulty**
> (`easy` ≈ hours, `medium` ≈ a day, `hard` ≈ multi-day, `research` ≈ needs genuinely new
> theory), the **Mathlib support** that exists, what is **missing**, and a **strategy**.

---

## 0. Current status (done, green)

- **Soundness fix — `Dynamics.evolve` is ℂ-linear** (`Condition.lean`). `evolve` was typed
  `ℝ → A →ₗ⋆[ℂ] A` (**conjugate**-linear). Combined with `evolve_zero` (`α_0 = id`) this is
  *inconsistent*: it forces `c • a = conj c • a`, so `Dynamics A` was **uninhabited for every
  nontrivial `A`** — every KMS theorem rested on an unsatisfiable hypothesis (vacuously true).
  Fixed to `ℝ → A →ₗ[ℂ] A` (a `*`-automorphism *is* ℂ-linear). No proof relied on the
  conjugate-linearity (`map_smul` of `evolve` was never used). **Non-vacuity is now witnessed**:
  `Dynamics.trivial` (identity evolution) is a genuine `Dynamics A`, giving `Nonempty (Dynamics A)`.
- **Two-point function is bilinear** — `KMSFunction.{add,smul,addLeft,smulLeft}` +
  `KMSFunction.eqOn_{add,smul}_{right,left}` (W2). **Conjugation symmetry** —
  `KMSFunction.{starReflect,eqOn_starReflect}` (W3).
- **Analytic elements (A1)** — `Spectra/KMS/AnalyticElements.lean`: `α_t` isometric (proved),
  `IsAnalyticElement` + `σ_z` (proof-carrying) + identity-theorem uniqueness, `*`-subalgebra
  closure, real-shift cocycle, and **Bratteli–Robinson density** (`analyticElements_dense`).
- **Imaginary-time KMS (A2)** — `Spectra/KMS/ImaginaryTime.lean`: `IsKMSState.imaginaryTime`,
  `ω(a·σ_{iβ} b) = ω(b·a)` for analytic `b`, via the new one-boundary strip uniqueness
  (`eqOn_closedStrip_of_lower_boundary_eq`, `PeriodicStrip/Basic.lean`).
- **Complex flow group law** — `AnalyticElements.lean`: `Dynamics.isAnalyticElement_sigma` (closure
  under `σ_w`, complex `w`) and `Dynamics.sigma_sigma` (`σ_z ∘ σ_w = σ_{z+w}`).
- **Infinitesimal generator (C*-algebraic, G2 core)** — `Spectra/KMS/Generator.lean`:
  `Dynamics.generator` (`δ(a) = σ_z(a)′|_0`) proved a `ℂ`-linear `*`-derivation
  (`generator_{add,smul,mul,star}`) + the vacuum `IsInvariant.generator_apply` (`ω(δ a)=0`) +
  `Dynamics.generator_one` (`δ(1)=0`, the orbit of `1` is constant; needs the new
  `Dynamics.analyticElements_one`).
- **G2 reality half (ground-state spectral form is real)** — `Generator.lean`:
  `IsInvariant.generator_leibniz_apply` (integration by parts `ω(δa·b)+ω(a·δb)=0`),
  `IsInvariant.re_star_mul_generator_eq_zero` (`Re ω(a⋆·δ a)=0`, i.e. `ω(a⋆·δ a)` purely
  imaginary), and `IsInvariant.im_neg_I_mul_star_mul_generator_eq_zero` (`-i·ω(a⋆·δ a)` is **real**).
  This is the *reality half* of the ground-state spectrum condition `-i·ω(a⋆·δ a) ≥ 0` (BR 5.3.19);
  the nonnegative *sign* stays gated on the GNS Hamiltonian. Holds for any invariant state.
- **Extremal KMS states (C-tier)** — `Spectra/KMS/ExtremalKMS.lean`: `kmsStateSet` (imaginary-time,
  weak-*-closed/convex/compact) + `extremalKMSStateSet_nonempty` (Krein–Milman).
- **KMS equivalence (A3)** — `Spectra/KMS/Equivalence.lean`: `isKMSState_iff_imaginaryTime`
  (`IsKMSState ↔ IsImaginaryTimeKMS`), via `kmsFunctionOfAnalytic` (analytic `b`) and
  `limitKMSFunction` (general `b`, isometry-controlled uniform-Cauchy limit — no Montel). The
  one-boundary uniqueness `eqOn_closedStrip_of_lower_boundary_eq` and the new
  `sigmaCorr_{differentiable,bddAbove_closedStrip}` lemmas support it.
- **GNS unitary group + Stone bridge (G-GNS)** — `Spectra/KMS/UnitaryGroup.lean`: from an
  `α`-invariant state (in particular any KMS state, via `IsKMSState.isInvariant`), the canonical
  GNS implementation `invariantUnitaryGroup ω α hinv : OneParameterUnitaryGroup H_ω` (`U_ω(t) π(a)Ω
  = π(α_t a)Ω`), and `IsKMSState.unitaryGroup`. The bridge from the C\*-algebraic KMS world to the
  Hilbert-space Stone/Yosida world: `invariantUnitaryGroup_generator_isSelfAdjoint` (the Liouvillian
  is self-adjoint) and `invariantUnitaryGroup_stoneEquivSpectral` (it is the operator assigned by
  the Cayley/spectral `stoneEquivSpectral`). Built on Mathlib's `PositiveLinearMap.GNS`.
- **Cyclic vector, vacuum annihilation, GNS reconstruction** — `UnitaryGroup.lean`:
  `State.cyclicVector` (`Ω = π(1)Ω`), `cyclicVector_norm` (`‖Ω‖ = 1`),
  `inner_cyclicVector_gnsStarAlgHom` (**GNS reconstruction** `⟪Ω, π(a)Ω⟫ = ω(a)`, certifying `Ω`
  represents `ω`), `evolveU_cyclicVector` (`U_ω(t) Ω = Ω`), and `generator_apply_cyclicVector`
  (**`L Ω = 0`** — the Liouvillian annihilates the equilibrium vector).
- **Modular (Tomita–Takesaki) specialization** — `UnitaryGroup.lean`:
  `ModularTheoryData.modularUnitaryGroup` (the GNS implementation of the modular flow, i.e. `Δ^{it}`
  — Δ/J themselves stay axiomatized in `ModularTheoryData`), with `modularUnitaryGroup_apply_cyclicVector`
  (`Δ^{it} Ω = Ω`), `modularHamiltonian_isSelfAdjoint` (`K = -log Δ` self-adjoint),
  `modularHamiltonian_apply_cyclicVector` (`K Ω = 0`), and `modularUnitaryGroup_stoneEquivSpectral`.
- **Strip machinery** — `PeriodicStrip/{Defs,IndexProps,ExtensionProps}`: open/closed strip,
  fundamental-domain index, continuity + off-boundary holomorphy of the periodic extension.
- **Periodic extension is entire** — `periodicExtension_entire` (`PeriodicStrip/Basic.lean`),
  via the local Painlevé line-removal in `PeriodicStrip/{Painleve,LineRemove}.lean`.
- **KMS ⇒ invariant**, *unconditionally* — `IsKMSState.isInvariant` (`Condition.lean`).
- **Commutative cylinder theorem** — `commutative_kms_correlations_constant` / `_is_invariant`.
- **Temperature rescaling** — `KMSFunction.rescale`/`rescaleGeneral`, `IsKMSState.rescale`, plus
  the reparametrization group laws `Dynamics.rescale_one`, `Dynamics.rescale_rescale`.
- **KMS function uniqueness** — `KMSFunction.unique` (`Condition.lean`), via the strip max
  principle `eqOn_closedStrip_of_boundary_eq` / `eqZero_of_strip_boundary_zero`
  (`PeriodicStrip/Basic.lean`), which uses `Spectra.ThreeLines.hadamard_three_lines_horizontal`.
- **Convexity** — `State.mix`, `State.mix_apply`, `IsKMSState.mix` (constructive: a mixture of
  KMS states is KMS).
- **Modular bridge (axiomatized bundle)** — `ModularTheoryData`, `modular_state_is_kms`,
  `ConnesCocycle`, `modular_state_is_kms_at_beta` (`Modular.lean`).
- **Von Neumann via Mathlib (W5)** — the abstract VNA assumption is now `[WStarAlgebra A]`
  (Sakai predual), replacing the old `has_predual : True` placeholder, throughout `Modular.lean`
  and `KMSCorr.lean`.
- **Three-lines correlation bound (W4)** — `KMSFunction.norm_le_threeLines` (`Condition.lean`).
- **Genuine state positivity (W0)** — `State.nonneg` strengthened to `0 ≤ ω(a⋆a)` in ℂ's order.
- **Hermiticity & GNS-form symmetry (W1/W2)** — `State.star_apply`, `State.inner_conj`.
- **Correlation conjugation (W3)** — `kms_correlation_conj` (`Condition.lean`).
- **Ground states invariant (G0/G1)** — `IsGroundState` now bounded; `IsGroundState.isInvariant`
  via the half-plane gluing `const_of_glue` (`GroundState.lean`).
- **State space topology + compactness (C1)** — `stateSet` convex + weak-*-closed + **weak-*-compact**
  (Banach–Alaoglu), via the positive-functional norm bound `‖φ a‖ ≤ 2‖a‖`; `State.toWeakDual`
  embedding (`StateTopology.lean`). Pure states (C2) are one Krein–Milman call away (instance gap).

**Placeholders in `Modular.lean`:** ~~`IsVonNeumannAlgebra.has_predual : True`~~ (→ `WStarAlgebra`,
**W5**) and ~~`State.IsNormal := True`~~ — **both DISCHARGED.** `State.IsNormal` is now an honest,
predual-free **order-continuity** predicate (2026-06-30): `ω` preserves suprema of bounded increasing
nets of positives, using the spectral order `[PartialOrder A] [StarOrderedRing A]` threaded through the
`FaithfulNormalState`/`ModularTheoryData` layer. `FaithfulNormalState` is now a genuine restriction (not
"faithful state"). *Remaining as future work (not a placeholder):* proving concrete states — e.g. vector
states — satisfy it. §4 V1 below is superseded by this change.

---

## Mathlib inventory (quick reference)

| Need | Mathlib status | Where |
|---|---|---|
| Phragmén–Lindelöf, **horizontal strip** | ✅ `PhragmenLindelof.horizontal_strip`, `.eqOn_horizontal_strip`, `.eq_zero_on_horizontal_strip` | `Analysis/Complex/PhragmenLindelof.lean` |
| Phragmén–Lindelöf, **half-plane** | ✅ `.right_half_plane_of_bounded_on_real`, `.right_half_plane_of_tendsto_zero_on_real`, `.eq_zero_on_right_half_plane_of_superexponential_decay` | `Analysis/Complex/PhragmenLindelof.lean` |
| Hadamard three-lines | ✅ `Complex.HadamardThreeLines.*` (already wrapped in `PeriodicStrip/Hadamard.lean`) | `Analysis/Complex/Hadamard.lean` |
| Maximum modulus | ✅ `Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn` etc. | `Analysis/Complex/AbsMax.lean` |
| Liouville | ✅ `Differentiable.apply_eq_apply_of_bounded` (already used), `…exists_eq_const_of_bounded`, `…eq_const_of_tendsto_cocompact` | `Analysis/Complex/Liouville.lean` |
| Half-plane closure/frontier bridges | ✅ `Complex.closure_setOf_lt_im`, `Complex.frontier_setOf_lt_im` | `Analysis/Complex/ReImTopology.lean` |
| Identity theorem / analytic continuation | ✅ `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `…eqOn_zero_of_preconnected_of_eventuallyEq_zero` | `Analysis/Analytic/Uniqueness.lean`, `…/IsolatedZeros.lean` |
| Schwarz reflection | ✅ `Analysis/Complex/Schwarz.lean` | — |
| `DiffContOnCl` (holo on open + cont on closure) | ✅ (PL is stated in these terms; project uses split `DifferentiableOn`+`ContinuousOn`) | `Analysis/Calculus/DiffContOnCl.lean` |
| Vector-valued holomorphy (Banach codomain) | ✅ `Analysis/Calculus/FDeriv/Analytic.lean`, `DifferentiableOn` into Banach | — |
| Continuous functional calculus (`cfc`) | ✅ extensive | `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/*` |
| Positive linear maps `A →ₚ[ℂ] B` | ✅ `PositiveLinearMap`: `exists_norm_apply_le` (positive ⇒ bounded), `map_isSelfAdjoint`, `apply_le_of_isSelfAdjoint` | `Analysis/CStarAlgebra/PositiveLinearMap.lean` |
| GNS construction | ✅ `PreGNS`, `gnsNonUnitalStarAlgHom`, cyclic vector (states as `A →ₚ[ℂ] ℂ`) | `Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` |
| Completely positive maps | ✅ | `Analysis/CStarAlgebra/CompletelyPositiveMap.lean` |
| Extreme points / Krein–Milman | ✅ `IsCompact.extremePoints_nonempty`, `closure_convexHull_extremePoints`; `Set.extremePoints`, `IsExtreme` | `Analysis/Convex/KreinMilman.lean`, `…/Extreme.lean`, `…/Exposed.lean` |
| Weak-\* topology / Banach–Alaoglu | ✅ `WeakDual`, Alaoglu | `Analysis/Normed/Module/WeakDual.lean` |
| von Neumann algebra (concrete) | ✅ `VonNeumannAlgebra H` = `StarSubalgebra ℂ (H →L[ℂ] H)` with bicommutant `centralizer_centralizer'` | `Analysis/VonNeumannAlgebra/Basic.lean` |
| Abstract W\*-algebra (Sakai predual) | ✅ `WStarAlgebra M` — `class … [CStarAlgebra M] : Prop` with `exists_predual`; instance `WStarAlgebra (H →L[ℂ] H)` | `Analysis/VonNeumannAlgebra/Basic.lean` |
| **Normal** state (σ-weak continuous) | ❌ MISSING — predual is asserted ∃-style only; no chosen σ-weak topology to define normality against | — |
| Abstract `State` on a C\*-algebra (bundled) | ❌ MISSING (Mathlib uses `→ₚ[ℂ] ℂ` + separate normalization) | — |
| One-parameter automorphism group / Stone (abstract, strongly continuous) | ❌ MISSING (project has its own Cayley/Stone) | — |
| Choquet simplex / barycentric (integral) decomposition | ❌ MISSING (only `StdSimplex`, the finite simplex) | `Analysis/Convex/StdSimplex.lean` |
| Tomita–Takesaki (Δ, J, modular flow) | ❌ MISSING | — |
| KMS condition itself | ❌ MISSING (this project is the source) | — |

---

## Tier 0 — Structural wins (easy–medium, little/no new Mathlib)

These need only the existing `State`/`KMSFunction`/`Hadamard` infrastructure.

### W0. Strengthen `State.nonneg` (soundness fix)  ·  ✅ **DONE**
- **Was:** `State.nonneg` only asserted `0 ≤ (toFun (star a * a)).re`, *not* that the value is
  real, so `State A` admitted non-states (counterexample on `A = ℂ²`:
  `ω(z₁,z₂) = (½+i)·z₁ + (½−i)·z₂`). **Now:** `nonneg : ∀ a, 0 ≤ toFun (star a * a)` in ℂ's
  order (`open scoped ComplexOrder`; `0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im` via `Complex.nonneg_iff`).
  `State.mix`'s `nonneg` was updated to prove both halves. Genuine positivity now holds.

### W1. States are hermitian: `ω (star a) = star (ω a)`  ·  ✅ **DONE**
- `State.star_apply` (`Condition.lean`). The special case `b = 1` of `State.inner_conj` (W2).

### W2. Conjugate symmetry of the GNS form  ·  ✅ **DONE**
- `State.inner_conj` (`Condition.lean`): `ω (star b * c) = star (ω (star c * b))`, by the
  polarization identity (`x = b + c` and `x = b + I•c`) using W0's genuine positivity. This is
  the sesquilinear-form content of W2; full additivity-via-uniqueness combinators were not needed.

### W3. Conjugation symmetry of two-point correlations  ·  ✅ **DONE**
- `kms_correlation_conj` (`Condition.lean`): `ω (a · α_t b) = star (ω (α_t (star b) · star a))`,
  from W1 (hermiticity) and `Dynamics.map_star`. Holds for any state/dynamics.

### W2. Two-point function is bilinear in `(a, b)`  ·  ✅ **DONE**
- **Correction to the original sketch:** the two-point function `F_{a,b}` (lower boundary
  `ω(a · α_t b)`) is **bilinear** — ℂ-linear in *both* `a` and `b` — once `evolve` is ℂ-linear
  (see the **Soundness fix** in §0). It is *not* conjugate-linear in `a`: there is no `star` on
  `a` in `ω(a · α_t b)`. (Conjugate-symmetry belongs to the GNS form `ω(star b * c)`, which is a
  different object — `State.inner_conj`.)
- **Done** (`Condition.lean`): combinators `KMSFunction.add`, `KMSFunction.smul` (right slot) and
  `KMSFunction.addLeft`, `KMSFunction.smulLeft` (left slot) build the KMS function for the combined
  pair pointwise; uniqueness corollaries `KMSFunction.eqOn_add_right`/`eqOn_smul_right`/
  `eqOn_add_left`/`eqOn_smul_left` lift bilinearity to *the* canonical continuation on the closed
  strip. Boundary algebra uses `map_add`/`map_smul`/`mul_add`/`smul_mul_assoc`/`mul_smul_comm`.

### W3. Conjugation symmetry `F_{a,b}` ↔ `F_{a⋆,b⋆}`  ·  ✅ **DONE**
- **Done** (`Condition.lean`): `KMSFunction.starReflect` builds, from a KMS function `H` for
  `(star a, star b)`, the conjugate reflection `z ↦ conj (H (conj z + iβ))` and proves it is a KMS
  function for `(a, b)`; `KMSFunction.eqOn_starReflect` then gives, on the closed strip,
  `F_{a,b}(z) = conj (F_{a⋆,b⋆}(conj z + iβ))`. The reflection `z ↦ conj z + iβ` is the strip's
  boundary-swapping antiholomorphic involution; holomorphy via `DifferentiableAt.conj_conj`
  (`Analysis/Calculus/Deriv/Star.lean`, same tool as `GroundState.lean`), boundary identification
  via `kms_correlation_conj` + `State.star_apply` + `Dynamics.map_star`. (Needs the new import
  `Mathlib.Analysis.Calculus.Deriv.Star` and `open ComplexConjugate` in `Condition.lean`.)

### W4. Three-lines bound for KMS correlations  ·  ✅ **DONE**
- **Done:** `KMSFunction.norm_le_threeLines` (`Condition.lean`):
  `‖F z‖ ≤ (sup_t ‖ω(a·α_t b)‖)^((β−Im z)/β) · (sup_t ‖ω(α_t b·a)‖)^(Im z/β)` on the closed strip.
  Instantiates `Spectra.ThreeLines.hadamard_three_lines_horizontal` at a KMS function and
  identifies the two edge `sSup`s with the ranges of the boundary correlations. Covers the
  autocorrelation case (`b = a`, or `a = star a'`). No new Mathlib needed.

### W5. De-placeholder von Neumann: `IsVonNeumannAlgebra` → `WStarAlgebra`  ·  ✅ **DONE**
- **Done:** `IsVonNeumannAlgebra` (whose `has_predual : True` was a placeholder) is deleted; all
  binders in `Modular.lean` and `QuantumMechanics/BornRule/KMSCorr.lean` now use Mathlib's
  `WStarAlgebra A` (Sakai: `class … [CStarAlgebra M] : Prop` with `exists_predual`,
  `Analysis/VonNeumannAlgebra/Basic.lean`). The predual assumption now has real content. The
  migration was a pure binder swap — no instance is ever constructed in-project.
- **Caveat (SUPERSEDED 2026-06-30):** at the time, this fixed only the *predual* placeholder and
  `State.IsNormal := True` stayed. That is **no longer true** — `IsNormal` was replaced with an honest
  predual-free **order-continuity** predicate (§4 V1 below is superseded); normality does not need a
  chosen σ-weak topology, only the spectral order `[PartialOrder A] [StarOrderedRing A]`.

> Note (refactor, not new work): the existing `eqOn_closedStrip_of_boundary_eq` could be
> *derived from* `PhragmenLindelof.eqOn_horizontal_strip` instead of the bespoke Hadamard
> wrapper — boundedness gives the required growth bound trivially (`c = 0 < π/(b−a)`). Keep the
> Hadamard wrapper if the explicit interpolation *bound* (W4) is wanted; otherwise PL is shorter.

---

## Tier 1 — Ground states (β = ∞)  ·  **medium → hard**

`IsGroundState` (`Condition.lean`) is defined (one-sided analyticity on the upper half-plane)
but has **zero theorems**. Mathlib's half-plane Phragmén–Lindelöf makes the analytic core
reachable — this is the most valuable next *new-analysis* target.

> ⚠️ **Two gotchas, both confirmed against Mathlib:**
> 1. Every half-plane PL theorem carries a **growth hypothesis** (`f =O exp(B·‖z‖^c)`, `c < 2`),
>    *and* a bounded holomorphic function on a half-plane is **not** forced constant by its
>    real-boundary values alone (counterexample `e^{iz}`). The constancy that gives invariance
>    must come from the **spectrum-positivity** content of being a ground state, not from PL alone.
> 2. The current `IsGroundState` is stated with `DifferentiableOn`/`ContinuousOn` on the open/closed
>    UHP and carries **no boundedness**, so *no* PL/Liouville lemma can fire yet.

### G0. Strengthen the `IsGroundState` definition  ·  ✅ **DONE**
- `IsGroundState` (`Condition.lean`) now carries `BddAbove (norm '' (F '' {z | 0 ≤ z.im}))` — the
  boundedness that makes the half-plane an effective domain (β → ∞ limit of strip boundedness).

### G1. Ground states are invariant: `IsGroundState ω α → IsInvariant ω α`  ·  ✅ **DONE**
- `Spectra.KMS.IsGroundState.isInvariant` (`GroundState.lean`).
- **How it actually went** (cleaner than the strategy first sketched): the gluing did **not** need
  half-plane Phragmén–Lindelöf or the `-i·z` rotation. Instead:
  - **Reflection is in Mathlib:** `DifferentiableAt.conj_conj` / `HasDerivAt.conj_conj`
    (`Analysis/Calculus/Deriv/Star.lean`) make `G z := conj (F'(conj z))` holomorphic on the LHP
    directly — no manual Schwarz reflection. `F'` is the UHP extension for the pair `(1, star a)`.
  - **Gluing = the project's own line-removal.** `const_of_glue` (new, in `GroundState.lean`) pastes
    `F` (closed UHP) and `G` (closed LHP), agreeing on `ℝ` by hermiticity (`State.star_apply` +
    `Dynamics.map_star`), into `H := fun z => if 0 ≤ z.im then F z else G z`; continuity via
    `ContinuousOn.if` + `frontier/closure_setOf_*_im` (`ReImTopology.lean`); entirety via
    `differentiableOn_of_continuousOn_of_differentiableOn_off_horizLine` (`LineRemove.lean`) on a
    ball around each real point; then Liouville (`Differentiable.apply_eq_apply_of_bounded`).
  - So the `e^{iz}` subtlety is handled by the **second (reflected) continuation**, exactly as noted.
- **Mathlib half-plane PL was *not* needed** for invariance (it remains the tool for the spectrum
  condition G2). Edge-of-the-wedge is *not* missing in effect — the single-line local Painlevé in
  `LineRemove.lean` already does the across-`ℝ` glue.

### G2. The generator + spectrum / positivity condition  ·  generator ✅ **DONE**; positivity gated
- **C*-algebraic generator** ✅ **DONE** (`Spectra/KMS/Generator.lean`): the infinitesimal generator
  `Dynamics.generator ha = δ(a) = (d/dz) σ_z(a)|_{z=0}` on analytic elements (A1), proved a `ℂ`-linear
  `*`-derivation — `generator_{add,smul,mul,star}` (`δ(ab)=δa·b+a·δb`, `δ(a⋆)=(δa)⋆`) — plus
  `hasDerivAt_analyticExtend` (`σ_z` has complex derivative `δa` at `0`). **Vacuum:**
  `IsInvariant.generator_apply` — an invariant state is annihilated by the generator, `ω(δ a) = 0`
  (the orbit average `z ↦ ω(σ_z a)` is entire and constant on `ℝ`). Done entirely via the *complex*
  derivative at `0` (using `analyticExtend_unique` + `HasDerivAt.{add,const_smul,mul,star_conj}`),
  which sidesteps the `ℝ`-vs-`ℂ` module diamonds a real-parameter formulation hits. Green, axiom-clean.
- **GNS Hilbert-space generator (Liouvillian):** the GNS unitary-group / Stone-bridge development was
  moved out of `KMS/` into a forthcoming **Modular Theory** directory (the in-KMS `UnitaryGroup.lean`
  was removed as too shallow).
- **Reality half** ✅ **DONE** (`Generator.lean`): `-i·ω(a⋆·δ a) ∈ ℝ`, i.e. `Re ω(a⋆·δ a)=0`, for any
  invariant state — `IsInvariant.re_star_mul_generator_eq_zero` /
  `IsInvariant.im_neg_I_mul_star_mul_generator_eq_zero`, via the new integration-by-parts lemma
  `IsInvariant.generator_leibniz_apply` (`ω(δa·b)+ω(a·δb)=0`, from vacuum + Leibniz) plus hermiticity
  and `δ(a⋆)=(δa)⋆`. (No need for the autocorrelation `g(-t)=conj g(t)` route — the algebraic
  integration-by-parts argument is cleaner and avoids the `ℝ`-derivative module diamonds.)
- **Remaining (the nonnegative sign):** `-i·ω(a⋆·δ a) ≥ 0` for ground states. This is the
  operator-theoretic ground-state content, gated on the GNS Hamiltonian (`H ≥ 0`, Modular Theory dir)
  or spectral-measure/Bochner theory. **Blocked** until that exists.

### G3. β → ∞ limit gives a ground state  ·  **research**
- **Missing:** needs normal-families/Vitali compactness for the family of KMS functions
  (Montel/Vitali **not found** in Mathlib) plus a weak-\* limit of states. Defer.

---

## Tier 2 — Topology of the state space & extremal KMS states  ·  **medium → research**

### C1. Give the state space a usable topology  ·  ✅ **DONE** (incl. weak-* compactness)
- **Done** (`StateTopology.lean`): `stateSet A := {φ : WeakDual ℂ A | (∀ a, 0 ≤ φ(a⋆a)) ∧ φ 1 = 1}`,
  with `stateSet_convex`, `stateSet_isClosed`, the embedding `State.toWeakDual`, and **`stateSet_isCompact`**
  (Banach–Alaoglu: `stateSet` is a weak-*-closed subset of the radius-2 ball, compact via
  `WeakDual.isCompact_closedBall` + `IsCompact.of_isClosed_subset`).
- **The norm bound was achieved without Cauchy–Schwarz.** Foundations: `stateSet.map_nonneg`
  (positivity on all `0 ≤ x`, via `StarOrderedRing.nonneg_iff` + `AddSubmonoid.closure_induction`),
  `stateSet.map_mono`, `stateSet.apply_algebraMap`. Then `stateSet.norm_apply_le : ‖φ a‖ ≤ 2‖a‖` via
  the **self-adjoint decomposition** `a = ℜa + i·ℑa`: for self-adjoint `h`, the order squeeze
  `-‖h‖•1 ≤ h ≤ ‖h‖•1` (`IsSelfAdjoint.le_algebraMap_norm_self`) pushed through `φ` gives
  `‖φ h‖ ≤ ‖h‖` *and* hermiticity (`(φ h).im = 0`) **for free** — no polarization needed.
- **Note:** the C*-order on abstract `A` is not a global instance; enable it file-locally via
  `attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing`.

### C2. Pure states exist  ·  ✅ **DONE**
- **Done** (`StateTopology.lean`): `pureStateSet A := (stateSet A).extremePoints ℝ`;
  `pureStateSet_nonempty` (Krein–Milman: nonempty weak-*-compact convex ⇒ extreme point) and
  `pureStateSet_nonempty_of_state` (a concrete state ⇒ a pure state); `pureStateSet_subset_stateSet`.
  Green, `#print axioms`-clean.
- **The instance-diamond fix** (the documented blocker): two missing real-LCTVS instances on the
  complex weak dual are now supplied — `instance : LocallyConvexSpace ℝ (WeakDual ℂ A)` via
  `inferInstanceAs (… (WeakBilin (topDualPairing ℂ A)))` (Mathlib's `WeakBilin.locallyConvexSpace`
  unfolds only on the `WeakBilin` form), and `instance : ContinuousSMul ℝ (WeakDual ℂ A)` built from
  **weak-* evaluation continuity** (`WeakDual.continuous_of_continuous_eval`) rather than
  `inferInstance` — the eval-continuity proof uses the *ambient* `SMul`, so it matches the `Module ℝ`
  Krein–Milman infers (the `inferInstance` route picks a `DistribMulAction`-based `SMul` that
  diamond-mismatches). KEY subtlety: state the conclusion via the `pureStateSet` *def* (or dot-notation
  `stateSet_isCompact.extremePoints_nonempty`), not an explicit `extremePoints ℝ` return annotation,
  which would re-trigger the diamond by fixing a second `Module ℝ`.
- **Extremal KMS states** ✅ **DONE** (`Spectra/KMS/ExtremalKMS.lean`): `kmsStateSet α β` = the KMS
  states in the weak dual via the **imaginary-time** characterization (A3) — the strip condition is
  not manifestly closed, but each imaginary-time equation `φ(a·σ_{iβ}b)=φ(b·a)` is weak-*-closed
  (`isClosed_imaginaryTimeCond`). Hence `kmsStateSet_isClosed`, `_convex` (the equations are affine),
  and `_isCompact` (closed in the compact `stateSet`). `extremalKMSStateSet := kmsStateSet.extremePoints ℝ`;
  `extremalKMSStateSet_nonempty` (Krein–Milman, reusing the C2 real-LCTVS instances) and
  `extremalKMSStateSet_nonempty_of_kmsState` (non-vacuity from any concrete KMS state, via
  `IsKMSState.toWeakDual_mem_kmsStateSet` ← A2). Green, `#print axioms`-clean.

### C3. Extremal KMS = factor states (cluster property)  ·  **research**
- **Missing:** requires von Neumann **factor** decomposition / central decomposition — Mathlib's
  vN algebra is concrete and has no central-decomposition theory. Defer.

### C4. KMS states form a Choquet simplex  ·  **research**
- **Missing:** Choquet integral representation is entirely absent (only `StdSimplex`). Defer.

---

## Tier 3 — Analytic elements & the imaginary-time KMS form  ·  **hard → research**

### A1. Analytic / entire elements of `Dynamics`  ·  ✅ **DONE** (including density)
- **Done** (`Spectra/KMS/AnalyticElements.lean`, all green, `#print axioms`-clean):
  - **Isometry for free** — `Dynamics.evolveStarAlgHom` (bundle `α_t : A →⋆ₐ[ℂ] A`),
    `Dynamics.norm_evolve : ‖α_t a‖ = ‖a‖` (PROVED via `NonUnitalStarAlgHom.norm_map` + injectivity
    from the inverse `α_{-t}`; not a field), `Dynamics.evolveL` (`α_t` as a CLM).
  - **`Dynamics.IsAnalyticElement`** (entire `ℂ → A` extension of the orbit) + non-vacuity
    (`isAnalyticElement_trivial`); **`analyticExtend_unique`** (1-D identity theorem for `ℂ → A`, via
    `analyticOnNhd_univ_iff_differentiable` + `eqOn_of_preconnected_of_frequently_eq`); the
    proof-carrying flow **`Dynamics.sigma`** (`σ_z`) with `sigma_ofReal`/`sigma_zero`.
  - **`*`-subalgebra closure** — `analyticElements_{zero,add,smul,mul,star}`; the real-shift cocycle
    **`Dynamics.ext_add_real`** (`σ_{s+z} = α_s ∘ σ_z`, `s ∈ ℝ`).
  - **DENSITY** — `Dynamics.gaussianSmooth a n := √(n/π) ∫ e^{-n t²} α_t(a) dt`;
    `integrable_gaussian_smul`; **`gaussianSmooth_isAnalyticElement`** (each `aₙ` is entire, by
    differentiation under the integral — `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a
    bespoke Gaussian×linear dominating bound on each ball); **`gaussianSmooth_tendsto`** (`aₙ → a`, by
    rescaling `s = √n·t` then dominated convergence + strong continuity); **`analyticElements_dense`**
    (`Dense (α.analyticElements)`). The Bratteli–Robinson theorem, fully formalized.
- **Note:** the `σ_{z+w} = σ_z ∘ σ_w` *complex* group law (full) is deferred to the A2 chapter (needs
  closure of `analyticElements` under `σ_w` for complex `w`); the real-shift cocycle is landed.

### A2. Imaginary-time KMS: `ω(a · σ_{iβ}(b)) = ω(b · a)` for analytic `b`  ·  ✅ **DONE**
- **Done** (`Spectra/KMS/ImaginaryTime.lean`): `IsKMSState.imaginaryTime` —
  `ω (a * α.sigma hb ((β:ℂ)*I)) = ω (b * a)` for any analytic element `b` (`hb`). Green,
  `#print axioms`-clean.
- **How:** the boundary correlation `t ↦ ω(a·α_t b)` continues to the entire `G z := ω(a·σ_z b)`
  (`σ_z` entire from A1; `ω` bundled as a CLM `⟨ω.toFun, ω.continuous⟩`). `G` is **bounded** on the
  closed strip because `α_t` is isometric (A1 `norm_evolve`) so `‖σ_z b‖ = ‖σ_{i·Im z} b‖` via
  `ext_add_real` + `Complex.re_add_im`, bounded over the compact `Im z ∈ [0,β]`. `G` and the KMS
  function `F` agree on the **lower** boundary (`sigma_ofReal` + `F.lower_boundary`); the new
  **one-boundary strip uniqueness** `eqOn_closedStrip_of_lower_boundary_eq` (below) forces `F = G`
  on the closed strip; evaluate at `iβ = realToUpper β 0` and use `F.upper_boundary 0` +
  `evolve_zero`.
- **New reusable analysis:** `eqZero_of_strip_lower_boundary_zero` /
  `eqOn_closedStrip_of_lower_boundary_eq` (`PeriodicStrip/Basic.lean`) — vanishing on *one* boundary
  line suffices (Hadamard gives `0^{positive}·M = 0` on `{Im < β}`; the upper edge `Im = β` follows
  by a vertical-limit continuity argument, since `0^0 = 1` there). This is the genuinely new lemma;
  it could be upstreamed.
- **Complex flow group law** ✅ **DONE** (`AnalyticElements.lean`): `Dynamics.isAnalyticElement_sigma`
  (analytic elements are closed under `σ_w` for complex `w`; witness `z ↦ σ_{z+w}(a)`) and
  `Dynamics.sigma_sigma` (`σ_z(σ_w a) = σ_{z+w}(a)`), both via `ext_add_real` + `analyticExtend_unique`.

### A3. Equivalence of KMS definitions (strip ⇔ imaginary-time)  ·  ✅ **DONE**
- **Done** (`Spectra/KMS/Equivalence.lean`): `isKMSState_iff_imaginaryTime` —
  `IsKMSState ω α β ↔ IsImaginaryTimeKMS ω α β`, where `IsImaginaryTimeKMS` is
  `∀ a b (hb : IsAnalyticElement b), ω(a·σ_{iβ} b) = ω(b·a)`. Green, `#print axioms`-clean. **The
  Tier-3 capstone.**
- **`⟹`** is A2 (`IsKMSState.imaginaryTime`), packaged over all analytic `b`.
- **`⟸` for analytic `b`** — `kmsFunctionOfAnalytic`: `F_b(z) = ω(a·σ_z b)` is a KMS function; its
  upper boundary is the imaginary-time identity applied to the analytic element `σ_t b` (closure
  under the flow + the group law `sigma_sigma`). Holomorphy/boundedness are the KMS-free
  `sigmaCorr_differentiable`/`sigmaCorr_bddAbove_closedStrip` (extracted from `ImaginaryTime.lean`).
- **`⟸` for general `b`** — `limitKMSFunction`: approximate `b` by analytic `bₙ → b` (A1 density).
  Because `α_t` is **isometric** (A1), the boundary differences `‖ω(a·α_t(bₙ−bₘ))‖ ≤ ‖ωL‖‖a‖‖bₙ−bₘ‖`
  are uniformly small, so Hadamard three-lines on `Fₙ−Fₘ` makes `Fₙ` **uniformly Cauchy** on the
  closed strip (`diff_bound`). The limit is holomorphic by `TendstoLocallyUniformlyOn.differentiableOn`,
  continuous by `TendstoUniformlyOn.continuousOn`, with the boundary values by `tendsto_nhds_unique`.
  **Montel/Vitali is *not* needed** — the isometry replaces it. (This is why the "research"
  classification was too pessimistic.)

---

## Tier 4 — von Neumann algebras & Tomita–Takesaki  ·  **research**

### V1. Replace the `True` placeholders  ·  **predual: ✅ DONE (W5) · normal: ✅ DONE (order-continuity, 2026-06-30)**
- **Finding (corrected):** Mathlib has **both** flavors of von Neumann algebra in
  `Analysis/VonNeumannAlgebra/Basic.lean`:
  - **abstract** `WStarAlgebra M` (Sakai: `[CStarAlgebra M]` + `exists_predual`) — drops straight
    into the project's abstract setting;
  - **concrete** `VonNeumannAlgebra H` (a `StarSubalgebra ℂ (H →L[ℂ] H)` equal to its bicommutant).
    ⚠ **Correction (2026-06-30):** there is **no** `instance WStarAlgebra (H →L[ℂ] H)` — `Basic.lean:64`
    is a future-tense TODO comment, not a declaration; constructing it is part of the predual build.
- **Predual placeholder → real:** do **W5** — swap `IsVonNeumannAlgebra A` for `[WStarAlgebra A]`.
  Easy–medium, pure win.
- **Normal-state placeholder (`State.IsNormal := True`) → real: ✅ DONE (2026-06-30)** via option (c),
  order-continuity: `IsNormal ω := ∀ (s : Set A) (a : A), DirectedOn (·≤·) s → (∀ x∈s, 0≤x) →
  IsLUB s a → IsLUB ((fun x => (ω x).re) '' s) (ω a).re` — ω preserves the suprema of bounded increasing
  nets of positives. **Predual-free** (needs only the spectral order `[PartialOrder A] [StarOrderedRing A]`,
  threaded through `FaithfulNormalState`/`ModularTheoryData`/`ConnesCocycle`; nothing inhabits these so no
  proofs broke). `FaithfulNormalState` is now a genuine restriction, not "faithful state". Also purged the
  vacuous `modular_state_is_kms` ("Takesaki's Theorem" = `hmod.kms_at_one` field access).
- **Remaining (future work, NOT a placeholder):** prove concrete states — e.g. vector states — satisfy it
  (the `Q1 = concrete` corollary that inhabits the predicate). Build + AxiomCheck green (4088).

### V2. Actual Tomita–Takesaki construction (Δ, J, modular flow)  ·  **research**
- **Missing entirely** in Mathlib. The project rightly *axiomatizes* this via
  `ModularTheoryData`. A real construction (GNS ⇒ `S = JΔ^{1/2}` ⇒ `σ_t = Δ^{it} · Δ^{-it}`)
  needs unbounded operators, polar decomposition of closed operators, and self-adjoint
  functional calculus on Hilbert space — a major project of its own. Keep axiomatized.

---

## Recommended order

0. ✅ **ALL of Tier 3, plus C1/C2, are done.** The soundness fix (Dynamics ℂ-linearity), all of
   **Tier 0 (W0–W5)** — incl. **bilinearity (W2)** and **conjugation-symmetry (W3)** — **G0/G1**
   (ground-state invariance), **C1** (state space topology + compactness), **C2** (**pure states
   exist** via Krein–Milman, with the real-LCTVS instances on `WeakDual ℂ A` supplied), **A1**
   (analytic elements, σ_z, `*`-subalgebra closure, **Gaussian-smoothing density**), **A2**
   (**imaginary-time KMS**), the **complex flow group law** `σ_z ∘ σ_w = σ_{z+w}`, and **A3**
   (**strip ⇔ imaginary-time equivalence**, `isKMSState_iff_imaginaryTime`) are **done**.
1. ✅ **Extremal KMS states** (`ExtremalKMS.lean`) and the ✅ **C*-algebraic generator** δ
   (`Generator.lean`: `*`-derivation + vacuum `ω(δa)=0`) are **done**.
2. ✅ **Ground-state positivity — reality half DONE** (`(ω(a⋆·δ a)).re = 0`,
   `IsInvariant.re_star_mul_generator_eq_zero`). The nonnegative *sign* `-i·ω(a⋆·δ a) ≥ 0` is now the
   only G2 remainder and is **blocked** on the GNS Hamiltonian (Modular Theory dir) or spectral-measure
   theory. Also blocked there: the GNS Liouvillian itself, slated for the new **Modular Theory** directory.
3. Everything in `research` (G3, C3/C4, V2) — defer until Mathlib gains Choquet theory /
   central decomposition / Tomita–Takesaki, or scope as standalone subprojects.

## Gaps worth upstreaming to Mathlib
- **Real-LCTVS instances on a complex weak dual** (`ContinuousSMul ℝ` / `LocallyConvexSpace ℝ` on
  `WeakDual ℂ A`) — supplied locally in `StateTopology.lean`; the `ContinuousSMul ℝ`-via-eval-continuity
  construction sidesteps the `DistribMulAction`-vs-`Module` `SMul` diamond and is upstreamable.
- Edge-of-the-wedge / "remove a line" glue across `ℝ` (the project's `LineRemove.lean` is most
  of the way there for one horizontal line).
- Abstract one-parameter strongly-continuous automorphism groups + Stone (the project's
  `CayleyTransform`/`Stone` could seed this).
- Montel/Vitali normal families (needed for β → ∞ limits).

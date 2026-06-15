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

**Placeholders in `Modular.lean`:** `IsVonNeumannAlgebra.has_predual : True` and
`State.IsNormal := True`. The predual one is now *replaceable* with Mathlib's `WStarAlgebra`
(see **W5**); `State.IsNormal` genuinely stays a placeholder for now (see §4 V1). Don't naively
delete `IsNormal` — downstream signatures depend on it.

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
- **Caveat (still true):** this fixed only the *predual* placeholder. `State.IsNormal := True`
  stays a placeholder (see §4 V1): `exists_predual` is existential, so there is no *chosen*
  predual / σ-weak topology to define normality against.

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

### G2. Spectrum / positivity condition  ·  **hard / research**
- **Statement:** ground state ⇔ the GNS generator (Hamiltonian) is positive.
- **Missing:** requires the GNS generator of `Dynamics` and Stone's theorem at the abstract
  level (MISSING). Realistically gated on Tier 3 / a GNS-for-dynamics development.

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

### C2. Pure / extremal states exist  ·  ✅ **one lemma call away** (blocked by a Mathlib instance gap)
- The Krein–Milman corollary `IsCompact.extremePoints_nonempty stateSet_isCompact hne :
  (Set.extremePoints ℝ (stateSet A)).Nonempty` is mathematically immediate from `stateSet_isCompact`,
  but does **not elaborate**: it needs `[ContinuousSMul ℝ (WeakDual ℂ A)]` and
  `[LocallyConvexSpace ℝ (WeakDual ℂ A)]` — the **real** LCTVS structure on a **complex** weak dual,
  which Mathlib doesn't register, and the real-module instance it would use does not defeq-match the
  one Krein–Milman infers (an instance-diamond, not a math gap). Documented in `StateTopology.lean`.
- **Next:** supply a coherent real-LCTVS instance on `WeakDual ℂ A` (or upstream it); then pure-state
  existence is a one-liner. Also: show the KMS-state subset is weak-*-closed (preserved under limits)
  to specialize to *extremal KMS* states.

### C3. Extremal KMS = factor states (cluster property)  ·  **research**
- **Missing:** requires von Neumann **factor** decomposition / central decomposition — Mathlib's
  vN algebra is concrete and has no central-decomposition theory. Defer.

### C4. KMS states form a Choquet simplex  ·  **research**
- **Missing:** Choquet integral representation is entirely absent (only `StdSimplex`). Defer.

---

## Tier 3 — Analytic elements & the imaginary-time KMS form  ·  **hard → research**

### A1. Analytic / entire elements of `Dynamics`  ·  **hard**
- **Goal:** the set of `a` for which `t ↦ σ_t(a)` extends to an (entire) `ℂ`-analytic
  `A`-valued map, plus `σ_z` on them, plus **density** of analytic elements.
- **Mathlib support:** vector-valued holomorphy is available (`DifferentiableOn` into a Banach
  space, `Analysis/Calculus/FDeriv/Analytic.lean`); the Bochner integral
  (`MeasureTheory.integral`) supports Gaussian smoothing `a_n := √(n/π) ∫ e^{-n t²} σ_t(a) dt`
  to produce a dense set of analytic elements.
- **Missing:** there is **no** abstract one-parameter-group / Stone framework to inherit from;
  `σ_z` and analyticity must be built directly on the bespoke `Dynamics`. cfc
  (`ContinuousFunctionalCalculus/*`) helps only in a concrete (Δ^{iz}) realization, not abstractly.

### A2. Imaginary-time KMS: `ω(a · σ_{iβ}(b)) = ω(b · a)` for analytic `b`  ·  **hard**
- **Depends on:** A1 + identification of the strip boundary value at `iβ` with `σ_{iβ}`. Uses
  `KMSFunction.unique` to pin the continuation. The identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) helps equate continuations.

### A3. Equivalence of KMS definitions (strip ⇔ imaginary-time)  ·  **research**
- Capstone of Tier 3; needs A1+A2 in both directions.

---

## Tier 4 — von Neumann algebras & Tomita–Takesaki  ·  **research**

### V1. Replace the `True` placeholders  ·  **predual: easy–medium · normal: hard**
- **Finding (corrected):** Mathlib has **both** flavors of von Neumann algebra in
  `Analysis/VonNeumannAlgebra/Basic.lean`:
  - **abstract** `WStarAlgebra M` (Sakai: `[CStarAlgebra M]` + `exists_predual`) — drops straight
    into the project's abstract setting;
  - **concrete** `VonNeumannAlgebra H` (a `StarSubalgebra ℂ (H →L[ℂ] H)` equal to its bicommutant),
    with `instance WStarAlgebra (H →L[ℂ] H)`.
- **Predual placeholder → real:** do **W5** — swap `IsVonNeumannAlgebra A` for `[WStarAlgebra A]`.
  Easy–medium, pure win.
- **Normal-state placeholder (`State.IsNormal := True`) → real:** still hard. `exists_predual` only
  *asserts* a predual; Mathlib has no chosen σ-weak/ultraweak topology on a general `WStarAlgebra`,
  so "normal = σ-weakly continuous / order-continuous / predual-represented" can't be stated
  off-the-shelf. Realistic paths: (a) keep `IsNormal` a placeholder; (b) define normality only
  after a chosen predual is fixed (needs new dev); (c) use order-continuity (monotone-net
  continuity) as the definition — more tractable but still new work.
- **Recommendation:** land **W5** now (predual becomes real); keep `IsNormal` placeholder, revisit
  alongside the state topology (Tier 2, C1) or an order-continuity definition.

### V2. Actual Tomita–Takesaki construction (Δ, J, modular flow)  ·  **research**
- **Missing entirely** in Mathlib. The project rightly *axiomatizes* this via
  `ModularTheoryData`. A real construction (GNS ⇒ `S = JΔ^{1/2}` ⇒ `σ_t = Δ^{it} · Δ^{-it}`)
  needs unbounded operators, polar decomposition of closed operators, and self-adjoint
  functional calculus on Hilbert space — a major project of its own. Keep axiomatized.

---

## Recommended order

0. ✅ **The soundness fix (Dynamics ℂ-linearity)**, all of **Tier 0 (W0–W5)** — including the
   **bilinearity (W2)** and **conjugation-symmetry (W3)** of the two-point function — and **G0/G1**
   (ground-state invariance) and **C1** (state space topology + compactness) are **done**.
1. **C2 pure states** — supply a real-LCTVS instance on `WeakDual ℂ A` (`ContinuousSMul ℝ` +
   `LocallyConvexSpace ℝ`, matching the inferred `Module ℝ`); then Krein–Milman gives pure states
   in one line. (C1 incl. compactness is done.)
2. **G2** (ground-state spectrum condition) — still needs the GNS generator (hard).
3. **C1 → C2** (state-space topology → extremal states) — unlocks Krein–Milman; the embedding
   `State A ↪ WeakDual ℂ A` is the gating subtask.
4. **A1** (analytic elements) — needed before any imaginary-time results; large but well-scoped.
5. Everything in `research` (G2/G3, C3/C4, A3, V2) — defer until Mathlib gains Choquet theory /
   central decomposition / Tomita–Takesaki, or scope as standalone subprojects.

## Gaps worth upstreaming to Mathlib
- Edge-of-the-wedge / "remove a line" glue across `ℝ` (the project's `LineRemove.lean` is most
  of the way there for one horizontal line).
- Abstract one-parameter strongly-continuous automorphism groups + Stone (the project's
  `CayleyTransform`/`Stone` could seed this).
- Montel/Vitali normal families (needed for β → ∞ limits).

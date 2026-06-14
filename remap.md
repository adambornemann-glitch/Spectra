# Spectra — Reorganization Map (`remap.md`)

Working document tracking proposed file/directory renames and structural changes.
Renames are applied in dedicated passes, **separate from docstring work**, because every
rename rewrites `import` lines across the subtree and the root `Spectra.lean`.

**Conventions:** see [STYLE.md](STYLE.md) §3. In short — directory = mathematical *area*;
file = the *object or theorem* it develops; letters-only `UpperCamelCase`; no
`Helpers`/`Lemmas`/`Utils`/`Misc`; drop the prefix the directory already supplies; spell
out abbreviations; avoid "-Like" nicknames; files are nouns, not verbs.

**Status legend:** `proposed` (recommendation) · `open` (needs a decision) ·
`accepted` (agreed, not yet applied) · `done`

> Nothing here is applied until marked `accepted`. Each batch is verified with `lake build`.

---

## 0. Whole-library verdict

232 `.lean` files, 15 top-level areas, **5 naming smells total**. The library is
well-organized; no big-bang restructure is warranted. Work needed is moderate polish:
the trivial renames in §1, and decisions on the three structural questions in §2 — which
should be settled **before** finalizing any single area's internal breakdown (including
InformationGeometry).

Top-level areas (file counts): QuantumMechanics 54 · Mathlib 46 (upstream staging) ·
Bochner 29 · InformationGeometry 25 · Resolvent 24 · SobolevSpaces 11 · SpectralTheory 9 ·
CayleyTransform 8 · Herglotz 7 · Kernel 6 · Operator 5 · Fourier 3 · PositiveDefinite 2 ·
ProjValMeasure 2 · SphericalHarmonics 1.

---

## 1. Trivial naming fixes (library-wide, uncontroversial)

These violate STYLE.md mechanically. Each is a pure rename (+ update of importers).

| Current | Proposed | Why | Status |
|---|---|---|---|
| `InformationGeometry/StoneLike/mConnect.lean` | `MixtureConnection.lean` | leading-lowercase + abbreviation | proposed |
| `QuantumMechanics/BellsTheorem/CHSH_Bounds/` | `CHSHBounds/` | underscore (CHSH acronym kept) | proposed |
| `…/CHSH_Bounds/CHSH_Basic.lean` | `…/CHSHBounds/Basic.lean` | underscore; dir supplies "CHSH" | proposed |
| `…/CHSH_Bounds/Op_square.lean` | `…/CHSHBounds/OperatorSquare.lean` | underscore + lowercase word | proposed |
| `…/QuantumCHSH/Q_CHSH_Basic.lean` | `…/QuantumCHSH/Basic.lean` | underscore; dir supplies "Quantum CHSH" | proposed |
| `QuantumMechanics/Unitarity/FirstLawEqiv.lean` | `FirstLawEquiv.lean` | likely typo ("Eqiv") — **confirm** | open |

---

## 2. Structural questions (decide before per-area breakdowns)

### 2a. Thin top-level areas (1–3 files)
`SphericalHarmonics` (1), `Fourier` (3), `PositiveDefinite` (2), `ProjValMeasure` (2) read
as peer areas but are really sub-topics. Options per area: **grow** it, or **nest** it under
a related parent (e.g. `ProjValMeasure`, `PositiveDefinite` → under `SpectralTheory`;
`SphericalHarmonics` → under a harmonic-analysis parent). — `open`

### 2b. The spectral / operator cluster
`Operator`, `Resolvent`, `SpectralTheory`, `ProjValMeasure`, `CayleyTransform`,
`PositiveDefinite` are all facets of "spectral theory of (unbounded) self-adjoint
operators," yet sit flat, and `SpectralTheory` is simultaneously a peer **and** the natural
umbrella name. Decision: **(a)** keep flat, Mathlib-style (each a legitimate area); or
**(b)** introduce a parent (e.g. `OperatorTheory/` or promote `SpectralTheory/` to hold the
others). — `open`

### 2c. Naming philosophy to ratify once, apply everywhere
- **Abbreviations:** spell out (`mConnect`→`MixtureConnection`)? Keep standard physics
  acronyms (`CHSH`, `GNS`, `RLD`, `PVM`)? — `open`
- **"-Like" nicknames:** rename to the object (`StoneLike`→`Flow`, `SchrodingerLike`→…)? — `open`
- **Optional `Defs.lean` split:** adopt the Mathlib pattern of separating bare definitions
  (light imports) from `Basic.lean`, as already done in `Resolvent/`? — `open`

---

## 3. InformationGeometry — APPLIED 2026-06-13 (builds green)

All moves/renames below were performed; `FaaDiBruno/{Basic,Helpers}` merged into a single
`Flow/FaaDiBruno.lean`; imports + `Spectra.lean` rewritten; `lake build` green (3959 jobs). The
move dissolved `Dynamics/` (it mixed static geometry with a foundational regularity file) and
renamed the `StoneLike/` flow theory to `Flow/`. Done as plain `mv` (not `git mv`), so `git`
shows deletes+adds — run `git add -A` to let rename-detection pair them.

### Proposed tree
```
InformationGeometry/
  StatisticalModel.lean        (was Fisher/StatisticalModel)   ── foundations to root
  Score.lean                   (was Fisher/Score)
  Regularity.lean              (was Dynamics/Models)           ── Twice/ThriceDifferentiableModel
  StatisticalManifold.lean     (was Fisher/StatisticalManifold)
  Divergence.lean              (was Dynamics/Hessian)          ── klDiv + the ∂²D=g theorem
  Fisher/
    Metric.lean                (was Fisher/FisherMetric)       ── prefix dropped
    Information.lean           (was Fisher/FisherInformation)
  Connection/                  (was Dynamics/, minus the above)
    Basic.lean                 (was AlphaConnect)              ── α-connections
    AmariChentsov.lean         (was CubicTensor)               ── eponym; keep `cubicTensor` def
    Bartlett.lean              (was BartlettIdentities)
  GeometricData.lean           (keep, or → Structure.lean)     ── open
  CramerRao/
    Basic.lean                 (unchanged)
    CauchySchwarz.lean         (unchanged)
    Covariance.lean            (was Cross — score↔estimator covariance identity + Leibniz)
    Bound.lean                 (unchanged)
    Quantum.lean               (was SchrodingerRLD)
  Flow/                        (was StoneLike/)
    Basic.lean                 (unchanged path within area)
    Family.lean                (unchanged)
    Generator.lean             (unchanged)
    Schrodinger.lean           (was SchrodingerLike — IG Schrödinger/Ehrenfest eqns for flows)
    FaaDiBruno.lean            (merge FaaDiBruno/Basic + Helpers)
    MixtureConnection.lean     (was mConnect)
    CubicInvariance.lean       (was PreservesCubic)
  Dichotomy.lean               (stays at root — classical↔quantum capstone over GeometricData)
```

### Duplication audit (RESOLVED 2026-06-13)
1. **KL divergence — REAL duplication, consolidate.** `StatisticalManifold.klDivergence`
   (StatisticalManifold.lean:322) and `TwiceDifferentiableModel.klDiv` (Hessian.lean:48)
   have the *identical* integrand `∫ p(θ₁)·log(p(θ₁)/p(θ₂)) dμ`; only the carrier differs
   (manifold vs model). The author's own comment calls `klDiv` a "redefine … at the model
   level." **Action:** define KL once on the underlying `RegularStatisticalModel` (which both
   already project to — so `M.klDiv` keeps resolving via `extends`), keep canonical name
   **`klDiv`** (workhorse: 8 files vs `klDivergence`'s single file; also the short form Mathlib
   uses), retire `klDivergence` (→ `@[deprecated] alias` or delete). Surface it from
   `Divergence.lean` in the new tree.
2. **`InfoGeometricGenerator` — NOT duplication, keep both.** `InfoGeometricGenerator M`
   (StoneLike/Basic.lean:79, concrete, model-tied) and `GeometricData.Generator Γ`
   (GeometricData.lean:97, abstract, over a bare `(domain, g, C)` triple) are *deliberately*
   parallel, joined by `InfoGeometricGenerator.equivAbstract` (a `rfl`-on-both-sides ≃). The
   abstraction exists so the quantum pure-state case (no classical model) can share one
   definition — see `Dichotomy.lean`. **No merge, no rename**: the shared core name
   "Generator" is the point, and the lowercase analytic `generator` (Generator.lean, the
   d/dt of a flow) is a distinct, correctly-named object. Leave as-is.

### Non-blockers (RESOLVED 2026-06-13)
- **`SchrodingerLike.lean`** is NOT a stub — 4 theorems (`infoGeometric_schrodinger₁/₂/₃`,
  `infoGeometric_ehrenfest`): the IG Schrödinger/Ehrenfest *evolution equations* for
  divergence-preserving flows, deliberately mirroring the quantum `Schrodinger.lean`. It lives
  entirely on `DivergencePreservingFamily`, so it belongs in **`Flow/`, not Quantum** →
  `Flow/Schrodinger.lean` (drop "-Like"). (My earlier draft mis-filed it under Quantum/.)
- **`CramerRao/Cross.lean`** = the score↔estimator **cross-covariance identity**
  (`covariance_score_eq_deriv_target`: `Cov_θ(T, s) = ∇E_θ[T]`) plus its Leibniz /
  differentiate-under-the-integral and centered-integrability support. It's the step between
  `Basic` (defs) and `CauchySchwarz` (which imports it) → `Bound`. → `CramerRao/Covariance.lean`.
- **Minor:** `GeometricData.lean` header carries cruft (`Target:` line + a `NOTE:` paragraph
  inside the copyright block) — clean during the rename pass.

### Remaining follow-ups (post-move, none block the build)
1. **Module-title gap** — 7 files have only `/-! ### section -/` blocks, no titled
   `/-! # Title … -/`: `CramerRao/{Bound, CauchySchwarz, Covariance}`,
   `Connection/{Basic, AmariChentsov}`, `Flow/Schrodinger`, `Flow/Family`. Additive, no build risk.
2. **Stale prose filename refs** (8, cosmetic — docstrings mention old paths): `Connection/Bartlett`
   (`CubicTensor.lean`), `Flow/CubicInvariance` (`mConnect.lean` ×3), `Flow/FaaDiBruno` (`Hessian.lean`),
   `Regularity` (`InformationGeometry.Dynamics`), `StatisticalManifold` (`KLDivergence.lean` ×2 — should
   point to `Divergence.lean`). Sweep alongside #1.
3. **KL consolidation** (§3.1 of the audit) — still pending: merge `klDivergence` into one model-level
   `klDiv`. Separate code change.

---

## 4. Decision log
_(record `accepted` / rejected decisions here as they're made, with date)_

- 2026-06-13 — doc created; InformationGeometry docstring/header first pass already complete
  (see git history), independent of the renames above.
- 2026-06-13 — duplication audit: KL divergence is real duplication → consolidate to one
  model-level `klDiv`, retire `klDivergence`. `InfoGeometricGenerator` vs
  `GeometricData.Generator` is an intentional concrete/abstract pair (proven `≃`) → keep both.
- 2026-06-13 — content audit: `SchrodingerLike` = IG evolution equations → `Flow/Schrodinger`;
  `CramerRao/Cross` = score↔estimator covariance identity → `CramerRao/Covariance`. Found 7 IG
  files still missing a titled module docstring (listed in §3) — to finish.
- 2026-06-13 — **APPLIED the full IG layout**: 18 moves/renames + FaaDiBruno merge (2→1) +
  Spectra.lean regenerated; `lake build` green (3959 jobs). (Some renames — Fisher/Metric,
  Fisher/Information, MConnect — were already on disk from concurrent edits; reconciled.)
  Remaining: module-title gap (7), KL consolidation, 8 cosmetic prose refs.

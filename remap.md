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

## 3. InformationGeometry (DRAFT — pending §2 decisions)

From the design discussion. Marked **draft**: the internal breakdown should follow whatever
§2 ratifies. The move dissolves `Dynamics/` (it mixed static geometry with a foundational
regularity file) and renames the `StoneLike/` flow theory.

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
    Cross.lean                 (→ Covariance.lean? — open, depends on content)
    Bound.lean                 (unchanged)
    Quantum.lean               (was SchrodingerRLD)
  Flow/                        (was StoneLike/)
    Basic.lean                 (unchanged path within area)
    Family.lean                (unchanged)
    Generator.lean             (unchanged)
    FaaDiBruno.lean            (merge FaaDiBruno/Basic + Helpers)
    MixtureConnection.lean     (was mConnect)
    CubicInvariance.lean       (was PreservesCubic)
  Quantum/                     (or leave Dichotomy/Schrodinger at root)
    Dichotomy.lean             (was Dichotomy)
    Schrodinger.lean           (was SchrodingerLike — open: what is this file?)
```

### Open questions blocking this draft
1. **Possible duplication:** `InfoGeometricGenerator` appears in *both* `GeometricData.lean`
   and `StoneLike/Basic.lean`; two divergence defs exist (`klDivergence` in
   `StatisticalManifold`, `klDiv` in `Hessian`). Intentional (abstract vs concrete) or
   leftover overlap to merge? Reorganizing around a duplicated generator would bake the
   duplication in.
2. **`SchrodingerLike.lean`** returned no title/objects — stub, or a QM bridge?
3. **`CramerRao/Cross.lean`** — cross-covariance for the bound, or something else?

---

## 4. Decision log
_(record `accepted` / rejected decisions here as they're made, with date)_

- 2026-06-13 — doc created; InformationGeometry docstring/header first pass already complete
  (see git history), independent of the renames above.

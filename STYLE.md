# Spectra Style Guide

Spectra is a Lean 4 library built on [Mathlib](https://github.com/leanprover-community/mathlib4),
formalizing spectral theory and mathematical quantum mechanics. Its conventions deliberately
mirror those of [PhysLean / PhysLib](https://physlib.io) and Mathlib, so that anyone fluent in
those libraries can read Spectra without a ramp-up — even if they never use it.

This document describes how Spectra source files should look. For *how to contribute* (building,
the PR workflow, etc.) see [CONTRIBUTING.md](CONTRIBUTING.md).

When this guide is silent on a point, **follow Mathlib.** The two references that matter most are:

- Documentation style — <https://leanprover-community.github.io/contribute/doc.html>
- Naming conventions — <https://leanprover-community.github.io/contribute/naming.html>

---

## 1. Anatomy of a file

Every `.lean` file in `Spectra/` has the same skeleton, in this order:

```lean
/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Spectra.Operator.Symmetric

/-!
# Title of the file

A paragraph (or several) explaining what this file builds and why it exists.
Written in prose, for a reader who has not seen the code.

## Main definitions

* `fooOperator` — the operator `F` acting on …

## Main statements

* `fooOperator_symmetric` — `F` is symmetric on its domain.

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section IV.1
-/

open InnerProductSpace MeasureTheory Complex
open scoped Topology

namespace Spectra.Operator

/-! ## Spectral region types -/

/-- One-line docstring describing the definition. -/
def foo : Type := …

end Spectra.Operator
```

### 1.1 Copyright header

Every file **opens** with the copyright block, before any `import`:

```lean
/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
```

- The year is the year the file was created.
- `Authors:` lists everyone who has made substantial contributions, in alphabetical order
  by last name. If you make a substantial change to an existing file, add yourself.
- Do **not** add a `Filename:` line — the path is already the path. (Some early files have one;
  it should be removed during cleanup.)

> Note: Spectra is Apache 2.0-licensed, matching Mathlib and PhysLean. Keep the wording above
> exactly so it stays consistent across the library.

### 1.2 Imports

- `import` lines come immediately after the header, before the module docstring.
- Group Mathlib imports first, then Spectra imports. Within a group, keep them sorted.
- Import the most specific file you need, not a broad umbrella.
- Avoid inline `-- explanatory` comments scattered through the import block; if an import is
  surprising, say why in the module docstring instead.

### 1.3 Module docstring

Immediately after the imports, every file has a module docstring delimited by `/-! … -/`:

```lean
/-!
# Title

Prose overview.

## Main definitions
## Main statements
## References
-/
```

- `# Title` — a short title in Title Case, on the first line.
- A prose overview follows. Explain the *mathematics* and the *design decisions*, not just
  a restatement of the names. The `Symmetric.lean` "Design notes" section is a good model.
- Then the standard sections, each introduced by `##`:
  - **`## Main definitions`** — bullet list, `` * `name` — description. ``
  - **`## Main statements`** — the headline theorems/lemmas. *(Use "Main statements", not
    "Main results"; pick one heading and Spectra uses this one.)*
  - **`## Notation`** *(optional)* — any custom notation introduced.
  - **`## Implementation notes`** / **`## Design notes`** *(optional)* — non-obvious choices.
  - **`## References`** — citations in Mathlib's `[Author, *Title*][bibkey]` form.
  - **`## Tags`** *(optional)* — search keywords.

### 1.4 `open` and `namespace`

- After the docstring, `open` the namespaces you use, then `open scoped` for scoped notation.
- Then declare a single `namespace`, prefixed with `Spectra` and mirroring the directory path:
  `Spectra/Operator/Symmetric.lean` lives in `namespace Spectra.Operator`.
- Close it with `end Spectra.Operator` at the bottom of the file.

### 1.5 Section dividers

Within a file, group related declarations under section comments:

```lean
/-! ## Neumann series -/
```

These mirror the `## Main statements` headings and make long files navigable.

---

## 2. Docstrings on declarations

**This is the most important rule, and the one Spectra most needs to catch up on.**

> Every `def`, `abbrev`, `structure`, `class`, `instance`, `lemma`, and `theorem` gets a
> docstring with `/-- … -/`.

PhysLean requires docstrings on *all definitions*; Spectra extends this to lemmas and theorems
too, because a reader scanning the file should understand each result without reading its proof.

Good:

```lean
/-- The Neumann series `∑_{k=0}^∞ Tᵏ = (1 - T)⁻¹` for `‖T‖ < 1`,
realized as the inverse of the unit `1 - T`. -/
noncomputable def neumannSeries (T : E →L[ℂ] E) (hT : ‖T‖ < 1) : E →L[ℂ] E :=
  ↑(Units.oneSub T hT)⁻¹

/-- `(1 - T) * neumannSeries T = 1`: the Neumann series is a left inverse of `1 - T`. -/
lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E :=
  (Units.oneSub T hT).mul_inv
```

Avoid (a bare lemma with no docstring):

```lean
lemma neumannSeries_mul_left (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℂ E - T) * neumannSeries T hT = ContinuousLinearMap.id ℂ E :=
  (Units.oneSub T hT).mul_inv
```

Docstring guidance:

- One sentence is enough for most lemmas: say *what is true*, not *how it's proved*.
- Use backticks for code and Unicode math (`` `‖T‖ < 1` ``); use `$…$`-free prose otherwise.
- Restate the statement in words when the name alone is cryptic. A `private` helper still gets a
  docstring, even a terse one.
- Mathematical "why it matters" belongs in the module docstring; per-declaration docstrings stay
  local and factual.

---

## 3. Naming

Follow Mathlib naming exactly.

| Kind | Convention | Example |
|------|-----------|---------|
| Types, structures, classes, `Prop`s | `UpperCamelCase` | `SymmetricOperator`, `OffRealAxis` |
| Definitions, data, functions | `lowerCamelCase` | `neumannSeries`, `commutatorAt` |
| Lemmas, theorems | `snake_case` describing the statement | `neumannSeries_mul_left` |
| Files and directories | `UpperCamelCase`, alphabetic only | `Symmetric.lean`, `RadialProblem/` |

- Theorem names read as a description of the conclusion: `inner_self_im_eq_zero`,
  `opNorm_pow_tendsto_zero`. Mathlib's naming page covers the vocabulary (`_of_`, `_iff_`, etc.).
- **File names use letters only — no underscores or digits.** `CHSH_Basic.lean` should become
  `ChshBasic.lean`; `Op_square.lean` → `OpSquare.lean`. (Renames are a separate pass from
  docstrings, but new files must follow this from the start.)

---

## 4. Formatting

Spectra inherits Mathlib's formatting:

- **Line length: 100 characters.** Break long signatures across lines with a 4-space continuation
  indent (see the `calc` and multi-line lemma signatures in `Resolvent/Defs.lean`).
- **Indentation: 2 spaces.** No tabs.
- A blank line separates the import block from the module docstring, and separates top-level
  declarations from each other.
- Tactic blocks use `by` at the end of the line, with the block indented 2 spaces.
- No trailing whitespace; files end with a single newline.
- Delete scaffolding comments (`-- (keep this, unchanged)`, commented-out experiments) before
  committing — they are editing artifacts, not documentation.

---

## 5. Informal and unfinished results

PhysLean has dedicated tooling (`informal_def`, `informal_lemma`, `semiformal_result`, tagged
`TODO`s via `import PhysLean.Meta.*`). Spectra does **not** vendor that infrastructure. Until it
does, use plain conventions:

- **TODO**: a normal comment, `-- TODO: <what is to be done>`, placed where the work belongs.
  A whole-file plan can live in a `TODO.lean` module.
- **`sorry`**: only in clearly-marked work-in-progress, never in a file imported by a "finished"
  result. Note it in the module docstring so it isn't mistaken for complete.
- **Informal statements**: write the intended statement in the module docstring's prose, or as a
  `def`/`lemma` with a `sorry` body and a docstring saying it is not yet proved.

---

## 6. Quick checklist before committing

- [ ] Copyright header present, Apache 2.0, correct year and authors, no `Filename:` line.
- [ ] Imports sorted, specific, Mathlib-then-Spectra.
- [ ] Module docstring with `# Title`, prose, `## Main definitions`, `## Main statements`,
      `## References`.
- [ ] Single `namespace Spectra.…` matching the path, closed with `end`.
- [ ] **Every** `def`/`lemma`/`theorem`/`instance` has a `/-- … -/` docstring.
- [ ] Names follow Mathlib casing; file name is letters-only `UpperCamelCase`.
- [ ] Lines ≤ 100 chars, 2-space indent, no trailing whitespace, no scaffolding comments.
- [ ] `lake build` succeeds.

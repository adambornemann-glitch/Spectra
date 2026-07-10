# Contributing to Spectra

Spectra is a Lean 4 formalization of spectral theory and mathematical quantum mechanics, built on
[Mathlib](https://github.com/leanprover-community/mathlib4). Its conventions follow
[PhysLean / PhysLib](https://physlib.io) and Mathlib closely, so the codebase reads the way those
libraries do.

Contributions of every size are welcome — a single new lemma, a docstring, a golfed proof, or a
whole new module. **Small pull requests are better than large ones**, even if a PR is just one
result; they are far easier to review and land.

---

## Getting set up

Spectra uses the standard Lean 4 / Lake toolchain. The pinned toolchain is in
[`lean-toolchain`](lean-toolchain) and is installed automatically by `elan`.

1. Install [`elan`](https://github.com/leanprover/elan) (the Lean version manager).
2. Clone the repository and fetch prebuilt Mathlib artifacts (this avoids recompiling Mathlib):

   ```sh
   git clone <your-fork-url> Spectra
   cd Spectra
   lake exe cache get
   ```

3. Build the library:

   ```sh
   lake build
   ```

The recommended editor is **VS Code with the Lean 4 extension**, which gives you the interactive
goal view, hover docstrings, and the `#lint` / `#check` commands inline.

---

## Project layout

- [`Spectra.lean`](Spectra.lean) is the root module: it simply imports every file in the library.
  When you add a new file, add a matching `import Spectra.…` line here (kept sorted) so it is part
  of the build.
- Source lives under [`Spectra/`](Spectra/), organized by topic — `Resolvent/`, `SpectralTheory/`,
  `QuantumMechanics/`, `Spaces/Sobolev/`, and so on.
- `Spectra/Mathlib/` holds material that is intended to eventually be upstreamed to Mathlib, mirroring
  Mathlib's own directory structure. Keep things here Mathlib-general (no Spectra-specific
  assumptions) so the eventual port is mechanical.

The directory path and the namespace match: a file at `Spectra/Resolvent/Defs.lean` declares
`namespace Spectra.Resolvent`.

---

## The contribution workflow

1. **Branch** off `master` for your change.
2. **Write** the code following [STYLE.md](STYLE.md). The non-negotiables:
   - the copyright header,
   - a module docstring with `# Title`, `## Main definitions`, `## Main statements`, `## References`,
   - **a `/-- … -/` docstring on every `def`, `lemma`, `theorem`, and `instance`.**
3. **Build** locally with `lake build` — the change must compile with no errors and no new `sorry`
   in finished files.
4. **Lint** (see below).
5. **Commit** with a clear message describing the result added. Keep the PR focused on one thing.
6. **Open a pull request** against `master`. Describe what you proved/added and reference any source
   (paper, textbook section) the formalization follows.

### Adding a new file

A new file must, from the start:

- open with the Apache 2.0 copyright header,
- carry a full module docstring,
- declare a single `Spectra.…` namespace matching its path,
- have a letters-only `UpperCamelCase` filename (no underscores or digits),
- be wired into [`Spectra.lean`](Spectra.lean).

---

## Linting and quality

Spectra inherits Mathlib's linters. At minimum, before opening a PR:

- Make sure `lake build` is clean.
- Run Mathlib's environment linters on your file by adding `#lint` at the bottom while developing
  (remove it before committing), or check the goal panel for linter warnings. These catch missing
  docstrings, unused arguments, simp-normal-form issues, and more.
- Re-read [STYLE.md §6](STYLE.md) and walk the checklist.

> Spectra ships a CI workflow ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) with two gates:
>
> - the **axiom gate** ([`AxiomCheck.lean`](AxiomCheck.lean)) — Mathlib's `assert_no_sorry` on every
>   headline result, wired as a default build target, so a `sorry` reaching one fails CI; and
> - the **length ratchet** ([`scripts/check_lengths.py`](scripts/check_lengths.py)) — file (≤ 1500
>   lines) and line-width (≤ 100 chars) budgets matching Mathlib's `longFile` / `longLine` linters, plus
>   a declaration-span budget (≤ 75 lines, a *house* guideline, not a Mathlib rule). It is checked
>   against [`scripts/length-baseline.txt`](scripts/length-baseline.txt), so only *new or worsened*
>   offenders fail — the grandfathered list can only shrink. After improving a long file/proof,
>   regenerate the baseline (`python3 scripts/check_lengths.py --write-baseline scripts/length-baseline.txt`)
>   to lock in the gain.
>
> Spectra does not yet vendor PhysLean's full `lake exe lint_all` / `scripts/lint-style.sh` text-style
> suite — adding more checks is welcome; until then, the gates above + `#lint` + the STYLE.md checklist
> are the bar.

### Compile-time monitoring

[`scripts/check_compile_time.py`](scripts/check_compile_time.py) times how long each file takes to
elaborate in isolation (`lake env lean <file>`, against already-built dependency `.olean`s — the same
unit of work Lake redoes when a file changes) and flags anything slower than a threshold (default 5s)
so it can be assessed. There's no external "correct" number here — Mathlib manages compile time via a
*relative* CI regression bot plus its line-count linter, not an absolute per-file wall-clock budget —
5s was picked from this library's own data: a clean (uncontended) full sweep put ~1-4s down to nothing
more than each file's own Mathlib-heavy import-closure loading (a real, unavoidable floor, not a
measurement artifact), while the genuine outliers sit at 5s+. The tool ships with a baseline ratchet
exactly like the length checker, plus a *tolerance* (default 50% relative / 1s absolute) since
wall-clock timings are noisier than line counts:

```sh
lake exe cache get && lake build                        # must be built first
python3 scripts/check_compile_time.py --changed          # fast: files touched vs. base + working tree
python3 scripts/check_compile_time.py --all --jobs 4     # full sweep (slower; jobs>1 trades fidelity for speed)
python3 scripts/check_compile_time.py --changed --strict --baseline scripts/compile-time-baseline.txt
```

After genuinely speeding up a slow file, regenerate the baseline (`--all --write-baseline
scripts/compile-time-baseline.txt`) to lock in the gain. This is currently a local/manual tool, not
wired into CI — see [`scripts/compile-time-baseline.txt`](scripts/compile-time-baseline.txt) for the
current picture.

It can also track the *shape* of the build over time. `--graph` prints an ASCII histogram of the
current run's time distribution straight to the terminal (no file). `--history [PATH]` appends this
run's aggregate stats (mean/median/p90/max/count-over-threshold) as one JSON line to
[`scripts/compile-time-history.jsonl`](scripts/compile-time-history.jsonl) by default — aggregate,
not per-file, so it survives files being added, split, or renamed. `--trend [PATH]` reads that log
back as an ASCII sparkline:

```sh
python3 scripts/check_compile_time.py --all --graph                                   # this run's histogram
python3 scripts/check_compile_time.py --all --history                                 # record a data point
python3 scripts/check_compile_time.py --trend                                         # see the trend
```

---

## Informal and work-in-progress results

Spectra does not (yet) use PhysLean's `informal_def` / `semiformal_result` machinery. Instead:

- Mark unfinished work with `-- TODO: …` comments, or a `TODO.lean` module for a larger plan.
- A `sorry` is acceptable only in a clearly work-in-progress file, and must be flagged in that
  file's module docstring. Never leave a `sorry` in a file that other "finished" files import.

---

## Questions and conventions

If a situation isn't covered here or in [STYLE.md](STYLE.md), follow Mathlib's conventions:

- Documentation style — <https://leanprover-community.github.io/contribute/doc.html>
- Naming — <https://leanprover-community.github.io/contribute/naming.html>

When in doubt, open the PR and ask in the description — a reviewer would rather discuss a small,
clear change than a large one built on a guess.

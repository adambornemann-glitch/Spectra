# `@Meta` — tooling for the Spectra library

Small, dependency-free Python utilities for understanding, auditing, and
extending the Spectra Lean 4 formalization. Everything here is **pure Python 3
standard library** — no `pip install`, no virtualenv. Run any script from the
repository root:

```bash
python3 @Meta/lib_stats.py
```

The scripts locate the repo automatically (they walk up to the directory
containing `lakefile.lean`), so they work from any working directory.

---

## Scripts

### `lib_stats.py` — bird's-eye statistics
Files, lines (code / comment / blank), declarations by kind, documentation
coverage, `sorry`/`axiom` totals, per-area breakdown, and the largest files.

```bash
python3 @Meta/lib_stats.py            # report
python3 @Meta/lib_stats.py --top 20   # 20 largest files
python3 @Meta/lib_stats.py --json     # machine-readable
```

### `audit.py` — "what isn't finished?"
Comment-aware scan for open proof obligations and stubs. Because it works on a
*comment-blanked* view of each file, the word `sorry` inside a doc-string is not
mistaken for a real `sorry`. Exits non-zero when any genuine obligation
(`sorry` / `admit` / `axiom`) is found, so it works as a CI gate.

```bash
python3 @Meta/audit.py                       # full report
python3 @Meta/audit.py --only sorry,axiom    # subset
python3 @Meta/audit.py --strict              # also fail on `: True` stubs
python3 @Meta/audit.py --json
```

Categories: `sorry`, `admit`, `axiom`, `placeholder` (a declaration whose body
or type is literally `True` — heuristic), `todo` (TODO/FIXME/XXX/HACK).

### `aggregator.py` — keep `Spectra.lean` in sync with disk
The root `Spectra.lean` is a hand-maintained list of `import Spectra.…` lines.
This reconciles it against the files actually present.

```bash
python3 @Meta/aggregator.py            # read-only report
python3 @Meta/aggregator.py --fix      # insert missing imports (sorted)
python3 @Meta/aggregator.py --prune    # remove imports of missing files
python3 @Meta/aggregator.py --fix --prune
```

- **orphans** — source files on disk the aggregator never imports (so they don't
  build as part of the library).
- **dangling** — active imports with no file on disk (so the build breaks).

`--fix`/`--prune` **edit `Spectra.lean`**. They only ever touch *active* import
lines: imports commented out with `--` or wrapped in a `/- … -/` block are left
exactly alone.

### `import_graph.py` — internal dependency graph
The `import` graph over Spectra's own modules (external imports ignored).

```bash
python3 @Meta/import_graph.py                 # summary
python3 @Meta/import_graph.py --orphans       # unreachable from the root
python3 @Meta/import_graph.py --cycles        # import cycles (Lean forbids them)
python3 @Meta/import_graph.py --rank 20       # most depended-upon modules
python3 @Meta/import_graph.py --deps  KMS.Equivalence    # what it needs
python3 @Meta/import_graph.py --rdeps Stone.Basic        # what needs it
python3 @Meta/import_graph.py --dot --area KMS | dot -Tsvg -o kms.svg
```

Module names may be full (`Spectra.KMS.ImaginaryTime`) or a unique suffix
(`KMS.ImaginaryTime`).

> **orphans here vs. in `aggregator.py`.** `aggregator.py` reports files not
> *directly* listed in `Spectra.lean`. `import_graph.py --orphans` reports files
> not reachable *transitively* — a file missing from `Spectra.lean` is still
> reachable if some imported module pulls it in. The graph's set is the one that
> truly never builds.

### `new_module.py` — scaffold a new module
Creates a file with the house copyright header, module doc-string, and namespace,
then wires its import into `Spectra.lean` in sorted position.

```bash
python3 @Meta/new_module.py KMS.Tomita --title "Tomita–Takesaki setup"
python3 @Meta/new_module.py Resolvent/Foo --import Mathlib.Analysis.Normed.Basic
python3 @Meta/new_module.py Scratch.Tmp --no-wire     # leave Spectra.lean alone
```

The module argument accepts a dotted name or a path, with or without the leading
`Spectra.` / trailing `.lean`.

---

## Suggested workflow

```bash
# before committing a batch of new files
python3 @Meta/aggregator.py            # everything wired in & sorted?
python3 @Meta/audit.py                 # any new sorries sneak in?
python3 @Meta/import_graph.py --cycles # no accidental import cycle?
```

## Notes / limitations

- These tools parse Lean with comment-aware regexes, **not** a real elaborator.
  Counts are a faithful estimate; exotic syntax may be miscounted.
- `_spectra_meta.py` is the shared library (repo discovery, module ⇄ path
  mapping, the comment-blanking parser). The other scripts import it; keep it
  beside them.

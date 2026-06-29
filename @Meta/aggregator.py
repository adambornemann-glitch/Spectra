#!/usr/bin/env python3
"""Keep the root ``Spectra.lean`` aggregator honest.

``Spectra.lean`` is a hand-maintained flat list of ``import Spectra.…`` lines --
one per source module. It is easy for it to drift: a new file is added but never
imported (so it never builds), or a file is deleted/renamed but its import lines
on (so the build breaks). This script reconciles the aggregator against what is
actually on disk.

    python3 @Meta/aggregator.py            # report drift (read-only)
    python3 @Meta/aggregator.py --fix      # insert missing imports, sorted
    python3 @Meta/aggregator.py --prune    # remove imports of missing files
    python3 @Meta/aggregator.py --fix --prune

Reports three things:
    orphans    source files on disk that the aggregator never imports
    dangling   imports in the aggregator with no corresponding file
    order      whether the active import block is sorted

``--fix`` only inserts the missing imports (it preserves comments, commented-out
``--import`` lines, and any other content). ``--prune`` deletes dangling import
lines. Exit status is non-zero when drift remains.
"""

from __future__ import annotations

import argparse
import re
import sys

import _spectra_meta as M

IMPORT_RE = re.compile(r"^\s*import\s+(" + re.escape(M.LIB_NAME) + r"\.[\w.]+)\s*$")


def source_modules(repo_root):
    return {
        M.module_of_path(p, repo_root)
        for p in M.iter_lean_files(repo_root)
    }


def aggregator_imports(lines):
    """Return ``[(line_index, module), ...]`` for *active* imports only.

    Detection runs against a comment-blanked copy of the text, so imports that
    are commented out -- whether with ``--`` or wrapped in a ``/- ... -/`` block
    -- are correctly ignored (they are not seen by the Lean compiler either).
    The blanked text preserves newlines, so line indices match ``lines``."""
    code, _, _ = M._blank_comments("\n".join(lines))
    out = []
    for i, code_line in enumerate(code.splitlines()):
        m = IMPORT_RE.match(code_line)
        if m:
            out.append((i, m.group(1)))
    return out


def analyze(repo_root):
    agg = M.aggregator_path(repo_root)
    lines = agg.read_text(encoding="utf-8").splitlines()
    imports = aggregator_imports(lines)
    imported = {mod for _, mod in imports}
    on_disk = source_modules(repo_root)
    # the aggregator file itself is a module ("Spectra") but never imports itself
    on_disk.discard(M.LIB_NAME)

    orphans = sorted(on_disk - imported)
    dangling = sorted(imported - on_disk)
    ordered = [mod for _, mod in imports]
    is_sorted = ordered == sorted(ordered)

    return {
        "path": agg,
        "lines": lines,
        "imports": imports,
        "orphans": orphans,
        "dangling": dangling,
        "is_sorted": is_sorted,
    }


def do_fix(lines, orphans):
    """Insert ``import`` lines for *orphans* in sorted position relative to the
    existing active import lines. Returns the new list of lines."""
    lines = list(lines)
    for mod in orphans:
        new_line = f"import {mod}"
        imports = aggregator_imports(lines)  # recompute after each insert
        insert_at = None
        for idx, existing in imports:
            if existing > mod:
                insert_at = idx
                break
        if insert_at is None:
            # after the last active import (or at EOF if there are none)
            insert_at = (imports[-1][0] + 1) if imports else len(lines)
        lines.insert(insert_at, new_line)
    return lines


def do_prune(lines, dangling):
    """Remove *active* import lines whose module is in *dangling*. Commented-out
    imports are never touched (they are not active imports)."""
    dangling = set(dangling)
    drop = {i for i, mod in aggregator_imports(lines) if mod in dangling}
    return [ln for i, ln in enumerate(lines) if i not in drop]


def main():
    ap = argparse.ArgumentParser(description="Reconcile Spectra.lean with disk.")
    ap.add_argument("--fix", action="store_true",
                    help="insert imports for orphan source files (sorted)")
    ap.add_argument("--prune", action="store_true",
                    help="remove imports whose source file is missing")
    args = ap.parse_args()

    repo_root = M.find_repo_root()
    info = analyze(repo_root)
    relpath = M.rel(info["path"], repo_root)

    print(f"Aggregator: {relpath}")
    print(f"  active imports : {len(info['imports'])}")
    print(f"  orphans        : {len(info['orphans'])}  (on disk, not imported)")
    print(f"  dangling       : {len(info['dangling'])}  (imported, file missing)")
    print(f"  sorted         : {'yes' if info['is_sorted'] else 'NO'}")

    if info["orphans"]:
        print("\n  ORPHANS — add these (or run --fix):")
        for m in info["orphans"]:
            print(f"    import {m}")
    if info["dangling"]:
        print("\n  DANGLING — these will not build (run --prune to remove):")
        for m in info["dangling"]:
            print(f"    import {m}")

    if not args.fix and not args.prune:
        drift = info["orphans"] or info["dangling"] or not info["is_sorted"]
        if not drift:
            print("\n  ✓ aggregator is complete and sorted.")
        sys.exit(1 if drift else 0)

    lines = info["lines"]
    if args.fix and info["orphans"]:
        lines = do_fix(lines, info["orphans"])
        print(f"\n  + inserted {len(info['orphans'])} import(s)")
    if args.prune and info["dangling"]:
        lines = do_prune(lines, info["dangling"])
        print(f"  - pruned {len(info['dangling'])} dangling import(s)")

    info["path"].write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"  wrote {relpath}")

    # re-analyze so the exit code reflects the post-write state
    after = analyze(repo_root)
    remaining = after["orphans"] or after["dangling"]
    sys.exit(1 if remaining else 0)


if __name__ == "__main__":
    main()

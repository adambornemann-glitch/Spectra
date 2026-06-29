#!/usr/bin/env python3
"""Scaffold a new Spectra module with the house header and wire it into the
root aggregator.

The library has a fixed file preamble (copyright block, module doc-string,
namespace) and every module must be ``import``ed from ``Spectra.lean`` or it
never builds. This script does both, so a new file starts life conventional and
connected.

    python3 @Meta/new_module.py KMS.Tomita
    python3 @Meta/new_module.py Spectra.Resolvent.Foo --title "Foo operators"
    python3 @Meta/new_module.py QM/Widget --import Mathlib.Analysis.Normed.Basic \
                                          --import Spectra.Operator.Symmetric
    python3 @Meta/new_module.py Scratch.Tmp --no-wire    # don't touch Spectra.lean

The module may be given as a dotted name (``KMS.Tomita`` / ``Spectra.KMS.Tomita``)
or a path (``KMS/Tomita`` / ``KMS/Tomita.lean``). The leading ``Spectra.`` is
optional and added for you.
"""

from __future__ import annotations

import argparse
import datetime as _dt
from pathlib import Path

import _spectra_meta as M
import aggregator  # reuse the comment-aware sorted insertion

HEADER_TMPL = """\
/-
Copyright (c) {year} Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: {authors}
-/
{imports}
/-!
# {title}

TODO: describe what this file establishes.

## Main results

* `{namespace}.`
-/

namespace {namespace}


end {namespace}
"""


def normalize_module(raw: str) -> str:
    """Accept ``KMS.Tomita`` / ``Spectra.KMS.Tomita`` / ``KMS/Tomita[.lean]``
    and return the full dotted module name."""
    raw = raw.strip().replace("\\", "/")
    if raw.endswith(".lean"):
        raw = raw[: -len(".lean")]
    dotted = raw.replace("/", ".")
    if not dotted.startswith(M.LIB_NAME + "."):
        dotted = f"{M.LIB_NAME}.{dotted}"
    return dotted


def default_namespace(module: str) -> str:
    parts = module.split(".")
    return ".".join(parts[:-1]) if len(parts) > 1 else module


def render(module, title, authors, imports, namespace, year):
    if imports:
        import_block = "\n".join(f"import {i}" for i in imports) + "\n"
    else:
        import_block = "-- TODO: add imports\n"
    return HEADER_TMPL.format(
        year=year,
        authors=authors,
        title=title,
        namespace=namespace,
        imports=import_block,
    )


def wire_into_aggregator(repo_root, module):
    agg = M.aggregator_path(repo_root)
    lines = agg.read_text(encoding="utf-8").splitlines()
    active = {m for _, m in aggregator.aggregator_imports(lines)}
    if module in active:
        return False
    lines = aggregator.do_fix(lines, [module])
    agg.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return True


def main():
    ap = argparse.ArgumentParser(description="Scaffold a new Spectra module.")
    ap.add_argument("module", help="dotted name or path, e.g. KMS.Tomita")
    ap.add_argument("--title", help="module doc title (default: the file stem)")
    ap.add_argument("--authors", default="Adam Bornemann", help="Authors: line")
    ap.add_argument("--import", dest="imports", action="append", default=[],
                    metavar="MODULE", help="an import line (repeatable)")
    ap.add_argument("--namespace", help="override the namespace")
    ap.add_argument("--no-wire", action="store_true",
                    help="do not add the import to Spectra.lean")
    ap.add_argument("--force", action="store_true", help="overwrite if it exists")
    args = ap.parse_args()

    repo_root = M.find_repo_root()
    module = normalize_module(args.module)
    path = M.path_of_module(module, repo_root)
    title = args.title or module.split(".")[-1]
    namespace = args.namespace or default_namespace(module)
    year = _dt.date.today().year

    if path.exists() and not args.force:
        raise SystemExit(f"refusing to overwrite existing file: {M.rel(path, repo_root)} "
                         f"(use --force)")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render(module, title, args.authors, args.imports, namespace, year),
                    encoding="utf-8")
    print(f"created  {M.rel(path, repo_root)}")
    print(f"module   {module}")
    print(f"namespace {namespace}")

    if args.no_wire:
        print("skipped  Spectra.lean (--no-wire)")
    elif wire_into_aggregator(repo_root, module):
        print(f"wired    import {module}  ->  {M.LIB_NAME}.lean")
    else:
        print(f"note     {module} already imported in {M.LIB_NAME}.lean")


if __name__ == "__main__":
    main()

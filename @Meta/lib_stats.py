#!/usr/bin/env python3
"""Library statistics for Spectra.

A bird's-eye view of the formalization: file/line counts, declarations broken
down by kind and by subject area, documentation coverage, and incompleteness
markers (``sorry`` / ``axiom``).

Usage:
    python3 @Meta/lib_stats.py            # human-readable report
    python3 @Meta/lib_stats.py --json     # machine-readable
    python3 @Meta/lib_stats.py --top 15   # show the 15 largest files

Heuristics: declarations and comments are detected by a comment-aware parser
(see _spectra_meta.py), so keywords inside comments/doc-strings are not counted.
It is not a Lean elaborator, so exotic syntax may be miscounted -- treat the
numbers as a faithful estimate, not gospel.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter

import _spectra_meta as M

IGNORED_AREAS = {"Scratch"}

def tracked_module(module):
    return M.top_area(module) not in IGNORED_AREAS


def gather(repo_root, include_scratch=False):
    all_sources = M.load_all(repo_root)
    if include_scratch:
        sources = all_sources
        ignored = 0
    else:
        sources = [s for s in all_sources if tracked_module(M.module_of_path(s.path, repo_root))]
        ignored = len(all_sources) - len(sources)

    by_area_files = Counter()
    by_area_lines = Counter()
    by_area_decls = Counter()
    by_kind = Counter()
    documented = 0
    documentable = 0  # decls of a kind we expect to carry a doc-string
    total_lines = total_code = total_comment = total_blank = 0
    sorry_total = axiom_total = 0
    per_file = []

    # kinds for which a `/-- -/` doc-string is the norm in this library
    doc_expected = {"theorem", "lemma", "def", "abbrev", "structure", "class",
                    "inductive", "opaque", "instance"}

    for s in sources:
        module = M.module_of_path(s.path, repo_root)
        area = M.top_area(module)
        decls = s.declarations()

        total_lines += s.total_lines
        total_code += s.code_lines
        total_comment += s.comment_lines
        total_blank += s.blank_lines

        by_area_files[area] += 1
        by_area_lines[area] += s.total_lines
        by_area_decls[area] += len(decls)

        n_sorry = len(re.findall(r"\bsorry\b", s.code))
        n_axiom = sum(1 for d in decls if d.kind == "axiom")
        sorry_total += n_sorry
        axiom_total += n_axiom

        for d in decls:
            by_kind[d.kind] += 1
            if d.kind in doc_expected:
                documentable += 1
                if d.documented:
                    documented += 1

        per_file.append({
            "module": module,
            "area": area,
            "lines": s.total_lines,
            "code": s.code_lines,
            "decls": len(decls),
            "sorry": n_sorry,
        })

    return {
        "files": len(sources),
        "source_scope": "all" if include_scratch else "tracked",
        "ignored_areas": [] if include_scratch else sorted(IGNORED_AREAS),
        "ignored_files": ignored,
        "lines": {
            "total": total_lines,
            "code": total_code,
            "comment": total_comment,
            "blank": total_blank,
        },
        "declarations": {
            "total": sum(by_kind.values()),
            "by_kind": dict(by_kind.most_common()),
        },
        "documentation": {
            "documented": documented,
            "documentable": documentable,
            "coverage_pct": round(100 * documented / documentable, 1) if documentable else 0.0,
        },
        "incompleteness": {"sorry": sorry_total, "axiom": axiom_total},
        "areas": {
            area: {
                "files": by_area_files[area],
                "lines": by_area_lines[area],
                "decls": by_area_decls[area],
            }
            for area in sorted(by_area_files, key=lambda a: -by_area_lines[a])
        },
        "per_file": per_file,
    }


def bar(value, total, width=24):
    if total <= 0:
        return ""
    filled = round(width * value / total)
    return "█" * filled + "·" * (width - filled)


def human_report(stats, top):
    L = stats["lines"]
    D = stats["declarations"]
    docs = stats["documentation"]
    inc = stats["incompleteness"]

    print("=" * 64)
    print("  SPECTRA — LIBRARY STATISTICS")
    print("=" * 64)
    if stats.get("source_scope") == "tracked":
        ignored = ", ".join(stats.get("ignored_areas", [])) or "none"
        print(f"  Source scope .............. tracked ({stats.get('ignored_files', 0)} ignored: {ignored})")
    else:
        print("  Source scope .............. all source files")
    print(f"  Source files .............. {stats['files']:>8,}")
    print(f"  Total lines ............... {L['total']:>8,}")
    print(f"    code .................... {L['code']:>8,}")
    print(f"    comments/doc ........... {L['comment']:>8,}")
    print(f"    blank .................. {L['blank']:>8,}")
    print(f"  Declarations .............. {D['total']:>8,}")
    print(f"  Doc coverage .............. {docs['coverage_pct']:>7}%  "
          f"({docs['documented']:,}/{docs['documentable']:,} documentable)")
    print(f"  `sorry` occurrences ....... {inc['sorry']:>8,}")
    print(f"  `axiom` declarations ...... {inc['axiom']:>8,}")

    print("\n  Declarations by kind")
    print("  " + "-" * 50)
    mx = max(D["by_kind"].values()) if D["by_kind"] else 1
    for kind, n in D["by_kind"].items():
        print(f"  {kind:<12} {n:>6,}  {bar(n, mx)}")

    print(f"\n  Subject areas ({len(stats['areas'])})")
    print("  " + "-" * 58)
    print(f"  {'area':<26}{'files':>7}{'lines':>9}{'decls':>8}")
    print("  " + "-" * 58)
    mxl = max((a["lines"] for a in stats["areas"].values()), default=1)
    for area, a in stats["areas"].items():
        print(f"  {area:<26}{a['files']:>7}{a['lines']:>9,}{a['decls']:>8,}  "
              f"{bar(a['lines'], mxl, 12)}")

    if top:
        print(f"\n  {top} largest files (by lines)")
        print("  " + "-" * 58)
        for f in sorted(stats["per_file"], key=lambda f: -f["lines"])[:top]:
            flag = f"  ⚠ {f['sorry']} sorry" if f["sorry"] else ""
            print(f"  {f['lines']:>6,}  {f['module']}{flag}")
    print()


def main():
    ap = argparse.ArgumentParser(description="Spectra library statistics.")
    ap.add_argument("--json", action="store_true", help="emit JSON instead of a report")
    ap.add_argument("--top", type=int, default=10,
                    help="how many largest files to list (0 to skip)")
    ap.add_argument("--include-scratch", action="store_true",
                    help="include temporary Spectra/Scratch files in the counts")
    args = ap.parse_args()

    repo_root = M.find_repo_root()
    stats = gather(repo_root, include_scratch=args.include_scratch)

    if args.json:
        print(json.dumps(stats, indent=2))
    else:
        human_report(stats, args.top)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Completeness / health audit for Spectra.

Scans the library for everything that means "not actually finished" and prints
each hit as a clickable ``file:line``. Because it works on a comment-blanked
view of every file, the word "sorry" sitting in a doc-string is *not* reported
as a real ``sorry`` -- only proof obligations that are genuinely open are.

Categories:
    sorry        an open proof obligation (the real thing, in code)
    admit        the `admit` tactic (an open obligation)
    axiom        a locally introduced `axiom` (an unproven assumption)
    placeholder  a statement whose type is literally `True` -- a stub that
                 proves nothing (heuristic, low-confidence; see --no-placeholder)
    todo         TODO / FIXME / XXX / HACK markers (in comments OR code)

Exit status is non-zero when any "open obligation" (sorry/admit/axiom) is found,
so this doubles as a CI gate:

    python3 @Meta/audit.py            # full report
    python3 @Meta/audit.py --only sorry,axiom
    python3 @Meta/audit.py --strict   # also fail on placeholders
    python3 @Meta/audit.py --json
"""

from __future__ import annotations

import argparse
import json
import re
import sys

import _spectra_meta as M

# category -> compiled pattern applied to the *comment-blanked* code, except
# `todo`, which is applied to the raw text (markers live in comments).
CODE_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
}
TODO_PATTERN = re.compile(r"\b(TODO|FIXME|XXX|HACK)\b")

# A "placeholder" is a declaration whose body/type is literally `True`: a stub
# that type-checks but proves nothing (e.g. `def IsNormal ... : Prop := True`).
# Several surface forms, all matched against comment-blanked code:
_PLACEHOLDER_PATTERNS = [
    re.compile(r":=\s*True\s*$"),        # `... := True`
    re.compile(r":\s*True\s*:="),        # `theorem foo : True := ...`
]


def _is_placeholder_line(code_line: str) -> bool:
    if code_line.strip() == "True":      # body sitting on its own line
        return True
    return any(p.search(code_line) for p in _PLACEHOLDER_PATTERNS)

# Categories that count as genuinely-open obligations for the exit code.
OPEN_OBLIGATIONS = {"sorry", "admit", "axiom"}

ALL_CATEGORIES = ["sorry", "admit", "axiom", "placeholder", "todo"]


def scan(repo_root, categories):
    findings = {c: [] for c in categories}

    for s in M.load_all(repo_root):
        module = M.module_of_path(s.path, repo_root)
        relpath = M.rel(s.path, repo_root)
        code_lines = s.code.splitlines()
        raw_lines = s.text.splitlines()

        if "axiom" in categories:
            for d in s.declarations():
                if d.kind == "axiom":
                    findings["axiom"].append({
                        "file": relpath, "module": module, "line": d.line,
                        "text": raw_lines[d.line - 1].strip() if d.line <= len(raw_lines) else d.name,
                    })

        for cat, pat in CODE_PATTERNS.items():
            if cat not in categories:
                continue
            for i, ln in enumerate(code_lines):
                if pat.search(ln):
                    findings[cat].append({
                        "file": relpath, "module": module, "line": i + 1,
                        "text": raw_lines[i].strip() if i < len(raw_lines) else ln.strip(),
                    })

        if "placeholder" in categories:
            for i, ln in enumerate(code_lines):
                if _is_placeholder_line(ln):
                    findings["placeholder"].append({
                        "file": relpath, "module": module, "line": i + 1,
                        "text": raw_lines[i].strip() if i < len(raw_lines) else ln.strip(),
                    })

        if "todo" in categories:
            for i, ln in enumerate(raw_lines):
                m = TODO_PATTERN.search(ln)
                if m:
                    findings["todo"].append({
                        "file": relpath, "module": module, "line": i + 1,
                        "marker": m.group(1), "text": ln.strip(),
                    })

    return findings


def human_report(findings, categories):
    labels = {
        "sorry": "OPEN PROOFS (sorry)",
        "admit": "OPEN PROOFS (admit)",
        "axiom": "LOCAL AXIOMS",
        "placeholder": "STUB STATEMENTS (`: True`)  [heuristic]",
        "todo": "TODO / FIXME MARKERS",
    }
    any_hits = False
    for cat in categories:
        hits = findings.get(cat, [])
        print(f"\n{labels[cat]} — {len(hits)}")
        print("-" * 64)
        if not hits:
            print("  (none)")
            continue
        any_hits = True
        for h in hits:
            loc = f"{h['file']}:{h['line']}"
            snippet = h["text"]
            if len(snippet) > 80:
                snippet = snippet[:77] + "..."
            print(f"  {loc}")
            print(f"      {snippet}")

    print("\n" + "=" * 64)
    counts = {c: len(findings.get(c, [])) for c in categories}
    summary = "  ".join(f"{c}={counts[c]}" for c in categories)
    print(f"  SUMMARY  {summary}")
    print("=" * 64)
    return any_hits


def main():
    ap = argparse.ArgumentParser(description="Spectra completeness / health audit.")
    ap.add_argument("--only", default="",
                    help="comma-separated subset of: " + ",".join(ALL_CATEGORIES))
    ap.add_argument("--no-placeholder", action="store_true",
                    help="skip the heuristic `: True` placeholder scan")
    ap.add_argument("--no-todo", action="store_true", help="skip TODO/FIXME markers")
    ap.add_argument("--strict", action="store_true",
                    help="also exit non-zero if any placeholders are found")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.only:
        categories = [c.strip() for c in args.only.split(",") if c.strip()]
        bad = [c for c in categories if c not in ALL_CATEGORIES]
        if bad:
            ap.error(f"unknown category/categories: {', '.join(bad)}")
    else:
        categories = list(ALL_CATEGORIES)
        if args.no_placeholder:
            categories.remove("placeholder")
        if args.no_todo:
            categories.remove("todo")

    repo_root = M.find_repo_root()
    findings = scan(repo_root, categories)

    if args.json:
        print(json.dumps(findings, indent=2))
    else:
        human_report(findings, categories)

    fail_on = set(OPEN_OBLIGATIONS)
    if args.strict:
        fail_on.add("placeholder")
    open_count = sum(len(findings.get(c, [])) for c in fail_on if c in categories)
    sys.exit(1 if open_count else 0)


if __name__ == "__main__":
    main()

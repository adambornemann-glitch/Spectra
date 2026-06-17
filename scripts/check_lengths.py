#!/usr/bin/env python3
"""Length / size checker for Spectra, with a baseline ratchet for CI.

Checks three things, two of which are real enforced Mathlib rules and one a
Spectra house guideline:

  * ``file``  — file longer than the budget (default 1500 lines).
                Mathlib rule: ``linter.style.longFile`` (default 1500).
  * ``line``  — source line wider than the budget (default 100 chars), measured
                in Unicode codepoints (as Lean's column count does, so multi-byte
                math symbols count as one). Mathlib rule: ``linter.style.longLine``;
                like it, URL lines and ``import`` lines are exempt.
  * ``decl``  — declaration whose source span exceeds the budget (default 75).
                NOT a Mathlib rule — a Spectra house guideline. Mathlib has no
                numeric proof-length limit; long proofs are only discouraged
                culturally. Tune or drop with ``--max-decl`` / ``--checks``.

Self-contained (only the standard library + a small comment-aware scanner) so it
runs in CI without the git-ignored ``@Meta`` toolkit.

Baseline ratchet
----------------
The repo already has many over-budget files/lines/declarations; fixing them all
at once is impractical. Instead, snapshot today's offenders into a baseline and
let CI fail only on *new or worsened* ones, so the list can only shrink:

    python3 scripts/check_lengths.py --write-baseline scripts/length-baseline.txt
    python3 scripts/check_lengths.py --strict --baseline scripts/length-baseline.txt

A violation fails the ratchet if it is absent from the baseline, or if its value
(file lines / long-line count / declaration span) is larger than the baselined
one. Improvements never fail; regenerate the baseline to lock them in.

Usage:
    python3 scripts/check_lengths.py                       # report, all checks
    python3 scripts/check_lengths.py --checks file,line    # subset of checks
    python3 scripts/check_lengths.py --limit 0 --json      # full machine output
    python3 scripts/check_lengths.py --strict              # exit 1 on any violation
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

LIB_NAME = "Spectra"
MAX_FILE_DEFAULT = 1500   # Mathlib linter.style.longFile default
MAX_LINE_DEFAULT = 100    # Mathlib linter.style.longLine
MAX_DECL_DEFAULT = 75     # Spectra house guideline (not a Mathlib rule)
ALL_CHECKS = ("file", "line", "decl")

# Mathlib's longLine linter (Style.lean `isImport`) exempts URLs and import lines,
# since neither can be wrapped. We mirror that so the counts match.
_IMPORT_PREFIXES = ("import ", "public import ", "meta import ",
                    "public meta import ", "import all ", "meta import all ")


def is_long_line(line: str, limit: int) -> bool:
    return (len(line) > limit and "http" not in line
            and not line.startswith(_IMPORT_PREFIXES))


# --------------------------------------------------------------------------- #
# Repo layout
# --------------------------------------------------------------------------- #
def find_repo_root() -> Path:
    here = Path(__file__).resolve()
    for cand in (here, *here.parents):
        if (cand / "lakefile.lean").is_file():
            return cand
    raise RuntimeError("could not locate repo root (no lakefile.lean found)")


def iter_lean_files(repo_root: Path):
    for path in sorted((repo_root / LIB_NAME).rglob("*.lean")):
        if ".lake" not in path.parts:
            yield path


def module_of(path: Path, repo_root: Path) -> str:
    rel = path.resolve().relative_to(repo_root.resolve())
    return ".".join(rel.with_suffix("").parts)


# --------------------------------------------------------------------------- #
# Comment-aware scan (keywords inside comments/strings are blanked to spaces,
# newlines preserved so line numbers stay exact). Ported from @Meta tooling.
# --------------------------------------------------------------------------- #
def blank_comments(text: str) -> str:
    out = []
    n = len(text)
    i = depth = 0
    in_line = in_str = esc = False
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_line:
            out.append("\n" if c == "\n" else " ")
            if c == "\n":
                in_line = False
            i += 1
        elif depth > 0:
            if c == "/" and nxt == "-":
                depth += 1; out.append("  "); i += 2
            elif c == "-" and nxt == "/":
                depth -= 1; out.append("  "); i += 2
            else:
                out.append("\n" if c == "\n" else " "); i += 1
        elif in_str:
            out.append(c)
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                in_str = False
            i += 1
        elif c == "-" and nxt == "-":
            in_line = True; out.append("  "); i += 2
        elif c == "/" and nxt == "-":
            depth = 1; out.append("  "); i += 2
        elif c == '"':
            in_str = True; out.append(c); i += 1
        else:
            out.append(c); i += 1
    return "".join(out)


_MODIFIERS = r"(?:private|protected|noncomputable|scoped|local|partial|unsafe|nonrec)"
_KINDS = ("theorem", "lemma", "def", "abbrev", "instance", "structure",
          "class", "inductive", "opaque", "axiom", "example")
_DECL_RE = re.compile(
    r"^\s*(?:(?:" + _MODIFIERS + r"|@\[[^\]]*\])\s+)*"
    r"(" + "|".join(_KINDS) + r")\b\s*([^\s:({\[⦃⟨]*)")
_BOUNDARY_RE = re.compile(
    r"^\s*(?:(?:end|namespace|section|open|variable|universe|set_option|attribute|"
    r"notation|macro|macro_rules|syntax|elab|declare_syntax_cat|run_cmd|initialize)\b|#)")


def total_lines(text: str) -> int:
    return text.count("\n") + (1 if text and not text.endswith("\n") else 0)


def declaration_violations(module, code_lines, max_decl):
    """Declarations whose span (keyword .. last body code line) exceeds max_decl."""
    starts = [i for i, ln in enumerate(code_lines) if _DECL_RE.match(ln)]  # 0-based
    n = len(code_lines)
    out = []
    for idx, s in enumerate(starts):
        nxt = starts[idx + 1] if idx + 1 < len(starts) else n
        boundary = nxt
        k = s + 1
        while k < nxt:
            if _BOUNDARY_RE.match(code_lines[k]):
                boundary = k
                break
            k += 1
        last = s
        for k in range(s, boundary):
            if code_lines[k].strip():
                last = k
        span = last - s + 1
        if span > max_decl:
            m = _DECL_RE.match(code_lines[s])
            name = (m.group(2) or "_") if m else "_"
            out.append({"check": "decl", "module": module, "name": name,
                        "line": s + 1, "value": span})
    return out


def scan(repo_root, max_file, max_line, max_decl, checks):
    violations = []
    n_files = n_decls = 0
    for path in iter_lean_files(repo_root):
        module = module_of(path, repo_root)
        text = path.read_text(encoding="utf-8", errors="replace")
        n_files += 1

        if "file" in checks:
            tl = total_lines(text)
            if tl > max_file:
                violations.append({"check": "file", "module": module,
                                   "name": None, "value": tl})

        if "line" in checks:
            long = sum(1 for ln in text.splitlines() if is_long_line(ln, max_line))
            if long:
                violations.append({"check": "line", "module": module,
                                   "name": None, "value": long})

        if "decl" in checks:
            code_lines = blank_comments(text).splitlines()
            n_decls += sum(1 for ln in code_lines if _DECL_RE.match(ln))
            violations.extend(declaration_violations(module, code_lines, max_decl))

    violations.sort(key=lambda v: (v["check"], -v["value"], v["module"]))
    return violations, {"files": n_files, "decls": n_decls}


# --------------------------------------------------------------------------- #
# Baseline
# --------------------------------------------------------------------------- #
def vkey(v):
    """Stable identity of a violation (independent of its value)."""
    return (v["check"], v["module"], v["name"] or "")


def load_baseline(path: Path):
    base = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        kind, value = parts[0], int(parts[-1])
        if kind == "decl":
            key = (kind, parts[1], parts[2])
        else:
            key = (kind, parts[1], "")
        base[key] = value
    return base


def write_baseline(path: Path, violations, cfg):
    lines = [
        "# Spectra length baseline — grandfathered over-budget items.",
        "# CI (check_lengths.py --strict --baseline this) fails only on NEW or",
        "# WORSENED entries, so the list can only shrink. Regenerate after",
        "# improvements with: python3 scripts/check_lengths.py --write-baseline " + path.name,
        f"# budgets: file={cfg['max_file']} line={cfg['max_line']} decl={cfg['max_decl']}",
    ]
    rows = []
    for v in violations:
        if v["check"] == "decl":
            rows.append(f"decl {v['module']} {v['name']} {v['value']}")
        else:
            rows.append(f"{v['check']} {v['module']} {v['value']}")
    lines.extend(sorted(rows))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def ratchet(violations, baseline):
    """Split current violations against the baseline."""
    new, worse, ok = [], [], []
    for v in violations:
        b = baseline.get(vkey(v))
        if b is None:
            new.append(v)
        elif v["value"] > b:
            worse.append({**v, "baseline": b})
        else:
            ok.append(v)
    fixed = len(baseline) - len(ok) - len(worse)  # baseline entries no longer violating
    return new, worse, ok, max(fixed, 0)


# --------------------------------------------------------------------------- #
# Reporting
# --------------------------------------------------------------------------- #
def describe(v):
    loc = v["module"] + (f":{v['line']}  ({v['name']})" if v["check"] == "decl" else "")
    unit = {"file": "lines", "line": "long lines", "decl": "lines"}[v["check"]]
    extra = f"  (baseline {v['baseline']})" if "baseline" in v else ""
    return f"  {v['value']:>5} {unit:<11} {loc}{extra}"


def report(violations, totals, cfg, limit):
    print("=" * 70)
    print("  SPECTRA — LENGTH CHECK")
    print("=" * 70)
    print(f"  budgets: file ≤ {cfg['max_file']:,}  |  line ≤ {cfg['max_line']}  |  "
          f"decl ≤ {cfg['max_decl']}   (decl = house guideline, not Mathlib)")
    by = {c: [v for v in violations if v["check"] == c] for c in ALL_CHECKS}
    print(f"  files over budget ......... {len(by['file']):>5,} / {totals['files']:,}")
    print(f"  long lines (files w/ any) . {len(by['line']):>5,} / {totals['files']:,}")
    print(f"  declarations over budget .. {len(by['decl']):>5,} / {totals['decls']:,}")
    for c, title in (("file", "Files over budget"),
                     ("line", "Files with >budget-width lines"),
                     ("decl", "Declarations over budget")):
        rows = by[c]
        if not rows:
            continue
        print(f"\n  {title}  ({len(rows)})")
        print("  " + "-" * 64)
        shown = rows if limit == 0 else rows[:limit]
        for v in shown:
            print(describe(v))
        if len(rows) > len(shown):
            print(f"  … and {len(rows) - len(shown):,} more  (use --limit 0)")
    print()


def main():
    ap = argparse.ArgumentParser(description="Length checker + baseline ratchet for Spectra.")
    ap.add_argument("--max-file", type=int, default=MAX_FILE_DEFAULT)
    ap.add_argument("--max-line", type=int, default=MAX_LINE_DEFAULT)
    ap.add_argument("--max-decl", type=int, default=MAX_DECL_DEFAULT)
    ap.add_argument("--checks", default=",".join(ALL_CHECKS),
                    help="comma list of checks to run: file,line,decl")
    ap.add_argument("--baseline", type=Path, help="compare against this baseline (ratchet)")
    ap.add_argument("--write-baseline", type=Path, help="snapshot current violations and exit")
    ap.add_argument("--limit", type=int, default=30, help="rows per section, 0 = all")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--strict", action="store_true", help="exit 1 on violations")
    args = ap.parse_args()

    checks = tuple(c for c in args.checks.split(",") if c in ALL_CHECKS)
    cfg = {"max_file": args.max_file, "max_line": args.max_line, "max_decl": args.max_decl}
    repo_root = find_repo_root()
    violations, totals = scan(repo_root, args.max_file, args.max_line, args.max_decl, checks)

    if args.write_baseline:
        write_baseline(args.write_baseline, violations, cfg)
        print(f"wrote baseline: {args.write_baseline}  ({len(violations):,} entries)")
        return

    if args.baseline:
        baseline = load_baseline(args.baseline)
        new, worse, ok, fixed = ratchet(violations, baseline)
        if args.json:
            print(json.dumps({"new": new, "worse": worse,
                              "grandfathered": len(ok), "fixed": fixed}, indent=2))
        else:
            print(f"baseline: {len(ok):,} grandfathered, {fixed:,} improved, "
                  f"{len(new):,} new, {len(worse):,} worsened")
            for v in new:
                print("  NEW    " + describe(v).strip())
            for v in worse:
                print("  WORSE  " + describe(v).strip())
            if fixed:
                print(f"  (↓ {fixed:,} baseline entries no longer violate — "
                      f"run --write-baseline to lock that in)")
        if args.strict and (new or worse):
            raise SystemExit(1)
        return

    if args.json:
        print(json.dumps({"violations": violations, "totals": totals}, indent=2))
    else:
        report(violations, totals, cfg, args.limit)
    if args.strict and violations:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

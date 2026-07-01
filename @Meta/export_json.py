#!/usr/bin/env python3
"""Export a comprehensive JSON snapshot of the Spectra library for the HTML docs.

Pure stdlib. Reuses _spectra_meta.py for parsing. Writes to stdout (or --out PATH).
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

import _spectra_meta as M


def git(repo: Path, *args: str) -> str:
    try:
        return subprocess.run(
            ["git", "-C", str(repo), *args],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    except Exception:
        return ""


def module_summary(src: M.LeanSource) -> str:
    """First sentence-ish of the first /-! module doc, cleaned for display."""
    text = src.text
    # find first /-! ... -/
    m = re.search(r"/-!(.*?)-/", text, re.DOTALL)
    if not m:
        return ""
    body = m.group(1)
    # drop leading markdown header line(s) like "# Title"
    lines = [ln.rstrip() for ln in body.splitlines()]
    # collect first non-empty, non-header paragraph
    para: list[str] = []
    seen_text = False
    for ln in lines:
        s = ln.strip()
        if not s:
            if seen_text:
                break
            continue
        if s.startswith("#"):
            continue
        seen_text = True
        para.append(s)
    out = " ".join(para)
    out = re.sub(r"\s+", " ", out).strip()
    return out[:320]


def module_title(src: M.LeanSource) -> str:
    """The first markdown '# ...' header inside the first /-! block, if any."""
    m = re.search(r"/-!(.*?)-/", src.text, re.DOTALL)
    if not m:
        return ""
    for ln in m.group(1).splitlines():
        s = ln.strip()
        if s.startswith("# "):
            return s[2:].strip()
    return ""


def count_sorries(src: M.LeanSource) -> int:
    return len(re.findall(r"\bsorry\b", src.code))


def parse_axiom_gate(repo: Path):
    """Parse AxiomCheck.lean → list of {section, theorems:[...]} (active lines only)."""
    p = repo / "AxiomCheck.lean"
    if not p.is_file():
        return []
    sections = []
    cur = {"section": "Verified results", "theorems": []}
    for raw in p.read_text(encoding="utf-8").splitlines():
        ln = raw.strip()
        hdr = re.match(r"/-![#\s]*(.+?)\s*-/", ln)
        if hdr:
            if cur["theorems"]:
                sections.append(cur)
            cur = {"section": hdr.group(1).strip(), "theorems": []}
            continue
        m = re.match(r"assert_no_sorry\s+([\w.]+)", ln)
        if m and not ln.startswith("--"):
            cur["theorems"].append(m.group(1))
    if cur["theorems"]:
        sections.append(cur)
    return sections


def main() -> int:
    repo = M.find_repo_root()
    # Exclude experimental scratch files: they are not imported into `Spectra.lean`
    # (not part of the built/gated library) and carry work-in-progress `sorry`s. The
    # docs describe the actual library, which is sorry-free.
    sources = [s for s in M.load_all(repo)
               if "Scratch" not in M.module_of_path(s.path, repo).split(".")]

    files = []
    area_agg = defaultdict(lambda: {"files": 0, "lines": 0, "code": 0,
                                    "comments": 0, "decls": 0, "sorries": 0,
                                    "documented": 0, "documentable": 0})
    kind_counts = Counter()
    edges = []
    indeg = Counter()
    total = {"files": 0, "lines": 0, "code": 0, "comments": 0, "blank": 0,
             "decls": 0, "sorries": 0, "documented": 0, "documentable": 0}

    module_of = {}
    for src in sources:
        mod = M.module_of_path(src.path, repo)
        module_of[src.path] = mod

    for src in sources:
        mod = module_of[src.path]
        area = M.top_area(mod)
        decls = src.declarations()
        documentable = [d for d in decls if d.kind not in ("example", "instance")]
        documented = [d for d in documentable if d.documented]
        sorries = count_sorries(src)
        for d in decls:
            kind_counts[d.kind] += 1
        internal_imports = src.imports()
        for imp in internal_imports:
            edges.append({"source": mod, "target": imp})
            indeg[imp] += 1

        rec = {
            "module": mod,
            "path": M.rel(src.path, repo),
            "area": area,
            "lines": src.total_lines,
            "code": src.code_lines,
            "comments": src.comment_lines,
            "blank": src.blank_lines,
            "decls": len(decls),
            "theorems": sum(1 for d in decls if d.kind in ("theorem", "lemma")),
            "defs": sum(1 for d in decls if d.kind in ("def", "abbrev")),
            "sorries": sorries,
            "doc_documented": len(documented),
            "doc_documentable": len(documentable),
            "title": module_title(src),
            "summary": module_summary(src),
            "imports": internal_imports,
        }
        files.append(rec)

        a = area_agg[area]
        a["files"] += 1
        a["lines"] += src.total_lines
        a["code"] += src.code_lines
        a["comments"] += src.comment_lines
        a["decls"] += len(decls)
        a["sorries"] += sorries
        a["documented"] += len(documented)
        a["documentable"] += len(documentable)

        total["files"] += 1
        total["lines"] += src.total_lines
        total["code"] += src.code_lines
        total["comments"] += src.comment_lines
        total["blank"] += src.blank_lines
        total["decls"] += len(decls)
        total["sorries"] += sorries
        total["documented"] += len(documented)
        total["documentable"] += len(documentable)

    areas = []
    for name, a in sorted(area_agg.items(), key=lambda kv: -kv[1]["lines"]):
        doc_pct = round(100 * a["documented"] / a["documentable"], 1) if a["documentable"] else 100.0
        areas.append({
            "name": name,
            "files": a["files"],
            "lines": a["lines"],
            "code": a["code"],
            "decls": a["decls"],
            "sorries": a["sorries"],
            "doc_pct": doc_pct,
        })

    # in-degree ranking (most depended-upon modules)
    rank = [{"module": m, "indeg": d} for m, d in indeg.most_common(25)]

    # sorries detail
    sorry_detail = []
    for src in sources:
        lines = src.text.splitlines()
        code_lines = src.code.splitlines()
        for i, cl in enumerate(code_lines):
            if re.search(r"\bsorry\b", cl):
                ctx = lines[i].strip() if i < len(lines) else ""
                sorry_detail.append({
                    "path": M.rel(src.path, repo),
                    "module": module_of[src.path],
                    "area": M.top_area(module_of[src.path]),
                    "line": i + 1,
                    "context": ctx[:160],
                })

    doc_pct = round(100 * total["documented"] / total["documentable"], 1) if total["documentable"] else 100.0

    # git log
    log_raw = git(repo, "log", "-25", "--pretty=format:%h\x1f%an\x1f%ar\x1f%s")
    commits = []
    for ln in log_raw.splitlines():
        parts = ln.split("\x1f")
        if len(parts) == 4:
            commits.append({"hash": parts[0], "author": parts[1],
                            "when": parts[2], "subject": parts[3]})

    branch = git(repo, "rev-parse", "--abbrev-ref", "HEAD")

    data = {
        "generated": git(repo, "log", "-1", "--pretty=format:%ci") or "",
        "branch": branch,
        "totals": {**total, "blank": total["blank"], "doc_pct": doc_pct,
                   "axioms": 0},
        "kinds": dict(kind_counts.most_common()),
        "areas": areas,
        "files": files,
        "edges": edges,
        "rank": rank,
        "sorries": sorry_detail,
        "axiom_gate": parse_axiom_gate(repo),
        "commits": commits,
    }

    out = json.dumps(data, indent=None, separators=(",", ":"))
    wrote = False
    if "--out" in sys.argv:
        target = sys.argv[sys.argv.index("--out") + 1]
        Path(target).write_text(out, encoding="utf-8")
        print(f"wrote {len(out):,} bytes → {target}", file=sys.stderr)
        wrote = True
    if "--js" in sys.argv:
        target = sys.argv[sys.argv.index("--js") + 1]
        Path(target).write_text("window.SPECTRA = " + out + ";\n", encoding="utf-8")
        print(f"wrote {len(out):,} bytes → {target} (JS global)", file=sys.stderr)
        wrote = True
    if not wrote:
        sys.stdout.write(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

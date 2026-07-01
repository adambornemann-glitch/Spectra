#!/usr/bin/env python3
"""Declaration / symbol index for Spectra  ->  docs/spectra-symbols.{json,tsv}

The machine "API" of the library: for every citable declaration this emits its FULLY-QUALIFIED name
(namespace-aware), kind, type signature, the module + source path it lives in, whether its body contains
`sorry`, and whether it carries a doc-string.

Why this exists: the module path and the declaration's namespace DIVERGE in Spectra (e.g. module
`Spectra.SpectralTheory.ResolventForm` -> name `Spectra.QuantumMechanics.SpectralTheory.spectralTheorem`),
so knowing the file is not enough to cite or reuse a result. A tool or AI can look a result up here by
name or signature instead of grepping blind.

Comment-aware: reuses @Meta/_spectra_meta, so keywords inside comments/docstrings are ignored. It is a
parser, not an elaborator, so signatures are a faithful estimate (cut at the first `:=`/`where`).

    python3 @Meta/symbol_index.py            # writes docs/spectra-symbols.json + .tsv

Run it after editing the library (it is deterministic; no model).
"""
from __future__ import annotations
import json, re
from collections import Counter
import _spectra_meta as M

CITABLE = {"theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "opaque", "instance", "axiom"}
IGNORED_AREAS = {"Scratch"}
NS_RE = re.compile(r"^\s*namespace\s+([\w.]+)")
SEC_RE = re.compile(r"^\s*section\b\s*([\w.']*)")
END_RE = re.compile(r"^\s*end\b\s*([\w.']*)")

def tracked_module(module):
    return M.top_area(module) not in IGNORED_AREAS

def prefixes_per_line(code_lines):
    """active namespace dotted-prefix in effect *at* each line (before that line opens/closes a scope)."""
    stack, out = [], []
    for ln in code_lines:
        out.append(".".join(n for k, n in stack if k == "ns"))
        m = NS_RE.match(ln)
        if m:
            stack.append(("ns", m.group(1))); continue
        if END_RE.match(ln):
            if stack: stack.pop()
            continue
        if SEC_RE.match(ln):
            stack.append(("sec", SEC_RE.match(ln).group(1) or "")); continue
    return out

def signature(code_lines, start, stop):
    buf = []
    for j in range(start, min(stop, start + 25)):
        buf.append(code_lines[j].strip())
        joined = re.sub(r"\s+", " ", " ".join(buf)).strip()
        for cut in (" :=", ":=", " where ", " where", "≔"):
            k = joined.find(cut)
            if k != -1:
                return joined[:k].strip()
    return re.sub(r"\s+", " ", " ".join(buf)).strip()

def main():
    repo = M.find_repo_root()
    all_sources = M.load_all(repo)
    sources = [s for s in all_sources if tracked_module(M.module_of_path(s.path, repo))]
    ignored = len(all_sources) - len(sources)
    symbols, by_kind = [], Counter()
    for s in sources:
        module = M.module_of_path(s.path, repo)
        area = M.top_area(module)
        src = M.rel(s.path, repo)
        code_lines = s.code.splitlines()
        pre = prefixes_per_line(code_lines)
        decls = [d for d in s.declarations() if d.kind in CITABLE and d.name != "_"]
        for i, d in enumerate(decls):
            start = d.line - 1
            stop = (decls[i + 1].line - 1) if i + 1 < len(decls) else len(code_lines)
            prefix = pre[start] if 0 <= start < len(pre) else ""
            qname = f"{prefix}.{d.name}" if prefix else d.name
            body = "\n".join(code_lines[start:stop])
            has_sorry = re.search(r"\bsorry\b", body) is not None
            by_kind[d.kind] += 1
            symbols.append({
                "name": qname,
                "kind": d.kind,
                "signature": signature(code_lines, start, stop),
                "module": module,
                "area": area,
                "src": src,
                "line": d.line,
                "sorry": has_sorry,
                "documented": d.documented,
            })
    symbols.sort(key=lambda x: x["name"])
    docs = repo / "docs"; docs.mkdir(exist_ok=True)
    out = {
        "meta": {
            "library": "Spectra",
            "generated_by": "@Meta/symbol_index.py",
            "note": "Names are fully qualified (namespace-aware). Source of truth is the .lean; verify with `lake build`.",
            "total": len(symbols),
            "by_kind": dict(sorted(by_kind.items(), key=lambda kv: -kv[1])),
            "with_sorry": sum(1 for x in symbols if x["sorry"]),
            "source_scope": "tracked",
            "ignored_areas": sorted(IGNORED_AREAS),
            "ignored_files": ignored,
        },
        "symbols": symbols,
    }
    (docs / "spectra-symbols.json").write_text(json.dumps(out, indent=1))
    # grep-friendly flat index: name<TAB>kind<TAB>module<TAB>sorry<TAB>signature
    lines = [f'{x["name"]}\t{x["kind"]}\t{x["module"]}\t{"sorry" if x["sorry"] else "ok"}\t{x["signature"]}'
             for x in symbols]
    (docs / "spectra-symbols.tsv").write_text("\n".join(lines) + "\n")
    print(f"docs/spectra-symbols.json + .tsv: {len(symbols)} tracked declarations, "
          f"{out['meta']['with_sorry']} contain sorry ({ignored} ignored Scratch files)")
    print("by kind:", dict(by_kind))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

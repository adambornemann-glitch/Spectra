#!/usr/bin/env python3
"""
library_signatures.py — Declaration signature extractor for a Lean 4 library.

Usage:
    python3 library_signatures.py /path/to/Spectra
    python3 library_signatures.py Spectra/Uncertainty -o signatures.md
    python3 library_signatures.py Spectra/Uncertainty --kind theorem lemma -o theorems.md
    python3 library_signatures.py Spectra/Uncertainty --sorry-only -o gaps.md
    python3 library_signatures.py Spectra/Uncertainty --format txt -o signatures.txt

Finds every def/lemma/theorem/structure/class/instance/axiom/abbrev/inductive
declaration, extracts its name and type signature (trimming proof bodies),
detects sorry, and reports them grouped by directory with summary statistics.
"""

import argparse
import os
import re
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Optional
from collections import defaultdict

# ── Skip rules (same as lean_axioms.py) ─────────────────────────────────────

SKIP_DIRS = {
    ".lake", ".git", "build", "lake-packages", "lake-env",
    "__pycache__", "node_modules", ".elan",
}

SKIP_EXTENSIONS = {
    ".ilean", ".olean", ".trace", ".log", ".json", ".toml",
    ".yaml", ".yml", ".lock", ".hash", ".dep",
}

ALL_KINDS = [
    "theorem", "lemma", "def", "axiom", "structure", "class",
    "instance", "abbrev", "inductive", "opaque",
]

# ── Block comment stripping (handles nesting) ───────────────────────────────

def strip_block_comments(source: str) -> str:
    """Remove all /- ... -/ block comments, respecting nesting."""
    result = []
    i = 0
    depth = 0
    n = len(source)
    while i < n:
        if i + 1 < n and source[i] == "/" and source[i + 1] == "-":
            depth += 1
            i += 2
        elif i + 1 < n and source[i] == "-" and source[i + 1] == "/" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            result.append(source[i])
            i += 1
        else:
            # Preserve newlines for line-number correspondence
            if source[i] == "\n":
                result.append("\n")
            i += 1
    return "".join(result)


# ── Declaration extraction ──────────────────────────────────────────────────

MODIFIERS = r"(?:noncomputable\s+|private\s+|protected\s+|unsafe\s+|partial\s+)*"
KEYWORDS = "|".join(ALL_KINDS)

DECL_RE = re.compile(
    rf"^\s*{MODIFIERS}({KEYWORDS})\s+(\S+)",
    re.MULTILINE,
)

# Fallback for anonymous instances: `instance :` or `instance [`
ANON_INSTANCE_RE = re.compile(
    rf"^\s*{MODIFIERS}instance\s*(?=[\[:({{])",
    re.MULTILINE,
)

# Patterns that signal a new top-level declaration (used as stop conditions)
DECL_START_RE = re.compile(
    rf"^\s*{MODIFIERS}({KEYWORDS})\s",
    re.MULTILINE,
)

NS_RE = re.compile(r"^\s*(namespace|end|section)\s")


@dataclass
class DeclInfo:
    kind: str           # theorem, lemma, def, structure, ...
    name: str           # The declaration identifier
    file: str           # Relative path
    line: int           # Line number in original source (1-indexed)
    signature: str      # Type signature (proof body trimmed)
    full_text: str      # Full collected text (for sorry detection)
    namespace: str      # Enclosing namespace
    has_sorry: bool     # Whether the body contains sorry


def strip_line_comment(line: str) -> str:
    """Remove trailing -- comments from a line."""
    idx = line.find("--")
    if idx >= 0:
        return line[:idx].rstrip()
    return line


def trim_to_signature(text: str, kind: str) -> str:
    """Remove proof body, keeping only the type signature.

    For structure/class/inductive, fields and constructors ARE the
    signature, so we keep everything.  For theorem/lemma/def/instance,
    we strip the proof body at the first body delimiter.

    Key insight: the FIRST `:=` in joined text is always the declaration
    body delimiter, never something inside the proof.
    """
    # Structures, classes, inductives: fields/constructors are API surface
    if kind in ("structure", "class", "inductive"):
        return text.strip()

    # Axioms and opaques have no body
    if kind in ("axiom", "opaque"):
        return text.strip()

    # For instances: `where` takes priority over `:=`
    if kind == "instance":
        m = re.search(r"\s+where\b", text)
        if m:
            return text[:m.start()].strip()

    # The first `:=` is the body delimiter
    m = re.search(r"\s*:=", text)
    if m:
        return text[:m.start()].strip()

    # Fallback: standalone `by` at end (rare: some tactic blocks)
    m = re.search(r"\s+by\s*$", text)
    if m:
        return text[:m.start()].strip()

    return text.strip()


def find_decls_in_file(filepath: Path, root: Path) -> List[DeclInfo]:
    """Extract all declarations from a single .lean file."""
    rel = str(filepath.relative_to(root))
    try:
        raw = filepath.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return []

    stripped = strip_block_comments(raw)
    stripped_lines = stripped.split("\n")

    # Namespace tracking
    current_namespaces: List[str] = []
    ns_open = re.compile(r"^\s*namespace\s+(\S+)")
    ns_end = re.compile(r"^\s*end\s+(\S+)")

    decls: List[DeclInfo] = []

    for line_idx, line in enumerate(stripped_lines):
        # Track namespaces
        m_open = ns_open.match(line)
        if m_open:
            current_namespaces.append(m_open.group(1))
            continue
        m_end = ns_end.match(line)
        if m_end:
            ns_name = m_end.group(1)
            for i in range(len(current_namespaces) - 1, -1, -1):
                if current_namespaces[i] == ns_name:
                    current_namespaces.pop(i)
                    break
            continue

        # Skip pure comment lines
        s = line.strip()
        if s.startswith("--"):
            continue

        # ── Match a declaration ──────────────────────────────────────────
        kind: Optional[str] = None
        name: Optional[str] = None

        m_decl = DECL_RE.match(line)
        if m_decl:
            kind = m_decl.group(1)
            name = m_decl.group(2)
            # Handle instance whose "name" is actually `:` or `[` or `(`
            if kind == "instance" and name and name[0] in ":([{":
                name = "(anonymous)"
        elif ANON_INSTANCE_RE.match(line):
            kind = "instance"
            name = "(anonymous)"

        if kind is None:
            continue

        # ── Collect continuation lines ───────────────────────────────────
        # Same strategy as lean_axioms.py: collect until blank line, next
        # top-level declaration, or namespace/section boundary.
        # Limit to 100 lines to avoid runaway collection in long proofs.

        first_line = strip_line_comment(stripped_lines[line_idx]).strip()
        sig_lines = [first_line] if first_line else []
        j = line_idx + 1
        collected = 0
        max_collect = 100

        # For structures/classes/inductives, blank lines between fields
        # are common (doc comments get stripped → blank lines remain).
        # We continue past blanks until we hit a real boundary.
        seen_where = "where" in first_line
        body_kind = kind in ("structure", "class", "inductive")

        while j < len(stripped_lines) and collected < max_collect:
            next_line = stripped_lines[j]
            next_stripped = next_line.strip()

            # Blank line
            if not next_stripped:
                if body_kind and seen_where:
                    j += 1
                    collected += 1
                    continue
                break

            # Pure comment line → skip but don't stop
            if next_stripped.startswith("--"):
                j += 1
                collected += 1
                continue

            # Next top-level declaration → stop
            if DECL_START_RE.match(next_line):
                break

            # Namespace/section boundary → stop
            if NS_RE.match(next_line):
                break

            cleaned = strip_line_comment(next_stripped)
            if cleaned:
                sig_lines.append(cleaned)
                if "where" in cleaned:
                    seen_where = True

            j += 1
            collected += 1

        full_text = " ".join(sig_lines)
        has_sorry = bool(re.search(r"\bsorry\b", full_text))
        signature = trim_to_signature(full_text, kind)

        # Truncate very long signatures
        if len(signature) > 500:
            signature = signature[:497] + "..."

        ns = ".".join(current_namespaces) if current_namespaces else "(root)"

        decls.append(DeclInfo(
            kind=kind,
            name=name,
            file=rel,
            line=line_idx + 1,
            signature=signature,
            full_text=full_text,
            namespace=ns,
            has_sorry=has_sorry,
        ))

    return decls


# ── Walk the tree ───────────────────────────────────────────────────────────

def walk_library(
    root: Path,
    kinds: Optional[List[str]] = None,
    sorry_only: bool = False,
) -> List[DeclInfo]:
    all_decls: List[DeclInfo] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [
            d for d in dirnames
            if d not in SKIP_DIRS and not d.startswith(".")
        ]
        for fname in sorted(filenames):
            fp = Path(dirpath) / fname
            if fp.suffix == ".lean":
                all_decls.extend(find_decls_in_file(fp, root))

    # Apply filters
    if kinds:
        all_decls = [d for d in all_decls if d.kind in kinds]
    if sorry_only:
        all_decls = [d for d in all_decls if d.has_sorry]

    all_decls.sort(key=lambda d: (d.file, d.line))
    return all_decls


# ── Grouping helpers ────────────────────────────────────────────────────────

def group_by_directory(decls: List[DeclInfo], depth: int = 2) -> Dict[str, List[DeclInfo]]:
    groups: Dict[str, List[DeclInfo]] = defaultdict(list)
    for d in decls:
        parts = Path(d.file).parts[:-1]
        key = "/".join(parts[:depth]) if parts else "(root)"
        groups[key].append(d)
    return dict(sorted(groups.items()))


def group_by_file(decls: List[DeclInfo]) -> Dict[str, List[DeclInfo]]:
    groups: Dict[str, List[DeclInfo]] = defaultdict(list)
    for d in decls:
        groups[d.file].append(d)
    return dict(sorted(groups.items()))


def group_by_namespace(decls: List[DeclInfo]) -> Dict[str, List[DeclInfo]]:
    groups: Dict[str, List[DeclInfo]] = defaultdict(list)
    for d in decls:
        groups[d.namespace].append(d)
    return dict(sorted(groups.items()))


def group_by_kind(decls: List[DeclInfo]) -> Dict[str, List[DeclInfo]]:
    groups: Dict[str, List[DeclInfo]] = defaultdict(list)
    for d in decls:
        groups[d.kind].append(d)
    return dict(sorted(groups.items()))


# ── Formatters ──────────────────────────────────────────────────────────────

KIND_ICON = {
    "theorem":   "thm",
    "lemma":     "lem",
    "def":       "def",
    "structure":  "str",
    "class":     "cls",
    "instance":  "ins",
    "axiom":     "axm",
    "abbrev":    "abv",
    "inductive": "ind",
    "opaque":    "opq",
}


def format_md(decls: List[DeclInfo], root: str) -> str:
    lines: List[str] = []
    w = lines.append

    lib_name = Path(root).name
    w(f"# Signature Map: `{lib_name}`\n")

    # ── Summary ──
    total = len(decls)
    sorry_count = sum(1 for d in decls if d.has_sorry)
    by_kind = group_by_kind(decls)
    kind_parts = []
    for k in ALL_KINDS:
        if k in by_kind:
            n = len(by_kind[k])
            kind_parts.append(f"{n} {k}{'s' if n != 1 else ''}")
    w(f"**Total declarations:** {total}")
    w(f"**By kind:** {', '.join(kind_parts)}")
    w(f"**Sorry count:** {sorry_count}\n")

    # ── Summary by kind ──
    w("## Summary by Kind\n")
    w("| Kind | Count | Sorry |")
    w("|------|------:|------:|")
    for k in ALL_KINDS:
        if k in by_kind:
            ds = by_kind[k]
            sc = sum(1 for d in ds if d.has_sorry)
            tag = KIND_ICON.get(k, "")
            sorry_str = f"**{sc}**" if sc > 0 else "0"
            w(f"| `{k}` | {len(ds)} | {sorry_str} |")
    w("")

    # ── By directory ──
    by_dir = group_by_directory(decls, depth=2)
    w("## Declarations by Directory\n")
    w("| Directory | Count | Sorry |")
    w("|-----------|------:|------:|")
    for d, ds in by_dir.items():
        sc = sum(1 for x in ds if x.has_sorry)
        sorry_str = f"**{sc}**" if sc > 0 else "0"
        w(f"| `{d}` | {len(ds)} | {sorry_str} |")
    w("")

    # ── Full catalogue ──
    w("## Full Catalogue\n")
    by_file = group_by_file(decls)
    current_dir = None
    for filepath, file_decls in by_file.items():
        d = str(Path(filepath).parent)
        if d != current_dir:
            current_dir = d
            dir_label = d if d != "." else "(root)"
            w(f"### `{dir_label}/`\n")

        sc = sum(1 for x in file_decls if x.has_sorry)
        sorry_note = f", {sc} sorry" if sc > 0 else ""
        w(f"#### `{Path(filepath).name}` ({len(file_decls)} decl{sorry_note})\n")

        # One lean block per file — all signatures, metadata as comments
        w("```lean")
        for i, decl in enumerate(file_decls):
            tag = KIND_ICON.get(decl.kind, decl.kind)
            sorry_mark = "  ⚠ sorry" if decl.has_sorry else ""
            ns_parts = []
            if decl.namespace != "(root)":
                ns_parts.append(f"ns: {decl.namespace}")
            meta = f"  -- [{tag}] L{decl.line}{sorry_mark}"
            if ns_parts:
                meta += f"  {ns_parts[0]}"
            w(meta)
            w(decl.signature)
            # Blank line between declarations, but not after the last one
            if i < len(file_decls) - 1:
                w("")
        w("```\n")

    # ── Sorry inventory ──
    sorry_decls = [d for d in decls if d.has_sorry]
    if sorry_decls:
        w("## Sorry Inventory\n")
        w(f"**{len(sorry_decls)} declaration(s) contain `sorry`:**\n")
        w("| # | Kind | Declaration | File | Line |")
        w("|--:|------|-------------|------|-----:|")
        for i, sd in enumerate(sorry_decls, 1):
            w(f"| {i} | `{sd.kind}` | `{sd.name}` | `{sd.file}` | {sd.line} |")
        w("")

    # ── By namespace ──
    by_ns = group_by_namespace(decls)
    w("## Declarations by Namespace\n")
    w("| Namespace | Count | Declarations |")
    w("|-----------|------:|--------------|")
    for ns, ds in by_ns.items():
        names = ", ".join(f"`{d.name}`" for d in ds[:10])
        if len(ds) > 10:
            names += f", ... (+{len(ds) - 10} more)"
        w(f"| `{ns}` | {len(ds)} | {names} |")
    w("")

    return "\n".join(lines)


def format_txt(decls: List[DeclInfo], root: str) -> str:
    lines: List[str] = []
    w = lines.append

    lib_name = Path(root).name
    w(f"SIGNATURE MAP: {lib_name}")
    total = len(decls)
    sorry_count = sum(1 for d in decls if d.has_sorry)
    w(f"Total declarations: {total}")
    w(f"Sorry count: {sorry_count}")
    w("=" * 72)
    w("")

    # ── By kind ──
    by_kind = group_by_kind(decls)
    w("BY KIND")
    w("-" * 40)
    for k in ALL_KINDS:
        if k in by_kind:
            ds = by_kind[k]
            sc = sum(1 for d in ds if d.has_sorry)
            sorry_str = f"  ({sc} sorry)" if sc > 0 else ""
            w(f"  {k:<15s} {len(ds):>4d}{sorry_str}")
    w("")

    # ── By file ──
    by_file = group_by_file(decls)
    w("BY FILE")
    w("-" * 72)
    for f, ds in by_file.items():
        sc = sum(1 for d in ds if d.has_sorry)
        sorry_str = f", {sc} sorry" if sc > 0 else ""
        w(f"  {f}  ({len(ds)}{sorry_str})")
        for d in ds:
            sorry_mark = " [SORRY]" if d.has_sorry else ""
            w(f"    L{d.line:<5d} [{d.kind:<9s}] {d.name}{sorry_mark}")
    w("")

    # ── Full catalogue ──
    w("FULL CATALOGUE")
    w("-" * 72)
    current_dir = None
    for d in decls:
        dirp = str(Path(d.file).parent)
        if dirp != current_dir:
            current_dir = dirp
            dir_label = dirp if dirp != "." else "(root)"
            w(f"\n  [{dir_label}/]")
            w("")

        sorry_mark = " [SORRY]" if d.has_sorry else ""
        w(f"  [{d.kind}] {d.name}{sorry_mark}")
        w(f"    File: {d.file}:{d.line}")
        w(f"    Namespace: {d.namespace}")
        sig = d.signature
        if len(sig) > 200:
            sig = sig[:197] + "..."
        w(f"    Sig:  {sig}")
        w("")

    # ── Sorry inventory ──
    sorry_decls = [d for d in decls if d.has_sorry]
    if sorry_decls:
        w("SORRY INVENTORY")
        w("-" * 72)
        for i, sd in enumerate(sorry_decls, 1):
            w(f"  {i}. [{sd.kind}] {sd.name}")
            w(f"     {sd.file}:{sd.line}")
        w("")

    return "\n".join(lines)


# ── Main ────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Extract declaration signatures from a Lean 4 library.",
        epilog=(
            "Examples:\n"
            "  python3 lean_signatures.py ./LogosLibrary\n"
            "  python3 lean_signatures.py LogosLibrary --kind theorem lemma\n"
            "  python3 lean_signatures.py LogosLibrary --sorry-only -o gaps.md\n"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "root",
        help="Root directory of the Lean library",
    )
    parser.add_argument(
        "-o", "--output",
        default=None,
        help="Output file (default: signatures.md or .txt in parent dir)",
    )
    parser.add_argument(
        "--format",
        choices=["md", "txt"],
        default="md",
        help="Output format (default: md)",
    )
    parser.add_argument(
        "--kind",
        nargs="+",
        choices=ALL_KINDS,
        default=None,
        metavar="KIND",
        help=f"Filter by declaration kind (choices: {', '.join(ALL_KINDS)})",
    )
    parser.add_argument(
        "--sorry-only",
        action="store_true",
        help="Show only declarations containing sorry",
    )

    args = parser.parse_args()
    root = Path(args.root).resolve()

    if not root.is_dir():
        print(f"Error: {root} is not a directory.")
        return 1

    kind_label = ", ".join(args.kind) if args.kind else "all"
    print(f"Scanning {root} for declarations (kinds: {kind_label}) ...")
    decls = walk_library(root, kinds=args.kind, sorry_only=args.sorry_only)
    sorry_count = sum(1 for d in decls if d.has_sorry)
    print(f"Found {len(decls)} declarations ({sorry_count} with sorry).")

    if args.format == "md":
        report = format_md(decls, str(root))
        default_name = "signatures.md"
    else:
        report = format_txt(decls, str(root))
        default_name = "signatures.txt"

    outpath = Path(args.output) if args.output else (root.parent / default_name)
    outpath.write_text(report, encoding="utf-8")
    print(f"Report written to {outpath}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
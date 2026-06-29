"""Shared helpers for the Spectra @Meta tooling.

This module is imported by the other scripts in this directory. It knows how to

  * locate the repository root (the directory containing ``lakefile.lean``),
  * enumerate the library's ``.lean`` source files,
  * translate between module names (``Spectra.KMS.ImaginaryTime``) and file
    paths, and
  * parse a Lean source into a *comment-blanked* form so that downstream tools
    can reason about real code without tripping over keywords that appear inside
    comments or doc-strings.

Pure standard library, no third-party dependencies -- every script here runs
with a bare ``python3``.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterator

# The Lean library is named "Spectra" and its sources live in a top-level
# directory of the same name next to ``lakefile.lean``.
LIB_NAME = "Spectra"


# --------------------------------------------------------------------------- #
# Repository layout
# --------------------------------------------------------------------------- #
def find_repo_root(start: Path | None = None) -> Path:
    """Walk upward from *start* (default: this file) to the directory that
    contains ``lakefile.lean``. Raises ``RuntimeError`` if none is found."""
    here = (start or Path(__file__)).resolve()
    for candidate in (here, *here.parents):
        if (candidate / "lakefile.lean").is_file():
            return candidate
    raise RuntimeError(
        "could not locate the Spectra repo root (no lakefile.lean found "
        f"walking up from {here})"
    )


def source_dir(repo_root: Path) -> Path:
    """The directory holding the library's ``.lean`` files."""
    return repo_root / LIB_NAME


def aggregator_path(repo_root: Path) -> Path:
    """The root ``Spectra.lean`` file that ``import``s every module."""
    return repo_root / f"{LIB_NAME}.lean"


def iter_lean_files(repo_root: Path) -> Iterator[Path]:
    """Yield every ``.lean`` source file under the library, in sorted order.
    The build cache (``.lake``) is never inside ``source_dir`` so no filtering
    is required, but we guard against it anyway."""
    src = source_dir(repo_root)
    for path in sorted(src.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        yield path


# --------------------------------------------------------------------------- #
# Module name <-> path
# --------------------------------------------------------------------------- #
def module_of_path(path: Path, repo_root: Path) -> str:
    """``<root>/Spectra/KMS/ImaginaryTime.lean`` -> ``Spectra.KMS.ImaginaryTime``."""
    rel = path.resolve().relative_to(repo_root.resolve())
    return ".".join(rel.with_suffix("").parts)


def path_of_module(module: str, repo_root: Path) -> Path:
    """``Spectra.KMS.ImaginaryTime`` -> ``<root>/Spectra/KMS/ImaginaryTime.lean``."""
    return repo_root / (Path(*module.split(".")).with_suffix(".lean"))


def top_area(module: str) -> str:
    """The second component of a module name -- the broad subject area, e.g.
    ``Spectra.KMS.ImaginaryTime`` -> ``KMS``. Falls back to the whole name."""
    parts = module.split(".")
    return parts[1] if len(parts) >= 2 else module


# --------------------------------------------------------------------------- #
# Lean source parsing
# --------------------------------------------------------------------------- #
# Leading modifiers / attributes that may sit in front of a declaration keyword.
_MODIFIERS = r"(?:private|protected|noncomputable|scoped|local|partial|unsafe|nonrec)"
_DECL_KINDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "structure",
    "class",
    "inductive",
    "opaque",
    "axiom",
    "example",
)
_DECL_RE = re.compile(
    r"^\s*"
    r"(?:(?:" + _MODIFIERS + r"|@\[[^\]]*\])\s+)*"  # modifiers / inline attrs
    r"(" + "|".join(_DECL_KINDS) + r")\b"           # 1: kind
    r"\s*([^\s:({\[⦃⟨]*)"                            # 2: name (may be empty)
)


@dataclass
class Declaration:
    kind: str
    name: str
    line: int            # 1-based line of the declaration keyword
    documented: bool     # immediately preceded by a `/-- ... -/` doc comment


@dataclass
class LeanSource:
    """A parsed Lean file. ``code`` is the original text with every comment
    replaced by spaces (newlines preserved, so line numbers are exact)."""

    path: Path
    text: str
    code: str
    doc_ranges: list[tuple[int, int]] = field(default_factory=list)   # /-- ... -/
    module_doc_ranges: list[tuple[int, int]] = field(default_factory=list)  # /-! ... -/

    # -- derived views ----------------------------------------------------- #
    @property
    def total_lines(self) -> int:
        return self.text.count("\n") + (1 if self.text and not self.text.endswith("\n") else 0)

    @property
    def code_lines(self) -> int:
        """Lines that contain at least one non-whitespace character of real code."""
        return sum(1 for ln in self.code.splitlines() if ln.strip())

    @property
    def blank_lines(self) -> int:
        return sum(1 for ln in self.text.splitlines() if not ln.strip())

    @property
    def comment_lines(self) -> int:
        """Lines that have text but whose real-code projection is blank."""
        orig = self.text.splitlines()
        code = self.code.splitlines()
        n = 0
        for o, c in zip(orig, code):
            if o.strip() and not c.strip():
                n += 1
        return n

    def imports(self) -> list[str]:
        """Internal ``import Spectra.*`` module names (comments ignored)."""
        out = []
        for ln in self.code.splitlines():
            m = re.match(r"\s*import\s+(" + re.escape(LIB_NAME) + r"\.[\w.]+)", ln)
            if m:
                out.append(m.group(1))
        return out

    def all_imports(self) -> list[str]:
        """Every ``import`` (Mathlib, Spectra, ...) -- comments ignored."""
        out = []
        for ln in self.code.splitlines():
            m = re.match(r"\s*import\s+([\w.]+)", ln)
            if m:
                out.append(m.group(1))
        return out

    def declarations(self) -> list[Declaration]:
        out: list[Declaration] = []
        orig = self.text.splitlines()
        code = self.code.splitlines()
        doc_ends = {e for _, e in self.doc_ranges}
        for idx, cline in enumerate(code):
            m = _DECL_RE.match(cline)
            if not m:
                continue
            kind, name = m.group(1), m.group(2) or "_"
            lineno = idx + 1
            out.append(
                Declaration(kind, name, lineno, _is_documented(lineno, orig, doc_ends))
            )
        return out


def _is_documented(lineno: int, orig_lines: list[str], doc_ends: set[int]) -> bool:
    """A declaration on 1-based ``lineno`` is documented when, skipping blank
    and attribute-only lines above it, the first content line is the closing
    line of a ``/-- ... -/`` doc comment."""
    j = lineno - 1  # 1-based line directly above
    while j >= 1:
        stripped = orig_lines[j - 1].strip()
        if not stripped or stripped.startswith("@["):
            j -= 1
            continue
        return j in doc_ends
    return False


def _blank_comments(text: str) -> tuple[str, list[tuple[int, int]], list[tuple[int, int]]]:
    """Return ``(code, doc_ranges, module_doc_ranges)``.

    ``code`` is *text* with every comment character replaced by a space and all
    newlines preserved. Doc ranges are ``(start_line, end_line)`` pairs (1-based)
    for ``/-- ... -/`` and ``/-! ... -/`` block comments. Nested block comments
    (Lean allows them) are handled; the kind is fixed by the outermost opener."""
    out: list[str] = []
    doc_ranges: list[tuple[int, int]] = []
    mod_ranges: list[tuple[int, int]] = []

    n = len(text)
    i = 0
    line = 1
    depth = 0
    block_start = 0
    block_kind: str | None = None  # "doc" | "mod" | "normal"
    in_line = False
    in_str = False
    str_escape = False

    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line:
            if c == "\n":
                in_line = False
                out.append("\n")
                line += 1
            else:
                out.append(" ")
            i += 1
            continue

        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if c == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
                if depth == 0:
                    if block_kind == "doc":
                        doc_ranges.append((block_start, line))
                    elif block_kind == "mod":
                        mod_ranges.append((block_start, line))
                    block_kind = None
                continue
            if c == "\n":
                out.append("\n")
                line += 1
            else:
                out.append(" ")
            i += 1
            continue

        if in_str:
            out.append(c)
            if str_escape:
                str_escape = False
            elif c == "\\":
                str_escape = True
            elif c == '"':
                in_str = False
            if c == "\n":
                line += 1
            i += 1
            continue

        # normal mode
        if c == "-" and nxt == "-":
            in_line = True
            out.append("  ")
            i += 2
            continue
        if c == "/" and nxt == "-":
            depth = 1
            block_start = line
            third = text[i + 2] if i + 2 < n else ""
            block_kind = "doc" if third == "-" else "mod" if third == "!" else "normal"
            out.append("  ")
            i += 2
            continue
        if c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if c == "\n":
            out.append("\n")
            line += 1
            i += 1
            continue
        out.append(c)
        i += 1

    return "".join(out), doc_ranges, mod_ranges


def parse_lean(path: Path) -> LeanSource:
    text = path.read_text(encoding="utf-8", errors="replace")
    code, doc_ranges, mod_ranges = _blank_comments(text)
    return LeanSource(path, text, code, doc_ranges, mod_ranges)


def load_all(repo_root: Path) -> list[LeanSource]:
    return [parse_lean(p) for p in iter_lean_files(repo_root)]


# --------------------------------------------------------------------------- #
# Small CLI helpers
# --------------------------------------------------------------------------- #
def rel(path: Path, repo_root: Path) -> str:
    """Path relative to the repo root, for tidy printing."""
    try:
        return str(path.resolve().relative_to(repo_root.resolve()))
    except ValueError:
        return str(path)

#!/usr/bin/env python3
"""Concept layer (from the Obsidian vault) -> docs/spectra-concepts.json

Makes the vault's concept<->module mapping consumable WITHOUT Obsidian: for each concept it emits the
theme, one-line summary, the modules that formalize it (with source paths and per-module `sorry` count
computed comment-aware), related concepts, and an overall sorry status.

Source of truth: the concept notes' YAML frontmatter (`Spectra-Vault/Concepts/*.md`) for theme + modules,
`.build/master.json` for one-liners/related, and the .lean source for `sorry` status. Skips gracefully if
the vault is absent (it is a local, git-ignored tool).

    python3 @Meta/concept_export.py
"""
from __future__ import annotations
import json, re, glob, os
import _spectra_meta as M

def main():
    repo = M.find_repo_root()
    vault = repo / "Spectra-Vault"
    if not (vault / "Concepts").is_dir():
        print("no Spectra-Vault/Concepts -> nothing to export"); return 0

    # sorry occurrences per module (no `Spectra.` prefix, to match concept frontmatter)
    sorry_by_mod = {}
    for s in M.load_all(repo):
        m = M.module_of_path(s.path, repo)
        if m.startswith("Spectra."): m = m[len("Spectra."):]
        n = len(re.findall(r"\bsorry\b", s.code))
        if n: sorry_by_mod[m] = n

    # one-liners / related from master.json (if present)
    master = {}
    mj = vault / ".build" / "master.json"
    if mj.exists():
        for c in json.loads(mj.read_text()):
            master[c["name"]] = c

    fm_item = re.compile(r"^\s*-\s+(\S+)\s*$")
    concepts = []
    for f in sorted(glob.glob(str(vault / "Concepts" / "*.md"))):
        name = os.path.splitext(os.path.basename(f))[0]
        lines = open(f).read().splitlines()
        if not lines or lines[0].strip() != "---":
            continue
        end = next((i for i in range(1, len(lines)) if lines[i].strip() == "---"), len(lines))
        theme, mods, in_mods = "", [], False
        for ln in lines[1:end]:
            tm = re.match(r'^theme:\s*"?(.*?)"?\s*$', ln)
            if tm and not in_mods: theme = tm.group(1)
            if re.match(r"^modules:\s*$", ln): in_mods = True; continue
            if in_mods:
                mm = fm_item.match(ln)
                if mm: mods.append(mm.group(1))
                elif re.match(r"^\S", ln): in_mods = False
        mod_objs = [{"module": m, "src": f"Spectra/{m.replace('.', '/')}.lean",
                     "sorry": sorry_by_mod.get(m, 0)} for m in mods]
        sorry_total = sum(o["sorry"] for o in mod_objs)
        minfo = master.get(name, {})
        concepts.append({
            "name": name,
            "theme": theme,
            "summary": minfo.get("oneLine", ""),
            "modules": mod_objs,
            "related": minfo.get("related", []),
            "sorry_total": sorry_total,
            "complete": sorry_total == 0,
        })

    docs = repo / "docs"; docs.mkdir(exist_ok=True)
    out = {
        "meta": {
            "library": "Spectra",
            "generated_by": "@Meta/concept_export.py",
            "note": "Concept layer from the Obsidian vault. Prose lives in Spectra-Vault/Concepts/<name>.md; "
                    "ground truth is the .lean source (verify with `lake build`).",
            "concepts": len(concepts),
            "with_open_goals": sum(1 for c in concepts if not c["complete"]),
        },
        "concepts": concepts,
    }
    (docs / "spectra-concepts.json").write_text(json.dumps(out, indent=1))
    print(f"docs/spectra-concepts.json: {len(concepts)} concepts, "
          f"{out['meta']['with_open_goals']} with open goals")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())

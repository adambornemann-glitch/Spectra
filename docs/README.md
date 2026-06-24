# Spectra — documentation site

A self-contained, dependency-free HTML site that visualises the current state of the
Spectra Lean 4 library. Open [`index.html`](index.html) directly in a browser (works over
`file://` — the data is embedded as a JS global, no server required), or serve the folder.

## Pages

| Page | What it shows |
|------|---------------|
| [`index.html`](index.html) | **Overview** — headline metrics, verification-health gauge, declaration-kind donut, area sizes, recent commits |
| [`theorems.html`](theorems.html) | **Crown Jewels** — every theorem gated `sorry`-free in `AxiomCheck.lean`, with human-readable statements |
| [`areas.html`](areas.html) | **Atlas** — a squarified treemap of the 19 subject areas, click to drill into modules |
| [`graph.html`](graph.html) | **Dependency Galaxy** — an interactive force-directed graph of all 274 modules and 504 import edges (drag, zoom, hover, filter) |
| [`files.html`](files.html) | **Module Index** — a sortable, searchable table of every source file |
| [`roadmap.html`](roadmap.html) | **Frontier** — the open `sorry`s and the deep results they reach toward |

Everything is hand-rolled vanilla HTML/CSS/SVG/Canvas — no D3, no frameworks, no fonts or
scripts fetched from a CDN. The whole site renders offline.

## Refreshing the snapshot

All pages read from `data.js` (a JS-wrapped copy of `spectra-data.json`). Regenerate both
from the live source tree with:

```sh
python3 @Meta/export_json.py --out docs/spectra-data.json --js docs/data.js
```

The exporter reuses `@Meta/_spectra_meta.py` (the comment-aware Lean parser) to recount
lines, declarations, doc coverage, `sorry`s, the import graph, and the `AxiomCheck.lean`
gate, and pulls recent commits from `git log`. No data is hand-edited.

## Local preview

```sh
python3 @Meta/devserver.py 8099    # no-cache static server → http://localhost:8099
```

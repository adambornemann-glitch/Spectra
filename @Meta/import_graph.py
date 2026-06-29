#!/usr/bin/env python3
"""Internal module dependency graph for Spectra.

Builds the ``import`` graph over the library's own modules (Mathlib and other
external imports are ignored) and answers the questions that matter when you are
navigating or refactoring a large formalization:

    --orphans   modules not reachable from the root Spectra.lean aggregator
                (i.e. they will never be built as part of the library)
    --cycles    import cycles (Lean forbids these; finding one explains a build
                error that is otherwise cryptic)
    --rank      the most depended-upon modules -- the load-bearing files you
                should be most careful changing
    --deps M    direct + transitive dependencies of module M
    --rdeps M   reverse dependencies: everything that (transitively) imports M
    --dot       emit Graphviz DOT (pipe to `dot -Tsvg`); pair with --area to
                restrict to one subject area

With no flags it prints a short summary. Module names may be given in full
(``Spectra.KMS.ImaginaryTime``) or by suffix (``KMS.ImaginaryTime``).
"""

from __future__ import annotations

import argparse
import sys
from collections import defaultdict, deque

import _spectra_meta as M


def build_graph(repo_root):
    """Return (nodes, out_edges) where nodes is the set of internal modules
    (including the synthetic root ``Spectra``) and out_edges maps a module to
    the set of internal modules it imports."""
    out_edges = defaultdict(set)
    nodes = set()

    for s in M.load_all(repo_root):
        mod = M.module_of_path(s.path, repo_root)
        nodes.add(mod)
        for dep in s.imports():
            out_edges[mod].add(dep)

    # The root aggregator is itself a module ("Spectra"); wire it to its imports.
    agg = M.aggregator_path(repo_root)
    if agg.is_file():
        root_src = M.parse_lean(agg)
        for dep in root_src.imports():
            out_edges[M.LIB_NAME].add(dep)
        nodes.add(M.LIB_NAME)

    # Keep only edges that point at real internal nodes.
    for m in list(out_edges):
        out_edges[m] = {d for d in out_edges[m] if d in nodes}

    return nodes, out_edges


def reachable_from(root, out_edges):
    seen = {root}
    q = deque([root])
    while q:
        m = q.popleft()
        for d in out_edges.get(m, ()):
            if d not in seen:
                seen.add(d)
                q.append(d)
    return seen


def reverse_edges(out_edges):
    rev = defaultdict(set)
    for m, deps in out_edges.items():
        for d in deps:
            rev[d].add(m)
    return rev


def transitive(start, edges):
    """All nodes reachable from *start* (exclusive of start)."""
    seen = set()
    q = deque(edges.get(start, ()))
    while q:
        m = q.popleft()
        if m in seen:
            continue
        seen.add(m)
        q.extend(edges.get(m, ()))
    return seen


def find_cycles(nodes, out_edges):
    """Tarjan's SCC; return the strongly-connected components with >1 node plus
    any self-loops (each is an import cycle)."""
    index = {}
    low = {}
    on_stack = {}
    stack = []
    counter = [0]
    sccs = []

    sys.setrecursionlimit(10000)

    def strongconnect(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack[v] = True
        for w in out_edges.get(v, ()):
            if w not in index:
                strongconnect(w)
                low[v] = min(low[v], low[w])
            elif on_stack.get(w):
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack[w] = False
                comp.append(w)
                if w == v:
                    break
            sccs.append(comp)

    for v in nodes:
        if v not in index:
            strongconnect(v)

    cycles = [c for c in sccs if len(c) > 1]
    cycles += [[v] for v in nodes if v in out_edges.get(v, ())]  # self-loops
    return cycles


def resolve(name, nodes):
    """Accept a full module name or a unique suffix."""
    if name in nodes:
        return name
    cands = [n for n in nodes if n == name or n.endswith("." + name)]
    if len(cands) == 1:
        return cands[0]
    if not cands:
        raise SystemExit(f"no module matches {name!r}")
    raise SystemExit(f"ambiguous: {name!r} matches " + ", ".join(sorted(cands)))


def emit_dot(nodes, out_edges, area):
    print("digraph spectra {")
    print('  rankdir=LR; node [shape=box, fontsize=10, fontname="monospace"];')

    def keep(m):
        return area is None or M.top_area(m) == area

    for m in sorted(nodes):
        if m == M.LIB_NAME or not keep(m):
            continue
        for d in sorted(out_edges.get(m, ())):
            if d == M.LIB_NAME or not keep(d):
                continue
            print(f'  "{m}" -> "{d}";')
    print("}")


def main():
    ap = argparse.ArgumentParser(description="Spectra internal import graph.")
    ap.add_argument("--orphans", action="store_true",
                    help="modules unreachable from the root aggregator")
    ap.add_argument("--cycles", action="store_true", help="report import cycles")
    ap.add_argument("--rank", type=int, metavar="N", nargs="?", const=20,
                    help="top-N most depended-upon modules (default 20)")
    ap.add_argument("--deps", metavar="MODULE", help="transitive dependencies of MODULE")
    ap.add_argument("--rdeps", metavar="MODULE", help="transitive reverse-deps of MODULE")
    ap.add_argument("--dot", action="store_true", help="emit Graphviz DOT")
    ap.add_argument("--area", help="restrict --dot to one subject area, e.g. KMS")
    args = ap.parse_args()

    repo_root = M.find_repo_root()
    nodes, out_edges = build_graph(repo_root)
    rev = reverse_edges(out_edges)
    source_nodes = nodes - {M.LIB_NAME}

    did_something = False

    if args.dot:
        emit_dot(nodes, out_edges, args.area)
        return

    if args.orphans:
        did_something = True
        reach = reachable_from(M.LIB_NAME, out_edges)
        orphans = sorted(source_nodes - reach)
        print(f"Orphan modules (unreachable from {M.LIB_NAME}.lean): {len(orphans)}")
        for m in orphans:
            print(f"  {m}")

    if args.cycles:
        did_something = True
        cycles = find_cycles(nodes, out_edges)
        if not cycles:
            print("Import cycles: none ✓")
        else:
            print(f"Import cycles: {len(cycles)}")
            for c in cycles:
                print("  " + " → ".join(c) + " → " + c[0])

    if args.rank is not None:
        did_something = True
        ranked = sorted(source_nodes, key=lambda m: (-len(rev.get(m, ())), m))
        print(f"Most depended-upon modules (top {args.rank}):")
        for m in ranked[:args.rank]:
            print(f"  {len(rev.get(m, '')):>4}  {m}")

    if args.deps:
        did_something = True
        m = resolve(args.deps, nodes)
        deps = sorted(transitive(m, out_edges) - {M.LIB_NAME})
        print(f"{m} depends on {len(deps)} internal module(s):")
        for d in deps:
            print(f"  {d}")

    if args.rdeps:
        did_something = True
        m = resolve(args.rdeps, nodes)
        rdeps = sorted(transitive(m, rev) - {M.LIB_NAME})
        print(f"{len(rdeps)} module(s) (transitively) import {m}:")
        for d in rdeps:
            print(f"  {d}")

    if not did_something:
        total_edges = sum(len(v) for v in out_edges.values())
        reach = reachable_from(M.LIB_NAME, out_edges)
        orphans = source_nodes - reach
        cycles = find_cycles(nodes, out_edges)
        print(f"Modules ............ {len(source_nodes)}")
        print(f"Internal edges ..... {total_edges}")
        print(f"Orphans ............ {len(orphans)}  (--orphans to list)")
        print(f"Import cycles ...... {len(cycles)}  (--cycles to list)")
        print("Try: --rank  --deps M  --rdeps M  --dot --area KMS")


if __name__ == "__main__":
    main()

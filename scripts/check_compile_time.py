#!/usr/bin/env python3
"""Per-file compile-time monitor for Spectra, with a baseline ratchet for CI.

Times how long each Lean file takes to elaborate in isolation and flags any
file slower than a threshold (default 5s) so it can be assessed (split, have a
slow tactic replaced, etc.). There is no external "correct" number to defer to —
Mathlib manages compile time via a *relative* CI regression bot plus its
line-count linter, not an absolute per-file wall-clock budget — so 5s here is
chosen from this library's own data: comfortably above the ~1-4s floor that is
just import-loading overhead (see below), comfortably below the real outliers.

Measurement method
-------------------
For each target file this runs

    lake env lean <path/to/File.lean>

and times the wall clock of that subprocess. ``lake env`` sets up the same
``LEAN_PATH`` a real ``lake build`` would use, so the file's own dependencies
are loaded from already-built ``.olean``s (not recompiled) and the number
measured is just this file's own parse+elaborate cost — the same unit of work
Lake itself would redo if the file changed. No ``-o``/``-i`` is passed, so
nothing is written to ``.lake/build`` and the real build's cache/hashes are
left untouched; this script is safe to run at any time without disturbing a
subsequent ``lake build``.

This requires the project (and Mathlib) to already be built — run
``lake exe cache get && lake build`` first, otherwise every file will fail to
resolve its imports. The script checks for a populated ``.lake/build`` and
aborts with a clear message if it looks unbuilt.

Baseline ratchet
----------------
Compile times are inherently noisy (machine load, thermal throttling, cache
warmth) in a way line counts are not, so the ratchet uses a *tolerance* rather
than a strict ``>`` comparison: a baselined file only counts as WORSE if its
new time exceeds ``max(baseline * (1 + tolerance_pct), baseline + tolerance_abs)``.

    python3 scripts/check_compile_time.py --all --write-baseline scripts/compile-time-baseline.txt
    python3 scripts/check_compile_time.py --changed --strict --baseline scripts/compile-time-baseline.txt

Trend tracking
--------------
``--graph`` prints an ASCII histogram of the current run's time distribution
straight to the terminal (no file). ``--history PATH`` appends this run's
*aggregate* stats (mean/median/p90/max/count-over-threshold — not a per-file
series, so it survives files being added, deleted, split, or renamed) as one
JSON line to PATH. ``--trend PATH`` reads that log back as an ASCII sparkline,
so repeated full sweeps over time show whether the library is getting slower.

    python3 scripts/check_compile_time.py --all --graph
    python3 scripts/check_compile_time.py --all --history scripts/compile-time-history.jsonl
    python3 scripts/check_compile_time.py --trend scripts/compile-time-history.jsonl

Usage:
    python3 scripts/check_compile_time.py --changed              # fast: files touched vs. base
    python3 scripts/check_compile_time.py --all --jobs 4          # full sweep, report only
    python3 scripts/check_compile_time.py --files A.lean B.lean   # explicit list
    python3 scripts/check_compile_time.py --changed --json
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

LIB_NAME = "Spectra"
THRESHOLD_DEFAULT = 5.0    # seconds — chosen to sit above the import-loading floor (see docstring)
TIMEOUT_DEFAULT = 180.0    # seconds; safety cap against a genuinely hung process
TOLERANCE_PCT_DEFAULT = 0.5   # baseline ratchet: 50% relative slack
TOLERANCE_ABS_DEFAULT = 1.0   # ...or 1s absolute slack, whichever is larger
HISTORY_DEFAULT = "scripts/compile-time-history.jsonl"
HISTOGRAM_BUCKETS = [(0, 1), (1, 2), (2, 3), (3, 5), (5, 8), (8, 15), (15, float("inf"))]
SPARK_CHARS = "▁▂▃▄▅▆▇█"


# --------------------------------------------------------------------------- #
# Repo layout
# --------------------------------------------------------------------------- #
def find_repo_root() -> Path:
    here = Path(__file__).resolve()
    for cand in (here, *here.parents):
        if (cand / "lakefile.lean").is_file():
            return cand
    raise RuntimeError("could not locate repo root (no lakefile.lean found)")


def module_of(path: Path, repo_root: Path) -> str:
    rel = path.resolve().relative_to(repo_root.resolve())
    return ".".join(rel.with_suffix("").parts)


def check_project_built(repo_root: Path) -> None:
    lib_dir = repo_root / ".lake" / "build" / "lib" / "lean"
    if not lib_dir.is_dir() or not any(lib_dir.rglob("*.olean")):
        raise SystemExit(
            "error: no built .olean artifacts found under .lake/build.\n"
            "  This script times files against an already-built project — run\n"
            "    lake exe cache get && lake build\n"
            "  first, then re-run this check."
        )


# --------------------------------------------------------------------------- #
# File selection
# --------------------------------------------------------------------------- #
def discover_all(repo_root: Path) -> list[Path]:
    files = [p for p in (repo_root / LIB_NAME).rglob("*.lean") if ".lake" not in p.parts]
    for extra in ("AxiomCheck.lean", "Spectra.lean"):
        p = repo_root / extra
        if p.is_file():
            files.append(p)
    return sorted(set(files))


def _git(repo_root: Path, *args: str) -> str | None:
    try:
        out = subprocess.run(["git", *args], cwd=repo_root, capture_output=True,
                              text=True, timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        return None
    return out.stdout.strip() if out.returncode == 0 else None


def _ref_exists(repo_root: Path, ref: str) -> bool:
    return _git(repo_root, "rev-parse", "--verify", "-q", ref) is not None


def resolve_base(repo_root: Path, explicit: str | None) -> str | None:
    if explicit:
        return explicit
    candidates = []
    gh_base = os.environ.get("GITHUB_BASE_REF")
    if gh_base:
        candidates.append(f"origin/{gh_base}")
    candidates += ["origin/master", "master", "HEAD~1"]
    for cand in candidates:
        if _ref_exists(repo_root, cand):
            return cand
    return None


def discover_changed(repo_root: Path, base: str | None) -> list[Path]:
    names: set[str] = set()
    resolved = resolve_base(repo_root, base)
    if resolved:
        diff = _git(repo_root, "diff", "--name-only", "--diff-filter=ACMR", f"{resolved}...HEAD")
        if diff:
            names.update(diff.splitlines())
    status = _git(repo_root, "status", "--porcelain", "--no-renames")
    if status:
        for line in status.splitlines():
            # porcelain format: "XY path" (or "XY orig -> new", excluded via --no-renames)
            names.add(line[3:])
    files = []
    for name in names:
        if name.endswith(".lean"):
            p = repo_root / name
            if p.is_file():
                files.append(p)
    if not files:
        base_desc = resolved or "(no base resolved)"
        print(f"note: no changed .lean files found (base={base_desc}, plus working tree)")
    return sorted(set(files))


# --------------------------------------------------------------------------- #
# Timing
# --------------------------------------------------------------------------- #
def time_file(repo_root: Path, path: Path, timeout: float) -> dict:
    module = module_of(path, repo_root)
    rel = path.resolve().relative_to(repo_root.resolve())
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(rel)],
            cwd=repo_root, capture_output=True, text=True, timeout=timeout,
        )
        elapsed = time.perf_counter() - start
        # Lean reports errors on stdout by default (stderr is for interpreter panics),
        # so surface both when something goes wrong.
        output = (proc.stdout + proc.stderr).strip()
        return {"module": module, "seconds": elapsed, "ok": proc.returncode == 0,
                "timed_out": False,
                "stderr_tail": "" if proc.returncode == 0 else output[-800:]}
    except subprocess.TimeoutExpired:
        return {"module": module, "seconds": timeout, "ok": False,
                "timed_out": True, "stderr_tail": ""}


def time_files(repo_root: Path, paths: list[Path], timeout: float, jobs: int) -> list[dict]:
    results = []
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        for r in pool.map(lambda p: time_file(repo_root, p, timeout), paths):
            results.append(r)
    results.sort(key=lambda r: -r["seconds"])
    return results


# --------------------------------------------------------------------------- #
# Baseline ratchet
# --------------------------------------------------------------------------- #
def load_baseline(path: Path) -> dict:
    base = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        module, seconds = line.split()
        base[module] = float(seconds)
    return base


def write_baseline(path: Path, violations: list[dict], threshold: float) -> None:
    lines = [
        "# Spectra compile-time baseline — grandfathered slow files.",
        "# CI (check_compile_time.py --strict --baseline this) fails only on NEW or",
        "# WORSENED (beyond tolerance) entries, so the list can only shrink.",
        "# Regenerate after improvements with:",
        "#   python3 scripts/check_compile_time.py --all --write-baseline " + path.name,
        f"# threshold: {threshold}s",
    ]
    rows = [f"{v['module']} {v['seconds']:.2f}" for v in violations]
    lines.extend(sorted(rows))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def ratchet(violations: list[dict], baseline: dict, tol_pct: float, tol_abs: float,
            checked_modules: set):
    new, worse, ok = [], [], []
    for v in violations:
        b = baseline.get(v["module"])
        if b is None:
            new.append(v)
        elif v["seconds"] > max(b * (1 + tol_pct), b + tol_abs):
            worse.append({**v, "baseline": b})
        else:
            ok.append(v)
    # Only count a baseline entry as "fixed" if this run actually re-measured it —
    # otherwise a partial run (--changed/--files) would misreport unchecked files
    # as improved. Full sweeps (--all) check everything, so this is exact there.
    violating_now = {v["module"] for v in violations}
    fixed = sum(1 for m in baseline if m in checked_modules and m not in violating_now)
    return new, worse, ok, fixed


# --------------------------------------------------------------------------- #
# Trend tracking (aggregate stats only, so it survives files being added,
# removed, split, or renamed — no per-file history is kept).
# --------------------------------------------------------------------------- #
def summary_stats(results: list[dict]) -> dict:
    secs = sorted(r["seconds"] for r in results)
    n = len(secs)
    if n == 0:
        return {"n": 0, "sum": 0.0, "mean": 0.0, "median": 0.0, "p90": 0.0, "max": 0.0}

    def pct(p: float) -> float:
        return secs[min(n - 1, round(p * (n - 1)))]

    return {"n": n, "sum": sum(secs), "mean": sum(secs) / n,
            "median": pct(0.5), "p90": pct(0.9), "max": secs[-1]}


def histogram(results: list[dict]) -> str:
    counts = [0] * len(HISTOGRAM_BUCKETS)
    for r in results:
        s = r["seconds"]
        for i, (lo, hi) in enumerate(HISTOGRAM_BUCKETS):
            if lo <= s < hi:
                counts[i] += 1
                break
    width, maxc = 40, max(counts) or 1
    lines = ["  Distribution of compile times"]
    for (lo, hi), c in zip(HISTOGRAM_BUCKETS, counts):
        label = f"{lo:g}-{hi:g}s" if hi != float("inf") else f"{lo:g}s+"
        bar = "█" * round(width * c / maxc)
        lines.append(f"  {label:>7}  {bar:<{width}}  {c}")
    return "\n".join(lines)


def append_history(path: Path, results: list[dict], threshold: float, mode: str) -> None:
    stats = summary_stats(results)
    record = {"ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
              "mode": mode, "threshold": threshold,
              "over_threshold": sum(1 for r in results if r["seconds"] > threshold),
              **stats}
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(record) + "\n")


def sparkline(values: list[float]) -> str:
    if not values:
        return ""
    lo, hi = min(values), max(values)
    span = (hi - lo) or 1.0
    n = len(SPARK_CHARS)
    return "".join(SPARK_CHARS[min(n - 1, int((v - lo) / span * (n - 1)))] for v in values)


def print_trend(path: Path, limit: int) -> None:
    if not path.is_file():
        print(f"no history yet at {path} — run with --history {path} to start recording")
        return
    records = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    if not records:
        print(f"no history yet at {path}")
        return
    shown = records if limit == 0 else records[-limit:]
    means = [r["mean"] for r in shown]
    overs = [r["over_threshold"] for r in shown]
    sums = [r["sum"] for r in shown]
    print(f"  Compile-time trend  ({len(shown)}/{len(records)} runs — {path})")
    print(f"  {shown[0]['ts']}  →  {shown[-1]['ts']}")
    print(f"  mean(s)   {sparkline(means):<{len(shown)}}  {means[0]:.2f} → {means[-1]:.2f}")
    print(f"  over-thr  {sparkline(overs):<{len(shown)}}  {overs[0]} → {overs[-1]}")
    print(f"  total(s)  {sparkline(sums):<{len(shown)}}  {sums[0]:.1f} → {sums[-1]:.1f}")


# --------------------------------------------------------------------------- #
# Reporting
# --------------------------------------------------------------------------- #
def describe(r: dict) -> str:
    flag = "  [ERROR]" if not r["ok"] and not r.get("timed_out") else \
           "  [TIMEOUT]" if r.get("timed_out") else ""
    base = f"  (baseline {r['baseline']:.2f}s)" if "baseline" in r else ""
    return f"  {r['seconds']:7.2f}s  {r['module']}{flag}{base}"


def report(results: list[dict], threshold: float, limit: int) -> None:
    slow = [r for r in results if r["seconds"] > threshold]
    print("=" * 70)
    print("  SPECTRA — COMPILE-TIME CHECK")
    print("=" * 70)
    print(f"  threshold: {threshold:.1f}s   |   files checked: {len(results)}   |   "
          f"over threshold: {len(slow)}")
    if slow:
        print(f"\n  Files over {threshold:.1f}s  ({len(slow)})")
        print("  " + "-" * 64)
        shown = slow if limit == 0 else slow[:limit]
        for r in shown:
            print(describe(r))
        if len(slow) > len(shown):
            print(f"  … and {len(slow) - len(shown):,} more  (use --limit 0)")
    failed = [r for r in results if not r["ok"]]
    if failed:
        print(f"\n  Non-zero exit / timeout while timing ({len(failed)}):")
        for r in failed:
            print(f"    {r['module']}" + ("  [TIMEOUT]" if r.get("timed_out") else ""))
    print()


def main() -> None:
    ap = argparse.ArgumentParser(description="Per-file compile-time monitor for Spectra.")
    sel = ap.add_mutually_exclusive_group()
    sel.add_argument("--changed", action="store_true",
                      help="time files changed vs. a base ref + working tree (default mode)")
    sel.add_argument("--all", action="store_true", help="time every Lean file in the library")
    sel.add_argument("--files", nargs="+", metavar="PATH", help="time an explicit file list")
    ap.add_argument("--base", help="base ref for --changed (default: auto-detect)")
    ap.add_argument("--threshold", type=float, default=THRESHOLD_DEFAULT,
                     help=f"seconds; files slower than this are flagged (default {THRESHOLD_DEFAULT})")
    ap.add_argument("--timeout", type=float, default=TIMEOUT_DEFAULT,
                     help=f"per-file safety timeout in seconds (default {TIMEOUT_DEFAULT})")
    ap.add_argument("--jobs", type=int, default=1,
                     help="parallel timing workers (default 1; >1 trades fidelity for speed)")
    ap.add_argument("--baseline", type=Path, help="compare against this baseline (ratchet)")
    ap.add_argument("--write-baseline", type=Path, help="snapshot current slow files and exit")
    ap.add_argument("--tolerance-pct", type=float, default=TOLERANCE_PCT_DEFAULT,
                     help=f"ratchet relative slack (default {TOLERANCE_PCT_DEFAULT})")
    ap.add_argument("--tolerance-abs", type=float, default=TOLERANCE_ABS_DEFAULT,
                     help=f"ratchet absolute slack in seconds (default {TOLERANCE_ABS_DEFAULT})")
    ap.add_argument("--limit", type=int, default=30, help="rows shown, 0 = all")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--strict", action="store_true", help="exit 1 on new/worsened violations")
    ap.add_argument("--graph", action="store_true",
                     help="print an ASCII histogram of this run's time distribution")
    ap.add_argument("--history", nargs="?", const=Path(HISTORY_DEFAULT), type=Path, default=None,
                     metavar="PATH",
                     help=f"append this run's aggregate stats to PATH as JSONL (default: {HISTORY_DEFAULT})")
    ap.add_argument("--trend", nargs="?", const=Path(HISTORY_DEFAULT), type=Path, default=None,
                     metavar="PATH",
                     help=f"print an ASCII trend view from PATH and exit, no build needed "
                          f"(default: {HISTORY_DEFAULT})")
    args = ap.parse_args()

    repo_root = find_repo_root()

    if args.trend is not None:
        print_trend(args.trend, args.limit)
        return

    check_project_built(repo_root)

    if args.files:
        paths = [Path(f) if Path(f).is_absolute() else repo_root / f for f in args.files]
        paths = [p for p in paths if p.is_file()]
    elif args.all:
        paths = discover_all(repo_root)
    else:
        paths = discover_changed(repo_root, args.base)

    if not paths:
        print("no files to check")
        return

    results = time_files(repo_root, paths, args.timeout, args.jobs)
    violations = [r for r in results if r["seconds"] > args.threshold]

    if args.graph:
        print(histogram(results))
        print()

    if args.history is not None:
        mode = "files" if args.files else ("all" if args.all else "changed")
        append_history(args.history, results, args.threshold, mode)
        print(f"appended history record to {args.history}")

    if args.write_baseline:
        write_baseline(args.write_baseline, violations, args.threshold)
        print(f"wrote baseline: {args.write_baseline}  ({len(violations):,} entries)")
        return

    if args.baseline:
        baseline = load_baseline(args.baseline)
        checked_modules = {r["module"] for r in results}
        new, worse, ok, fixed = ratchet(violations, baseline, args.tolerance_pct,
                                         args.tolerance_abs, checked_modules)
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
        print(json.dumps({"results": results, "threshold": args.threshold}, indent=2))
    else:
        report(results, args.threshold, args.limit)
    if args.strict and violations:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

"""Tiny check harness: collect named comparisons, print a report, set exit code.

Each check records the Lean declaration it validates so a failure points
straight at the formal statement under suspicion.
"""

import os
import sys

_results = []

# --------------------------------------------------------------------------
# Mutation hook (opt-in; ZERO effect on a normal run).
#
# `mutation_test.py` sets `NC_MUTATE=k` to corrupt the k-th check/check_le call
# (0-indexed) and confirm the suite then FAILS.  This proves every check is
# *live* — non-vacuous, comparing a meaningful quantity with a tight enough
# tolerance that a real discrepancy would be caught.  The corruption is a large
# additive kick (robust even when both sides are ~0 or the check is an
# inequality), so a surviving check exposes a dead/vacuous test.
# --------------------------------------------------------------------------
_mut_target = os.environ.get("NC_MUTATE")
_mut_target = int(_mut_target) if _mut_target not in (None, "") else None
_call_index = 0


def check(name, lean_decl, computed, expected, rel_tol=1e-9, abs_tol=1e-12):
    """Compare computed vs expected; record pass/fail."""
    global _call_index
    if _mut_target == _call_index:
        computed = computed + max(1.0, abs(expected)) + 1.0     # forced corruption
    _call_index += 1
    err = abs(computed - expected)
    scale = max(abs(expected), abs(computed), 1e-300)
    ok = err <= abs_tol or err / scale <= rel_tol
    _results.append((ok, name, lean_decl, computed, expected, err))
    return ok


def check_le(name, lean_decl, lhs, rhs, slack=0.0):
    """Check lhs <= rhs + slack (for inequality statements)."""
    global _call_index
    if _mut_target == _call_index:
        lhs = rhs + max(1.0, abs(rhs)) + 1.0                    # forced above rhs
    _call_index += 1
    ok = lhs <= rhs + slack
    _results.append((ok, name, lean_decl, lhs, rhs, lhs - rhs))
    return ok


def report(title):
    width = 78
    print("=" * width)
    print(title)
    print("=" * width)
    npass = sum(1 for r in _results if r[0])
    nfail = len(_results) - npass
    for ok, name, lean_decl, computed, expected, err in _results:
        tag = "PASS" if ok else "FAIL"
        print(f"[{tag}] {name}")
        print(f"       lean: {lean_decl}")
        print(f"       computed = {computed!r}")
        print(f"       expected = {expected!r}   |err| = {err:.3e}")
    print("-" * width)
    print(f"{npass} passed, {nfail} failed, {len(_results)} total")
    print("=" * width)
    return 0 if nfail == 0 else 1


def finish(title):
    sys.exit(report(title))

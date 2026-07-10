"""Automated mutation testing: prove every check is *live* (non-vacuous).

A numeric check only earns trust if it would FAIL on a wrong statement.  A check
that passes might be genuinely validating something — or it might be comparing a
quantity to itself, or using a tolerance so loose that nothing fails.  This
driver removes the doubt: for every `check`/`check_le` call in every suite it

  1. runs the suite once unperturbed (must exit 0 — all checks pass), then
  2. re-runs the suite once per check with that ONE check's computed value
     corrupted (via the `NC_MUTATE` hook in `nclib/harness.py`), and confirms
     the suite now FAILS.

If a corrupted check still passes, the suite exits 0 and this driver reports it
as a DEAD check — a test that validates nothing.  A green run here means every
check has teeth: each would catch a real discrepancy in exactly the quantity it
claims to validate.  This is the automated, exhaustive form of the by-hand
mutation table in the README.

Run: python3 mutation_test.py            # all suites
     python3 mutation_test.py check_entropy.py check_fock.py   # a subset

Exit code 0 iff every check in every suite is live.
"""

import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

SUITES = [
    "selftest.py",
    "check_hydrogen.py",
    "check_hardy.py",
    "check_infogeom.py",
    "check_misc.py",
    "check_modular.py",
    "check_kms.py",
    "check_cocycle.py",
    "check_spectral.py",
    "check_uncertainty.py",
    "check_entropy.py",
    "check_traceclass.py",
    "check_fock.py",
    "check_krein_gauge.py",
]

_TOTAL_RE = re.compile(r"(\d+) passed, (\d+) failed, (\d+) total")


def run_suite(suite, mutate=None):
    """Run a suite; return (returncode, npass, nfail, ntotal)."""
    env = dict(os.environ)
    if mutate is not None:
        env["NC_MUTATE"] = str(mutate)
    else:
        env.pop("NC_MUTATE", None)
    r = subprocess.run([sys.executable, os.path.join(HERE, suite)],
                       capture_output=True, text=True, env=env)
    m = _TOTAL_RE.search(r.stdout)
    if m:
        return r.returncode, int(m.group(1)), int(m.group(2)), int(m.group(3))
    return r.returncode, -1, -1, -1


def main(argv):
    suites = argv[1:] if len(argv) > 1 else SUITES
    grand_dead = []
    grand_total = 0
    for suite in suites:
        rc, npass, nfail, ntotal = run_suite(suite)
        if rc != 0 or nfail != 0 or ntotal < 0:
            print(f"!! {suite}: does not pass cleanly unperturbed (rc={rc}, "
                  f"pass={npass}, fail={nfail}) — cannot mutation-test")
            grand_dead.append((suite, -1, "suite not green unperturbed"))
            continue
        dead = []
        for k in range(ntotal):
            rc_k, _, nfail_k, _ = run_suite(suite, mutate=k)
            # a live check ⇒ corrupting it makes the suite fail (rc≠0 / nfail≥1)
            if rc_k == 0 and nfail_k == 0:
                dead.append(k)
        grand_total += ntotal
        tag = "OK" if not dead else "DEAD"
        print(f"[{tag}] {suite}: {ntotal} checks, "
              f"{ntotal - len(dead)}/{ntotal} live"
              + (f"  DEAD indices: {dead}" if dead else ""))
        for k in dead:
            grand_dead.append((suite, k, "survived corruption"))

    print("-" * 70)
    if grand_dead:
        print(f"MUTATION TEST FAILED: {len(grand_dead)} dead check(s) out of {grand_total}")
        for suite, k, why in grand_dead:
            print(f"    {suite} #{k}: {why}")
        return 1
    print(f"All {grand_total} checks are LIVE (each fails when its value is corrupted).")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

"""Run every numeric check suite; exit nonzero if any suite fails.

Usage: python3 run_all.py
"""

import os
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


def main():
    failures = []
    for suite in SUITES:
        print(f"\n>>> {suite}")
        r = subprocess.run([sys.executable, os.path.join(HERE, suite)])
        if r.returncode != 0:
            failures.append(suite)
    print()
    if failures:
        print(f"FAILED suites: {', '.join(failures)}")
        return 1
    print("All numeric check suites passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

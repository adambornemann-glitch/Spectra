#!/usr/bin/env bash
# Regenerate docs/spectra-forensic.json (unused-hypothesis ledger + assumption cones
# for the headline theorems). The SURPRISE tripwire itself is enforced on every
# `lake build` by the ForensicCheck default target; this script is the full report.
set -euo pipefail
cd "$(dirname "$0")/.."
exec lake env lean ForensicReport.lean

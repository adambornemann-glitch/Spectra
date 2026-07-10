/-
Copyright (c) 2026 Spectra Project, Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Forensic

/-!
# Hypothesis-hygiene gate

A **compile-time gate**, not library content — the statement-level analogue of
[`AxiomCheck`](AxiomCheck.lean). It scans every user-facing theorem in `Spectra.*` and
fails the build if any carries a *normally-named but unused* hypothesis: a declared
`Prop`-hypothesis whose proof term never touches it. Such a hypothesis makes the statement
stronger than it needs to be, or — if it is unsatisfiable — vacuously true.

Because `ForensicCheck` is a `@[default_target]` in [`lakefile.lean`](lakefile.lean), a plain
`lake build` (and therefore CI) fails the moment such a hypothesis appears. Hypotheses kept
deliberately (for API symmetry, documentation, or a "morally required" side condition) are
exempted by the standard `_`-prefix convention, which is exactly the author's own signal
that the argument is intentionally unused. Anonymous/hygienic binders are also exempt.

The full report (all buckets plus assumption cones for the crown jewels) is generated on
demand by [`ForensicReport.lean`](ForensicReport.lean).
-/

open Lean Lean.Meta Lean.Elab.Command Spectra.Forensic

set_option maxHeartbeats 0

run_cmd liftTermElabM do
  let env ← getEnv
  let (flags, scanned, errored) ← scanUnusedFlags env
  let surprise := flags.filter fun f => f.kind == "prop" && f.bucket == "surprise"
  let ack      := (flags.filter fun f => f.kind == "prop" && f.bucket == "ack").size
  let anon     := (flags.filter fun f => f.kind == "prop" && f.bucket == "anon").size
  if surprise.isEmpty then
    logInfo m!"Forensic gate ✔ — {scanned} theorems scanned ({errored} skipped); \
      0 surprise unused hypotheses ({ack} acknowledged via `_`, {anon} anonymous)."
  else
    let lines := surprise.toList.map fun f =>
      m!"  {f.thm}  —  unused ({f.hyp} : {f.hypTy})  [{f.mod}]"
    throwError m!"Forensic gate ✘ — {surprise.size} theorem(s) carry a normally-named but \
      unused hypothesis (over-strong or vacuous statement). Remove it, or mark it \
      intentional with a leading `_`:\n{MessageData.joinSep lines "\n"}"

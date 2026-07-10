/-
Copyright (c) 2026 Spectra Project, Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Forensic

/-!
# Forensic report generator

Run on demand (not a build target):

    lake env lean ForensicReport.lean

Writes `docs/spectra-forensic.json` — the full unused-hypothesis ledger (all buckets) plus
transitive assumption cones for a representative set of headline theorems — and prints a
short summary. The JSON is consumed by the docs site / Obsidian vault the same way the
sibling `spectra-symbols.json` exporter is.
-/

open Lean Lean.Meta Lean.Elab.Command Spectra.Forensic

set_option maxHeartbeats 0

/-- Representative crown jewels for the cone section (edit freely). -/
def headlineTargets : List Name :=
  [ `Spectra.QuantumMechanics.SpectralTheory.spectralTheorem,
    `Spectra.QuantumMechanics.SpectralTheory.spectralPVM,
    `Spectra.YosidaHille.stoneEquiv,
    `Spectra.Bochner.bochner_theorem,
    `Spectra.Bochner.GNS.gns_theorem,
    `Spectra.Fourier.fourier_uniqueness,
    `Spectra.Resolvent.generator_isSelfAdjoint,
    `Spectra.Herglotz.helly_selection,
    `Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum,
    `QuantumMechanics.Hydrogen.RadialEq.radial_quantization ]

/-- JSON array of strings. -/
def jArr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

/-- JSON array of names, each as a string literal. -/
def jNames (xs : List Name) : String := jArr (xs.map (fun n => jStr n.toString))

run_cmd liftTermElabM do
  let env ← getEnv
  let (flags, scanned, errored) ← scanUnusedFlags env
  let cnt (p : HypFlag → Bool) : Nat := (flags.filter p).size
  let surprise := cnt fun f => f.kind == "prop" && f.bucket == "surprise"
  let ackN     := cnt fun f => f.kind == "prop" && f.bucket == "ack"
  let anonN    := cnt fun f => f.kind == "prop" && f.bucket == "anon"
  let instN    := cnt fun f => f.kind == "inst"
  -- unused-hypothesis ledger
  let flagJson := flags.toList.map fun f =>
    "{" ++ String.intercalate "," [
      "\"thm\":" ++ jStr f.thm.toString,
      "\"module\":" ++ jStr f.mod.toString,
      "\"hyp\":" ++ jStr f.hyp.toString,
      "\"type\":" ++ jStr f.hypTy,
      "\"kind\":" ++ jStr f.kind,
      "\"bucket\":" ++ jStr f.bucket ] ++ "}"
  -- assumption cones for the headline set
  let mut coneJson : List String := []
  for tgt in headlineTargets do
    let c ← computeCone env tgt
    let fp := c.fingerprint.toList.map fun (sym, n) =>
      "{\"assumption\":" ++ jStr sym.toString ++ ",\"count\":" ++ toString n ++ "}"
    coneJson := coneJson ++ [
      "{" ++ String.intercalate "," [
        "\"target\":" ++ jStr tgt.toString,
        "\"found\":" ++ (if c.found then "true" else "false"),
        "\"ownHyps\":" ++ jArr (c.ownHyps.toList.map jStr),
        "\"coneUser\":" ++ toString c.coneUser,
        "\"coneAux\":" ++ toString c.coneAux,
        "\"externalBoundary\":" ++ toString c.external,
        "\"axioms\":" ++ jNames c.axioms.toList,
        "\"ambientSuppressed\":" ++ toString c.ambientSuppressed,
        "\"fingerprint\":" ++ jArr fp,
        "\"leaves\":" ++ jNames c.leaves.toList ] ++ "}" ]
  let metaObj := "{" ++ String.intercalate "," [
    "\"theoremsScanned\":" ++ toString scanned,
    "\"errored\":" ++ toString errored,
    "\"unusedPropSurprise\":" ++ toString surprise,
    "\"unusedPropAcknowledged\":" ++ toString ackN,
    "\"unusedPropAnonymous\":" ++ toString anonN,
    "\"unusedInstances\":" ++ toString instN ] ++ "}"
  let json :=
    "{\n  \"meta\": " ++ metaObj ++
    ",\n  \"unusedHypotheses\": " ++ jArr flagJson ++
    ",\n  \"cones\": " ++ jArr coneJson ++ "\n}\n"
  IO.FS.writeFile "docs/spectra-forensic.json" json
  IO.println
    (s!"forensic: {scanned} theorems | unused prop: surprise={surprise} ack={ackN} " ++
      s!"anon={anonN} | instances={instN}")
  IO.println
    s!"forensic: wrote docs/spectra-forensic.json  ({flags.size} flags, {coneJson.length} cones)"

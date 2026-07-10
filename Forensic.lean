/-
Copyright (c) 2026 Spectra Project, Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra

/-!
# Forensic index — hypothesis hygiene and assumption cones

Reusable meta-programming engine for auditing the *statements* of Spectra's theorems
(the part the kernel does **not** check). Two signals:

* **Unused-hypothesis scan** (`scanUnusedFlags`) — every theorem whose proof term never
  uses a declared `Prop`-hypothesis or instance argument. Such a hypothesis is removable:
  the statement is stronger than it needs to be, or (if the hypothesis is contradictory)
  vacuously true. Flags are bucketed by binder name: `surprise` (accessible, normally
  named — the author likely believed it was needed), `ack` (`_`-prefixed, intentionally
  unused by convention), `anon` (hygienic/unnamed).

* **Transitive assumption cone** (`computeCone`) — for a headline theorem, the full set of
  `Spectra` lemmas its proof rests on (Mathlib is the trusted boundary), the marginal
  assumptions that whole tower leans on (ambient Hilbert/measure structure quotiented
  out), the base leaves, and the axiom foundation.

This module has **no** top-level side effects; `ForensicCheck.lean` wires the unused-scan
into a build gate and `ForensicReport.lean` serialises everything to JSON.

Implementation notes (Lean 4.31):
* Filter theorems by **source module** (`getModuleIdxFor?`), not by name — Spectra
  declarations are not reliably `Spectra`-name-prefixed.
* `ConstantInfo.value?` returns `none` for *every* theorem; the proof term must be read
  from the `thmInfo`/`defnInfo` `value` field directly.
* Read a theorem's conclusion from its **declared type**, not `inferType` of the proof —
  `rfl` proofs infer to `x = x`, dropping hypotheses that occur only in the stated RHS.
-/

open Lean Lean.Meta

namespace Spectra.Forensic

/-! ## Shared predicates -/

/-- Auto-generated structure/inductive boilerplate we never scan. -/
def genLast : List String :=
  ["sizeOf_spec", "injEq", "noConfusion", "noConfusionType", "rec", "recOn", "casesOn",
   "brecOn", "below", "ibelow", "ind", "binductionOn", "toCtorIdx", "eq_def", "ofNat"]

def isGenerated : Name → Bool
  | .str _ s => genLast.contains s
  | _        => false

/-- Is `n` defined in a `Spectra.*` source module? -/
def isSpectra (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Spectra).isPrefixOf (env.header.moduleNames[idx]!)
  | none     => false

/-- A user-facing theorem or definition (not compiler boilerplate). -/
def isUserDecl (env : Environment) (n : Name) : Bool :=
  !n.isInternalDetail && !isGenerated n &&
  match env.find? n with
  | some (.thmInfo _)  => true
  | some (.defnInfo _) => true
  | _                  => false

/-- Does free variable `fv` occur anywhere in `e`? -/
def occursIn (fv : FVarId) (e : Expr) : Bool :=
  Option.isSome <| e.find? fun s => match s with
    | .fvar id => id == fv
    | _        => false

/-- Ambient "Hilbert space over ℂ with a measure structure" typeclasses (stratum 2),
    quotiented out so the marginal mathematical assumptions (stratum 3) surface. -/
def ambientList : List String :=
  ["NormedAddCommGroup", "SeminormedAddCommGroup", "InnerProductSpace", "CompleteSpace",
   "NormedSpace", "NormedField", "NormedRing", "NormedAlgebra", "Algebra", "Module",
   "AddCommGroup", "AddCommMonoid", "Ring", "CommRing", "Field", "Semiring", "CommMonoid",
   "RCLike", "TopologicalSpace", "MeasurableSpace", "MetricSpace", "PseudoMetricSpace",
   "T2Space", "ProperSpace", "SecondCountableTopology", "BorelSpace", "OpensMeasurableSpace",
   "Nontrivial", "DecidableEq", "Fintype", "Countable"]

def isAmbient : Name → Bool
  | .str _ s => ambientList.contains s
  | _        => false

/-- Head symbol of a hypothesis type, for tallying which assumptions recur. -/
def headSym (e : Expr) : Name :=
  if e.isForall then `«∀»
  else match e.getAppFn with
    | .const c _ => c
    | _          => `«?»

/-- Classify a bound-variable name: `_`-prefixed = author-acknowledged unused;
    hygienic = introduced without a real name; otherwise a "surprise". -/
def classifyHyp (nm : Name) : String :=
  if nm.hasMacroScopes then "anon"
  else match nm with
    | .str _ s => if s.startsWith "_" then "ack" else "surprise"
    | _        => "anon"

/-! ## Signal 1 — unused hypotheses -/

structure HypFlag where
  thm    : Name
  mod    : Name
  hyp    : Name
  hypTy  : String
  kind   : String  -- "prop" | "inst"
  bucket : String  -- "surprise" | "ack" | "anon"

/-- Flag `Prop`-hypotheses / instance arguments of a theorem whose bound variable is used
    nowhere: not in the proof, the conclusion, or any other binder's type. -/
def analyzeThm (name mod : Name) (ty val : Expr) : MetaM (Array HypFlag) :=
  Meta.forallTelescope ty fun xs concl => do
    let body := val.beta xs
    let decls ← xs.mapM (·.fvarId!.getDecl)
    let types := decls.map (·.type)
    let mut flags : Array HypFlag := #[]
    for i in [0:xs.size] do
      let d := decls[i]!
      let isInst := d.binderInfo == .instImplicit
      let isPr ← Meta.isProp d.type
      unless isInst || isPr do
        continue
      let fv := xs[i]!.fvarId!
      let mut used := occursIn fv body || occursIn fv concl
      if !used then
        for j in [0:types.size] do
          if j != i && occursIn fv types[j]! then
            used := true
      if used then
        continue
      flags := flags.push
        { thm := name, mod := mod, hyp := d.userName, hypTy := toString (← Meta.ppExpr d.type),
          kind := if isInst then "inst" else "prop", bucket := classifyHyp d.userName }
    return flags

/-- Scan every user-facing theorem in `Spectra.*`. Returns (flags, #scanned, #errored). -/
def scanUnusedFlags (env : Environment) : MetaM (Array HypFlag × Nat × Nat) := do
  let targets : Array (Name × Name × Expr × Expr) := env.constants.fold (init := #[])
    fun acc name ci =>
      match ci with
      | .thmInfo ti =>
        if name.isInternalDetail || isGenerated name then acc
        else match env.getModuleIdxFor? name with
          | some idx =>
            let mn := env.header.moduleNames[idx]!
            if (`Spectra).isPrefixOf mn then acc.push (name, mn, ti.type, ti.value) else acc
          | none => acc
      | _ => acc
  let mut all : Array HypFlag := #[]
  let mut errored := 0
  for (name, mn, ty, val) in targets do
    try
      all := all ++ (← analyzeThm name mn ty val)
    catch _ =>
      errored := errored + 1
  return (all, targets.size, errored)

/-! ## Signal 2 — transitive assumption cone -/

/-- Constants referenced by a declaration's type and proof/definition body. -/
def usedConsts (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some ci =>
    let valConsts := match ci with
      | .thmInfo ti  => ti.value.getUsedConstants
      | .defnInfo vi => vi.value.getUsedConstants
      | _            => #[]
    ci.type.getUsedConstants ++ valConsts
  | none => #[]

/-- Transitive cone, recursing only through `Spectra` declarations.
    Returns (all Spectra decls reached, external/Mathlib boundary constants). -/
partial def coneGo (env : Environment) (visited external : NameSet) : List Name → NameSet × NameSet
  | []      => (visited, external)
  | n :: rest =>
    let (visited, external, work) := (usedConsts env n).foldl (init := (visited, external, rest))
      fun (v, e, w) c =>
        if isSpectra env c then
          if v.contains c then (v, e, w) else (v.insert c, e, c :: w)
        else (v, e.insert c, w)
    coneGo env visited external work

/-- Head symbols of the marginal hypotheses (Prop-valued or instance) in a signature.
    Cheaper than `marginalHyps` — no pretty-printing — for tallying cone fingerprints. -/
def marginalHypHeads (ty : Expr) : MetaM (Array Name) :=
  Meta.forallTelescope ty fun xs _ => do
    let mut acc : Array Name := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .instImplicit || (← Meta.isProp d.type) then
        acc := acc.push (headSym d.type)
    return acc

/-- The marginal hypotheses (Prop-valued or instance) in a signature, as (pretty, head). -/
def marginalHyps (ty : Expr) : MetaM (Array (String × Name)) :=
  Meta.forallTelescope ty fun xs _ => do
    let mut acc : Array (String × Name) := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      let isInst := d.binderInfo == .instImplicit
      let isPr ← Meta.isProp d.type
      if isInst || isPr then
        acc := acc.push (toString (← Meta.ppExpr d.type), headSym d.type)
    return acc

structure ConeSummary where
  target            : Name
  found             : Bool
  ownHyps           : Array String
  coneUser          : Nat
  coneAux           : Nat
  external          : Nat
  axioms            : Array Name
  fingerprint       : Array (Name × Nat)  -- non-ambient marginal assumptions, desc
  ambientSuppressed : Nat
  leaves            : Array Name

/-- Compute the assumption cone of `tgt`. -/
def computeCone (env : Environment) (tgt : Name) : MetaM ConeSummary := do
  if (env.find? tgt).isNone then
    return { target := tgt, found := false, ownHyps := #[], coneUser := 0, coneAux := 0,
             external := 0, axioms := #[], fingerprint := #[],
             ambientSuppressed := 0, leaves := #[] }
  let (visited, external) := coneGo env (NameSet.empty.insert tgt) NameSet.empty [tgt]
  let allReached := visited.toList
  let userCone := (allReached.filter (isUserDecl env ·)).eraseDups
  let userSet : NameSet := userCone.foldl (·.insert ·) NameSet.empty
  let mut freq : NameMap Nat := {}
  let mut ambientSuppressed := 0
  for n in userCone do
    for sym in (← marginalHypHeads (env.find? n).get!.type) do
      if isAmbient sym then ambientSuppressed := ambientSuppressed + 1
      else freq := freq.insert sym ((freq.find? sym).getD 0 + 1)
  let leaves := userCone.filter fun n =>
    !(usedConsts env n).any fun c => c != n && userSet.contains c
  let ownHyps := (← marginalHyps (env.find? tgt).get!.type).map (·.1)
  let ax ← collectAxioms tgt
  return {
    target := tgt, found := true, ownHyps := ownHyps,
    coneUser := userCone.length, coneAux := allReached.length - userCone.length,
    external := external.toList.length, axioms := ax,
    fingerprint := (freq.toList.toArray.qsort (fun a b => a.2 > b.2)),
    ambientSuppressed := ambientSuppressed, leaves := leaves.toArray }

/-! ## Minimal JSON serialisation (stdlib only) -/

def jsonEsc (s : String) : String :=
  (((s.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" " ")
    |>.replace "\t" " " |>.replace "\r" " "

def jStr (s : String) : String := "\"" ++ jsonEsc s ++ "\""

end Spectra.Forensic

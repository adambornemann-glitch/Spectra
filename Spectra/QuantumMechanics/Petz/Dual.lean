/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Petz.RecoveryMap
import Spectra.QuantumMechanics.Channels.TraceClass.Complete
import Spectra.QuantumMechanics.Channels.TraceClass.Trace
import Spectra.QuantumMechanics.Channels.TraceClass.RankOne

/-!
# Heisenberg dual channels and concrete Petz recovery

The Petz recovery map `petzMap Φ σ τ` (in `RecoveryMap.lean`) takes the Heisenberg dual `Φ = N†` as
an abstract *unital* map. This file makes that dual a genuine object rather than a hypothesis.

## The duality relation

For a Schrödinger-picture channel `N : T(H) → T(H)` and a Heisenberg-picture map `Nd : B(H) → B(H)`,
`IsHeisenbergDual N Nd` is the trace-duality relation

  `tr(N(ρ) · B) = tr(ρ · Nd(B))`   for all `ρ ∈ T(H)`, `B ∈ B(H)`.

We prove the **full equivalence** `Nd 1 = 1 ⟺ N` is trace-preserving
(`IsHeisenbergDual.unital_iff_tracePreserving`): the forward direction is a one-line consequence of
the duality relation at `B = 1`; the converse uses **separation of the trace pairing**
(`eq_of_forall_trace_toOp_mul_eq`, `Channels/TraceClass/RankOne.lean`) to pin `Nd 1` from the trace
identities. The identity channel is self-dual.

**Deferred (honest gating).** *Constructing* `Nd` from a general `QuantumChannel` still requires the
trace duality `B(H) = (T(H))*` (the "predual" theorem, an open Trace-Class Hard Core milestone) —
that turns `Nd` from a *given* map satisfying `IsHeisenbergDual` into one produced *from* `N`. The
separation lemma built here is exactly the nondegeneracy half of that duality.

## A concrete Heisenberg dual: conjugation

`adjointConj K : B ↦ K† · B · K` is the Heisenberg dual of the Kraus/conjugation channel
`ρ ↦ K · ρ · K†`. It is unital exactly when `K` is an isometry (`K† K = 1`), and then it is a
genuine Heisenberg-picture channel for which the Petz map recovers the reference with **no
hypothesis on the dual** — `petzMap_adjointConj_recovery`.

## Main definitions

* `IsHeisenbergDual N Nd` — the trace-duality relation.
* `adjointConj K` — conjugation `B ↦ K† B K`, the concrete Heisenberg dual of `ρ ↦ K ρ K†`.

## Main results

* `IsHeisenbergDual.tracePreserving_of_unital` — a unital dual forces trace preservation.
* `adjointConj_isUnital` — `Ad K` is unital when `K` is an isometry.
* `petzMap_adjointConj_recovery` — exact recovery for the concrete dual `Ad K`, `K` isometric.
-/

namespace Spectra.QuantumMechanics.Petz

open Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The Heisenberg duality relation -/

/-- `Nd : B(H) → B(H)` is a **Heisenberg dual** of the channel `N : T(H) → T(H)` when it satisfies
the trace-duality relation `tr(N(ρ) · B) = tr(ρ · Nd(B))` for all trace-class `ρ` and bounded `B`.
-/
def IsHeisenbergDual (N : TraceClass H → TraceClass H)
    (Nd : (H →L[ℂ] H) → (H →L[ℂ] H)) : Prop :=
  ∀ (ρ : TraceClass H) (B : H →L[ℂ] H), trace ((N ρ).toOp * B) = trace (ρ.toOp * Nd B)

/-- The identity channel is its own Heisenberg dual. -/
theorem isHeisenbergDual_id :
    IsHeisenbergDual (id : TraceClass H → TraceClass H) (id : (H →L[ℂ] H) → (H →L[ℂ] H)) :=
  fun _ _ => rfl

/-- **A unital Heisenberg dual forces the channel to preserve the trace.** Taking `B = 1` in the
duality relation and using `Nd 1 = 1` gives `tr(N ρ) = tr ρ`. (This is the direction the Petz
recovery theorem consumes: unitality of `N†` is exactly trace preservation of `N`.) -/
theorem IsHeisenbergDual.tracePreserving_of_unital {N : TraceClass H → TraceClass H}
    {Nd : (H →L[ℂ] H) → (H →L[ℂ] H)} (h : IsHeisenbergDual N Nd) (hu : Nd 1 = 1)
    (ρ : TraceClass H) : trace (N ρ).toOp = trace ρ.toOp := by
  have hρ := h ρ 1
  rwa [hu, mul_one, mul_one] at hρ

/-- **A trace-preserving channel has a unital dual.** The converse of
`tracePreserving_of_unital`, via separation of the trace pairing (`eq_of_forall_trace_toOp_mul_eq`):
`tr(N ρ) = tr ρ` for all `ρ` pins `Nd 1 = 1`. -/
theorem IsHeisenbergDual.unital_of_tracePreserving {N : TraceClass H → TraceClass H}
    {Nd : (H →L[ℂ] H) → (H →L[ℂ] H)} (h : IsHeisenbergDual N Nd)
    (htp : ∀ ρ : TraceClass H, trace (N ρ).toOp = trace ρ.toOp) : Nd 1 = 1 := by
  apply eq_of_forall_trace_toOp_mul_eq
  intro ρ
  rw [← h ρ 1, mul_one, mul_one]
  exact htp ρ

/-- **A Heisenberg dual is unital iff its channel preserves the trace** — `N† 1 = 1 ⟺ N` is
trace-preserving. This is precisely the equivalence "the Petz recovery theorem's unitality
hypothesis holds ⟺ `N` is a genuine (trace-preserving) channel", now a theorem in both directions.
-/
theorem IsHeisenbergDual.unital_iff_tracePreserving {N : TraceClass H → TraceClass H}
    {Nd : (H →L[ℂ] H) → (H →L[ℂ] H)} (h : IsHeisenbergDual N Nd) :
    Nd 1 = 1 ↔ ∀ ρ : TraceClass H, trace (N ρ).toOp = trace ρ.toOp :=
  ⟨h.tracePreserving_of_unital, h.unital_of_tracePreserving⟩

/-! ## Conjugation: a concrete Heisenberg dual -/

/-- **Conjugation** `adjointConj K : B ↦ K† · B · K`, the Heisenberg dual of the Kraus/conjugation
channel `ρ ↦ K · ρ · K†`. (`K† = star K` is the operator adjoint.) -/
noncomputable def adjointConj (K : H →L[ℂ] H) : (H →L[ℂ] H) → (H →L[ℂ] H) :=
  fun B => star K * B * K

@[simp] lemma adjointConj_apply (K B : H →L[ℂ] H) : adjointConj K B = star K * B * K := rfl

lemma adjointConj_one (K : H →L[ℂ] H) : adjointConj K 1 = star K * K := by
  rw [adjointConj_apply, mul_one]

/-- `adjointConj K` is **unital** exactly when `K` is an isometry (`K† K = 1`). -/
lemma adjointConj_isUnital {K : H →L[ℂ] H} (hK : star K * K = 1) : adjointConj K 1 = 1 := by
  rw [adjointConj_one, hK]

/-- **Exact recovery for the concrete conjugation channel.** For an isometry `K` (`K† K = 1`), a
positive reference `σ`, and a strictly positive image `τ`, the Petz map with dual `Ad K` recovers
the reference: `P_{σ, Ad K}(τ) = σ`. Unlike `petzMap_recovery`, the dual here is an *explicit* map,
not a unitality hypothesis. -/
theorem petzMap_adjointConj_recovery {K : H →L[ℂ] H} (hK : star K * K = 1)
    {σ τ : H →L[ℂ] H} (hσ : 0 ≤ σ) (hτ : IsStrictlyPositive τ) :
    petzMap (adjointConj K) σ τ τ = σ :=
  petzMap_recovery (adjointConj_isUnital hK) hσ hτ

end Spectra.QuantumMechanics.Petz

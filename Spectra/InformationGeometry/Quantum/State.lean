/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Complete
import Spectra.QuantumMechanics.Channels.TraceClass.Trace
import Spectra.QuantumMechanics.Channels.TraceClass.Norm

/-!
# Quantum states as positive, trace-one trace-class operators

This file opens `InformationGeometry/Quantum/` — the **second view** of quantum theory, in which
density operators are points on a statistical manifold and channels are morphisms between such
manifolds. The load-bearing carrier for everything downstream is a **quantum state**: a positive,
trace-one operator in `TraceClass H`.

`DensityOperator` (`BornRule/Mixed.lean`) is an *ensemble* — a family of weights and unit vectors —
not an operator, so it cannot serve directly as a point of an operator-valued manifold. `QState H`
is the operator carrier that the quantum statistical manifold, the quantum Fisher/BKM metrics, and
the Petz recovery map all consume.

## Main definitions

* `QState H` — a positive (`0 ≤ ρ`), trace-one (`tr ρ = 1`) trace-class operator on `H`.
* `QState.toOp` — the underlying bounded operator `H →L[ℂ] H`.
* `QState.Faithful` — the (infinite-dimensional) full-rank condition: `toOp` is injective, i.e. the
  state has trivial kernel. Note this is *not* "bounded below": a trace-class operator is compact,
  so a faithful density's eigenvalues accumulate at `0`, its inverse is unbounded, and `ρ^{-1/2}`
  (which appears in the Petz sandwich) is a genuinely unbounded operator in infinite dimensions.

## Main results

* `QState.traceNorm_toOp` / `QState.norm_toTraceClass` — a quantum state has trace norm `1`.
* `QState.ext` — a state is determined by its operator.
-/

namespace Spectra.InformationGeometry.Quantum

open Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **quantum state** on `H`: a positive (`0 ≤ ρ`), trace-one (`tr ρ = 1`) trace-class operator.
This is the operator-valued carrier for the quantum statistical manifold and the Petz recovery
map — the density-operator-as-manifold-point of the information-geometric second view. -/
structure QState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The underlying trace-class operator `ρ`. -/
  toTraceClass : TraceClass H
  /-- Positivity of the state: `0 ≤ ρ`. -/
  nonneg : 0 ≤ toTraceClass.toOp
  /-- Normalization of the state: `tr ρ = 1`. -/
  trace_one : trace toTraceClass.toOp = 1

namespace QState

/-- The bounded operator `ρ : H →L[ℂ] H` underlying a quantum state. -/
def toOp (ρ : QState H) : H →L[ℂ] H := ρ.toTraceClass.toOp

@[simp] lemma toOp_eq (ρ : QState H) : ρ.toOp = ρ.toTraceClass.toOp := rfl

lemma toOp_nonneg (ρ : QState H) : 0 ≤ ρ.toOp := ρ.nonneg

@[simp] lemma trace_toOp (ρ : QState H) : trace ρ.toOp = 1 := ρ.trace_one

/-- The operator of a quantum state is trace-class. -/
lemma isTraceClass (ρ : QState H) : IsTraceClass ρ.toOp := ρ.toTraceClass.isTraceClass

/-- A quantum state is determined by its operator. -/
@[ext] lemma ext {ρ σ : QState H} (h : ρ.toOp = σ.toOp) : ρ = σ := by
  cases ρ with
  | mk r hr₁ hr₂ =>
    cases σ with
    | mk s hs₁ hs₂ =>
      have hrs : r = s := TraceClass.ext h
      subst hrs
      rfl

/-- **A quantum state has trace norm `1`.** For a positive operator the trace norm is the honest
trace, which is normalized to `1`. -/
lemma traceNorm_toOp (ρ : QState H) : traceNorm ρ.toOp = 1 := by
  rw [toOp_eq]
  have hpt : ((posTrace (stdHilbertBasis H) ρ.toTraceClass.toOp).toReal : ℂ) = 1 := by
    rw [← trace_of_nonneg ρ.nonneg (stdHilbertBasis H)]
    exact ρ.trace_one
  have hpt' : (posTrace (stdHilbertBasis H) ρ.toTraceClass.toOp).toReal = 1 := by
    exact_mod_cast hpt
  rw [traceNorm_of_nonneg ρ.nonneg (stdHilbertBasis H), hpt']

/-- **A quantum state has norm `1`** in the trace-class Banach space. -/
@[simp] lemma norm_toTraceClass (ρ : QState H) : ‖ρ.toTraceClass‖ = 1 := by
  rw [TraceClass.norm_def, ← toOp_eq]
  exact ρ.traceNorm_toOp

/-- A quantum state is **faithful** (full-rank) when its operator is injective — equivalently, has
trivial kernel. In infinite dimensions a faithful density is *not* bounded below: it is compact with
eigenvalues accumulating at `0`, so `ρ^{-1}` and `ρ^{-1/2}` are unbounded operators. This is the
correct infinite-dimensional analogue of "full-rank density matrix". -/
def Faithful (ρ : QState H) : Prop := Function.Injective ρ.toOp

end QState

/-! ## The trace as a bounded linear functional -/

/-- The **trace as a continuous linear functional** on trace-class operators, `T ↦ tr T`, bounded by
`|tr T| ≤ ‖T‖₁ = ‖T‖`. This is the pairing underlying expectation values, and — differentiated along
a `QuantumStatisticalModel` — it produces the vanishing-first-moment (traceless-tangent) constraint
that is the quantum analogue of `score_expectation_eq_zero`. -/
noncomputable def traceCLM : TraceClass H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun T => trace T.toOp
      map_add' := fun S T => by
        rw [TraceClass.toOp_add]; exact trace_add S.isTraceClass T.isTraceClass
      map_smul' := fun c T => by
        rw [TraceClass.toOp_smul]; simpa using trace_smul c T.toOp }
    1 fun T => by
      rw [one_mul]
      calc ‖trace T.toOp‖ ≤ traceNorm T.toOp := norm_trace_le_traceNorm T.toOp T.isTraceClass
        _ = ‖T‖ := (TraceClass.norm_def T).symm

@[simp] lemma traceCLM_apply (T : TraceClass H) : traceCLM T = trace T.toOp := rfl

end Spectra.InformationGeometry.Quantum

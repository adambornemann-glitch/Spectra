/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Complete
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Rank-one trace-class operators and separation of the trace pairing

The rank-one operators `|x⟩⟨x| = rankOne ℂ x x` are the simplest trace-class operators, and they
**separate** the trace pairing `T(H) × B(H) → ℂ`, `(ρ, C) ↦ tr(ρ C)`: if `tr(ρ C) = 0` for every
trace-class `ρ`, then `C = 0`.

This is the analytic core of the duality `B(H) = (T(H))*`, and it is exactly what upgrades the
Heisenberg-dual theory in `Petz/Dual.lean` from "unital ⟹ trace-preserving" to the full equivalence
(a trace-preserving channel has a *unital* dual).

## Main definitions

* `rankOneTC x` — the positive rank-one operator `|x⟩⟨x|` packaged as an element of `TraceClass H`.

## Main results

* `isTraceClass_rankOneSelf` — `|x⟩⟨x|` is trace-class (its positive trace is Parseval-summable).
* `trace_rankOneSelf_comp` — `tr(|x⟩⟨x| · C) = ⟪x, C x⟫`.
* `eq_zero_of_forall_trace_toOp_mul_eq_zero` — **separation**: `(∀ ρ, tr(ρ C) = 0) → C = 0`.
-/

namespace Spectra.QuantumMechanics.Channels

open ContinuousLinearMap RCLike InnerProductSpace
open scoped InnerProductSpace ENNReal NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The rank-one operator `|x⟩⟨x|` is positive. -/
lemma rankOneSelf_nonneg (x : H) : (0 : H →L[ℂ] H) ≤ rankOne ℂ x x :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (InnerProductSpace.isPositive_rankOne_self x)

/-- **The trace of a rank-one operator** `tr(|u⟩⟨v|) = ⟪v, u⟫` (Parseval over the canonical
basis). -/
lemma trace_rankOne (u v : H) : trace (rankOne ℂ u v) = ⟪v, u⟫_ℂ := by
  change ∑' i, ⟪stdHilbertBasis H i, rankOne ℂ u v (stdHilbertBasis H i)⟫_ℂ = ⟪v, u⟫_ℂ
  simp_rw [rankOne_apply, inner_smul_right]
  exact (stdHilbertBasis H).tsum_inner_mul_inner v u

/-- `|x⟩⟨x|` is trace-class: its positive trace `∑ᵢ |⟪x, eᵢ⟫|²` is Parseval-summable, hence
finite. -/
lemma isTraceClass_rankOneSelf (x : H) : IsTraceClass (rankOne ℂ x x) := by
  have hpos := rankOneSelf_nonneg x
  have hsum : Summable fun i => re (⟪x, stdHilbertBasis H i⟫_ℂ * ⟪stdHilbertBasis H i, x⟫_ℂ) :=
    ((stdHilbertBasis H).summable_inner_mul_inner x x).map Complex.reCLM Complex.reCLM.continuous
  change posTrace (stdHilbertBasis H) (absOp (rankOne ℂ x x)) ≠ ⊤
  rw [absOp_of_nonneg hpos, posTrace_eq_tsum_ofReal (stdHilbertBasis H) hpos]
  have hsummand : ∀ i, re ⟪stdHilbertBasis H i, rankOne ℂ x x (stdHilbertBasis H i)⟫_ℂ
      = re (⟪x, stdHilbertBasis H i⟫_ℂ * ⟪stdHilbertBasis H i, x⟫_ℂ) := by
    intro i
    rw [rankOne_apply, inner_smul_right]
  simp_rw [hsummand]
  exact hsum.tsum_ofReal_ne_top

/-- The positive rank-one operator `|x⟩⟨x|` as an element of `TraceClass H`. -/
noncomputable def rankOneTC (x : H) : TraceClass H :=
  ⟨rankOne ℂ x x, (mem_traceClassSubmodule).2 (isTraceClass_rankOneSelf x)⟩

@[simp] lemma rankOneTC_toOp (x : H) : (rankOneTC x).toOp = rankOne ℂ x x := rfl

/-- **The trace pairing against a rank-one operator** reads off the quadratic form:
`tr(|x⟩⟨x| · C) = ⟪x, C x⟫`. -/
lemma trace_rankOneSelf_comp (x : H) (C : H →L[ℂ] H) :
    trace (rankOne ℂ x x * C) = ⟪x, C x⟫_ℂ := by
  rw [mul_def, InnerProductSpace.rankOne_comp, trace_rankOne, adjoint_inner_left]

/-- **Separation of the trace pairing.** If `tr(ρ · C) = 0` for every trace-class `ρ`, then `C = 0`.
The rank-one operators `|x⟩⟨x|` witness the whole quadratic form `⟪x, C x⟫`, which over `ℂ`
determines `C`. This is the faithfulness of the pairing `T(H) × B(H) → ℂ` underlying
`B(H) = (T(H))*`. -/
theorem eq_zero_of_forall_trace_toOp_mul_eq_zero {C : H →L[ℂ] H}
    (h : ∀ ρ : TraceClass H, trace (ρ.toOp * C) = 0) : C = 0 := by
  have hC : ∀ x : H, ⟪x, C x⟫_ℂ = 0 := by
    intro x
    have hρ := h (rankOneTC x)
    rwa [rankOneTC_toOp, trace_rankOneSelf_comp] at hρ
  have hC' : ∀ x : H, ⟪C x, x⟫_ℂ = 0 := by
    intro x
    rw [← inner_conj_symm, hC x, map_zero]
  have h0 : (C : H →ₗ[ℂ] H) = 0 := (inner_map_self_eq_zero _).mp hC'
  ext x
  exact LinearMap.congr_fun h0 x

/-- **The trace pairing determines a bounded operator.** If `tr(ρ · A) = tr(ρ · B)` for every
trace-class `ρ`, then `A = B` — the pairing `T(H) × B(H) → ℂ` is nondegenerate on the `B(H)`
side. -/
theorem eq_of_forall_trace_toOp_mul_eq {A B : H →L[ℂ] H}
    (h : ∀ ρ : TraceClass H, trace (ρ.toOp * A) = trace (ρ.toOp * B)) : A = B := by
  have hAB : ∀ x : H, ⟪x, A x⟫_ℂ = ⟪x, B x⟫_ℂ := by
    intro x
    have hx := h (rankOneTC x)
    rwa [rankOneTC_toOp, trace_rankOneSelf_comp, trace_rankOneSelf_comp] at hx
  have hAB' : ∀ x : H, ⟪A x, x⟫_ℂ = ⟪B x, x⟫_ℂ := by
    intro x
    have hx := congrArg (starRingEnd ℂ) (hAB x)
    rwa [inner_conj_symm, inner_conj_symm] at hx
  have h0 : (A : H →ₗ[ℂ] H) = (B : H →ₗ[ℂ] H) := (ext_inner_map _ _).mp hAB'
  ext x
  exact LinearMap.congr_fun h0 x

end Spectra.QuantumMechanics.Channels

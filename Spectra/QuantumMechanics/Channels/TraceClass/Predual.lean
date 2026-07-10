/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.RankOne
import Spectra.QuantumMechanics.Channels.TraceClass.Cyclic
import Spectra.QuantumMechanics.Channels.TraceClass.Product
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Stage J — the trace pairing embeds `B(H)` into the dual of `T(H)`

Each bounded operator `B` gives a bounded linear functional on the trace-class operators,
`traceFunctional B : T ↦ tr(B T)`, with `‖traceFunctional B‖ = ‖B‖`.  The map
`B ↦ traceFunctional B` is therefore an **isometric linear embedding** `B(H) ↪ (T(H))*` — the
concrete `B(H)`-into-predual-dual direction of the duality `B(H) = (T(H))*`.

Boundedness is `norm_trace_comp_le` (`|tr(BT)| ≤ ‖B‖ ‖T‖₁`).  Injectivity is the rank-one separation
of the pairing (`eq_of_forall_trace_toOp_mul_eq`).  The isometry `‖traceFunctional B‖ = ‖B‖` uses
the unit rank-one witnesses `T = |û⟩⟨v̂|` (`‖T‖₁ = 1`), for which `tr(B T) = ⟪v̂, B û⟫` recovers
`‖B u‖`.

The reverse (surjectivity: every bounded functional on `T(H)` is `tr(B · )`) needs the trace-norm
density of the finite-rank operators and is not proved here.

## Main definitions

* `traceFunctional B` — the functional `T ↦ tr(B T)` in `(T(H))* = TraceClass H →L[ℂ] ℂ`.
* `traceDualₗᵢ` — the isometric embedding `B(H) ↪ (T(H))*`, `B ↦ traceFunctional B`.

## Main results

* `norm_traceFunctional_le` / `traceFunctional_injective` — boundedness and injectivity.
* `traceNorm_rankOne_of_unit` — `‖ |u⟩⟨v| ‖₁ = 1` for unit vectors.
* `norm_traceFunctional` — **`‖traceFunctional B‖ = ‖B‖`** (the isometry).
-/

open ContinuousLinearMap RCLike InnerProductSpace
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The trace pairing as a bounded functional -/

/-- The bounded linear functional `T ↦ tr(B T)` on the trace-class operators. -/
noncomputable def traceFunctional (B : H →L[ℂ] H) : TraceClass H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun T => trace (B ∘L T.toOp)
      map_add' := fun S T => by
        rw [TraceClass.toOp_add, ContinuousLinearMap.comp_add,
          trace_add (IsTraceClass.comp_left S.isTraceClass B)
            (IsTraceClass.comp_left T.isTraceClass B)]
      map_smul' := fun c T => by
        simp only [TraceClass.toOp_smul, ContinuousLinearMap.comp_smul, trace_smul,
          RingHom.id_apply, smul_eq_mul] }
    ‖B‖ fun T => by
      rw [TraceClass.norm_def]
      exact norm_trace_comp_le B T.toOp T.isTraceClass

@[simp] lemma traceFunctional_apply (B : H →L[ℂ] H) (T : TraceClass H) :
    traceFunctional B T = trace (B ∘L T.toOp) := rfl

/-- `‖traceFunctional B‖ ≤ ‖B‖`. -/
lemma norm_traceFunctional_le (B : H →L[ℂ] H) : ‖traceFunctional B‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg B) _

/-- **The trace pairing is faithful in `B`:** `B ↦ traceFunctional B` is injective.  If
`tr(A T) = tr(B T)` for every trace-class `T`, then `A = B` (rank-one separation). -/
theorem traceFunctional_injective :
    Function.Injective (traceFunctional : (H →L[ℂ] H) → TraceClass H →L[ℂ] ℂ) := by
  intro A B hAB
  refine eq_of_forall_trace_toOp_mul_eq fun ρ => ?_
  have hval := DFunLike.congr_fun hAB ρ
  rw [traceFunctional_apply, traceFunctional_apply] at hval
  have hcyc : ∀ C : H →L[ℂ] H, trace (ρ.toOp * C) = trace (C ∘L ρ.toOp) := fun C => by
    rw [ContinuousLinearMap.mul_def]; exact trace_comp_comm ρ.isTraceClass C
  rw [hcyc A, hcyc B]
  exact hval

/-! ## The unit rank-one operator: modulus, trace class, and trace norm -/

/-- **`| |u⟩⟨v| | = |v⟩⟨v|`** for unit vectors.  Since `|u⟩⟨v|⋆ |u⟩⟨v| = |v⟩⟨v|` is a projection and
the modulus is the unique nonnegative square root of `|u⟩⟨v|⋆ |u⟩⟨v|`. -/
theorem absOp_rankOne_of_unit {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    absOp (rankOne ℂ u v) = rankOne ℂ v v := by
  have hvv : (inner ℂ u u : ℂ) = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hSS : star (rankOne ℂ u v) * rankOne ℂ u v = rankOne ℂ v v := by
    rw [star_eq_adjoint, InnerProductSpace.adjoint_rankOne, ContinuousLinearMap.mul_def,
      InnerProductSpace.rankOne_comp_rankOne, hvv, one_smul]
  exact (CFC.mul_self_eq_mul_self_iff (absOp (rankOne ℂ u v)) (rankOne ℂ v v)
    (absOp_nonneg _) (rankOneSelf_nonneg v)).mp
    (by rw [absOp_mul_absOp, hSS, isIdempotentElem_rankOne_self hv])

/-- The unit rank-one `|u⟩⟨v|` is trace class. -/
theorem isTraceClass_rankOne_of_unit {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    IsTraceClass (rankOne ℂ u v) := by
  rw [← isTraceClass_absOp, absOp_rankOne_of_unit hu hv]
  exact isTraceClass_rankOneSelf v

/-- **`‖ |u⟩⟨v| ‖₁ = 1`** for unit vectors `u, v` (trace of the projection `|v⟩⟨v|`). -/
theorem traceNorm_rankOne_of_unit {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    traceNorm (rankOne ℂ u v) = 1 := by
  rw [traceNorm_eq (stdHilbertBasis H), absOp_rankOne_of_unit hu hv]
  have hpt : ((posTrace (stdHilbertBasis H) (rankOne ℂ v v)).toReal : ℂ) = 1 := by
    rw [← trace_of_nonneg (rankOneSelf_nonneg v) (stdHilbertBasis H), trace_rankOne,
      inner_self_eq_norm_sq_to_K, hv]; norm_num
  exact_mod_cast hpt

/-! ## The isometry `‖traceFunctional B‖ = ‖B‖` -/

/-- The unit rank-one `|u⟩⟨v|` packaged as an element of `TraceClass H`. -/
noncomputable def rankOneTCunit {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : TraceClass H :=
  ⟨rankOne ℂ u v, (mem_traceClassSubmodule).2 (isTraceClass_rankOne_of_unit hu hv)⟩

@[simp] lemma rankOneTCunit_toOp {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (rankOneTCunit hu hv).toOp = rankOne ℂ u v := rfl

/-- **The trace pairing embeds `B(H)` isometrically:** `‖traceFunctional B‖ = ‖B‖`.  For `≥`, the
unit witness `T = |p⟩⟨q|` with `p = u/‖u‖`, `q = Bu/‖Bu‖` has `‖T‖₁ = 1` and
`tr(B T) = ⟪q, B p⟫ = ‖Bu‖/‖u‖`, so `‖Bu‖ ≤ ‖traceFunctional B‖ · ‖u‖`. -/
theorem norm_traceFunctional (B : H →L[ℂ] H) : ‖traceFunctional B‖ = ‖B‖ := by
  refine le_antisymm (norm_traceFunctional_le B) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  rcases eq_or_ne (B u) 0 with hBu | hBu
  · rw [hBu, norm_zero]; positivity
  have hu0 : u ≠ 0 := fun h => hBu (by rw [h, map_zero])
  have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hBun : (0 : ℝ) < ‖B u‖ := norm_pos_iff.mpr hBu
  set p : H := ((‖u‖⁻¹ : ℝ) : ℂ) • u with hpdef
  set q : H := ((‖B u‖⁻¹ : ℝ) : ℂ) • B u with hqdef
  have hpn : ‖p‖ = 1 := by
    rw [hpdef, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hun).le,
      inv_mul_cancel₀ hun.ne']
  have hqn : ‖q‖ = 1 := by
    rw [hqdef, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hBun).le,
      inv_mul_cancel₀ hBun.ne']
  have hTnorm : ‖rankOneTCunit hpn hqn‖ = 1 := by
    rw [TraceClass.norm_def, rankOneTCunit_toOp]; exact traceNorm_rankOne_of_unit hpn hqn
  -- `tr(B |p⟩⟨q|) = ⟪q, B p⟫ = ‖Bu‖/‖u‖`.
  have _hBc : (‖B u‖ : ℂ) ≠ 0 := by exact_mod_cast hBun.ne'
  have _huc : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast hun.ne'
  have hinner : (⟪B u, B u⟫_ℂ) = ((‖B u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hreal : (‖B u‖⁻¹ * (‖u‖⁻¹ * ‖B u‖ ^ 2) : ℝ) = ‖B u‖ / ‖u‖ := by
    field_simp
  have heval : traceFunctional B (rankOneTCunit hpn hqn) = ((‖B u‖ / ‖u‖ : ℝ) : ℂ) := by
    rw [traceFunctional_apply, rankOneTCunit_toOp, InnerProductSpace.comp_rankOne, trace_rankOne,
      hqdef, hpdef, map_smul, inner_smul_left, inner_smul_right, hinner, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal]
  have hb := (traceFunctional B).le_opNorm (rankOneTCunit hpn hqn)
  rw [heval, hTnorm, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hb
  rw [div_le_iff₀ hun] at hb
  linarith

/-- **The trace pairing as an isometric embedding** `B(H) ↪ (T(H))*`, `B ↦ (T ↦ tr(B T))`. -/
noncomputable def traceDualₗᵢ : (H →L[ℂ] H) →ₗᵢ[ℂ] (TraceClass H →L[ℂ] ℂ) where
  toFun := traceFunctional
  map_add' A B := by
    ext T
    simp only [traceFunctional_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_comp,
      trace_add (IsTraceClass.comp_left T.isTraceClass A) (IsTraceClass.comp_left T.isTraceClass B)]
  map_smul' c B := by
    ext T
    simp only [traceFunctional_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smul_comp, trace_smul, RingHom.id_apply, smul_eq_mul]
  norm_map' := norm_traceFunctional

end Spectra.QuantumMechanics.Channels

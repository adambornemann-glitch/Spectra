/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Trace

/-!
# Stage E — the triangle inequality for the trace norm

`‖S + T‖₁ ≤ ‖S‖₁ + ‖T‖₁`.  The proof works in `ℝ≥0∞` first (so `∞` is handled gracefully and no
closure-under-`+` prerequisite is needed) and goes through the polar decomposition of `S + T` with a
**single fixed** partial isometry `W = polarIsometry (S + T)`, using `|S + T| = W⋆ (S + T)`:
`⟪eᵢ, |S+T| eᵢ⟫ = ⟪W eᵢ, S eᵢ⟫ + ⟪W eᵢ, T eᵢ⟫`, and each `∑ᵢ ‖⟪W eᵢ, · eᵢ⟫‖` is bounded by the trace
norm via `tsum_norm_inner_comp_le` (`‖W‖ ≤ 1`).  No supremum over contractions is taken.

## Main results

* `posTrace_absOp_add_le` — `tr |S+T| ≤ tr |S| + tr |T|` in `ℝ≥0∞` (unconditional).
* `isTraceClass_add` — the trace-class operators are closed under addition.
* `traceNorm_add_le` — the triangle inequality `‖S + T‖₁ ≤ ‖S‖₁ + ‖T‖₁` (for trace-class `S, T`).

## Context

Fifth brick of the trace-class / von Neumann predual development (the discharge-first route to the
Tomita–Takesaki fundamental theorem).  Together with absolute homogeneity (`traceNorm_smul`) and
`norm_le_traceNorm` (Stage F), this makes the trace-class operators a normed space; Banach
completeness is the final brick.
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `ofReal ‖T‖₁ = tr |T|` for trace-class `T` (the `ℝ≥0∞` trace is finite, so `toReal` inverts). -/
private lemma ofReal_traceNorm {X : H →L[ℂ] H} (hX : IsTraceClass X) :
    ENNReal.ofReal (traceNorm X) = posTrace (stdHilbertBasis H) (absOp X) :=
  ENNReal.ofReal_toReal hX

/-- **`tr |S + T| ≤ tr |S| + tr |T|`** in `ℝ≥0∞`, unconditional.  When either `S` or `T` is not
trace-class the right-hand side is `∞`; otherwise, with `W = polarIsometry (S + T)`, each diagonal
`re ⟪eᵢ, |S+T| eᵢ⟫ = re (⟪W eᵢ, S eᵢ⟫ + ⟪W eᵢ, T eᵢ⟫)` is `≤ ‖⟪W eᵢ, S eᵢ⟫‖ + ‖⟪W eᵢ, T eᵢ⟫‖`, and
the two sums are bounded by `‖S‖₁`, `‖T‖₁` (`tsum_norm_inner_comp_le`, `‖W‖ ≤ 1`). -/
theorem posTrace_absOp_add_le (S T : H →L[ℂ] H) :
    posTrace (stdHilbertBasis H) (absOp (S + T))
      ≤ posTrace (stdHilbertBasis H) (absOp S) + posTrace (stdHilbertBasis H) (absOp T) := by
  by_cases hS : IsTraceClass S
  · by_cases hT : IsTraceClass T
    · set W := polarIsometry (S + T) with _hWdef
      have hWpolar : (W†) ∘L (S + T) = absOp (S + T) := polarIsometry_adjoint_comp (S + T)
      have hW1 : ‖W‖ ≤ 1 := norm_polarIsometry_le_one (S + T)
      have hterm : ∀ i, re ⟪stdHilbertBasis H i, absOp (S + T) (stdHilbertBasis H i)⟫_ℂ
          ≤ ‖⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ‖
            + ‖⟪W (stdHilbertBasis H i), T (stdHilbertBasis H i)⟫_ℂ‖ := by
        intro i
        have hsplit : ⟪stdHilbertBasis H i, absOp (S + T) (stdHilbertBasis H i)⟫_ℂ
            = ⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ
              + ⟪W (stdHilbertBasis H i), T (stdHilbertBasis H i)⟫_ℂ := by
          rw [← hWpolar, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, map_add,
            inner_add_right, adjoint_inner_right, adjoint_inner_right]
        rw [hsplit]
        exact (re_le_norm _).trans (norm_add_le _ _)
      calc posTrace (stdHilbertBasis H) (absOp (S + T))
          = ∑' i, ENNReal.ofReal
              (re ⟪stdHilbertBasis H i, absOp (S + T) (stdHilbertBasis H i)⟫_ℂ) :=
            posTrace_eq_tsum_ofReal (stdHilbertBasis H) (absOp_nonneg (S + T))
        _ ≤ ∑' i, ENNReal.ofReal (‖⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ‖
              + ‖⟪W (stdHilbertBasis H i), T (stdHilbertBasis H i)⟫_ℂ‖) :=
            ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (hterm i)
        _ = ∑' i, (ENNReal.ofReal ‖⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ‖
              + ENNReal.ofReal ‖⟪W (stdHilbertBasis H i), T (stdHilbertBasis H i)⟫_ℂ‖) :=
            tsum_congr fun i => ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
        _ = (∑' i, ENNReal.ofReal ‖⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ‖)
              + ∑' i, ENNReal.ofReal ‖⟪W (stdHilbertBasis H i), T (stdHilbertBasis H i)⟫_ℂ‖ :=
            ENNReal.tsum_add
        _ = ENNReal.ofReal (∑' i, ‖⟪W (stdHilbertBasis H i), S (stdHilbertBasis H i)⟫_ℂ‖)
              + ENNReal.ofReal (∑' i, ‖⟪W (stdHilbertBasis H i), T (stdHilbertBasis H i)⟫_ℂ‖) := by
            rw [ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _)
                (summable_norm_inner_comp W hS),
              ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _)
                (summable_norm_inner_comp W hT)]
        _ ≤ ENNReal.ofReal (traceNorm S) + ENNReal.ofReal (traceNorm T) :=
            add_le_add (ENNReal.ofReal_le_ofReal (tsum_norm_inner_comp_le hW1 hS))
              (ENNReal.ofReal_le_ofReal (tsum_norm_inner_comp_le hW1 hT))
        _ = posTrace (stdHilbertBasis H) (absOp S) + posTrace (stdHilbertBasis H) (absOp T) := by
            rw [ofReal_traceNorm hS, ofReal_traceNorm hT]
    · rw [show posTrace (stdHilbertBasis H) (absOp T) = ⊤ by
        simpa only [IsTraceClass, not_not] using hT, add_top]
      exact le_top
  · rw [show posTrace (stdHilbertBasis H) (absOp S) = ⊤ by
      simpa only [IsTraceClass, not_not] using hS, top_add]
    exact le_top

/-- The trace-class operators are closed under addition. -/
theorem isTraceClass_add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hS, hT⟩) (posTrace_absOp_add_le S T)

/-- **The triangle inequality** `‖S + T‖₁ ≤ ‖S‖₁ + ‖T‖₁` (for trace-class `S, T`; both hypotheses
are needed — off the trace-class world the junk value `0` of `‖·‖₁` breaks subadditivity). -/
theorem traceNorm_add_le {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  have hfin : posTrace (stdHilbertBasis H) (absOp S) + posTrace (stdHilbertBasis H) (absOp T) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hS, hT⟩
  calc traceNorm (S + T) = (posTrace (stdHilbertBasis H) (absOp (S + T))).toReal := rfl
    _ ≤ (posTrace (stdHilbertBasis H) (absOp S) + posTrace (stdHilbertBasis H) (absOp T)).toReal :=
        ENNReal.toReal_mono hfin (posTrace_absOp_add_le S T)
    _ = traceNorm S + traceNorm T := ENNReal.toReal_add hS hT

end Spectra.QuantumMechanics.Channels

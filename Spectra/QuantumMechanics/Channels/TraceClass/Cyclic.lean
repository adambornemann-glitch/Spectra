/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Trace
import Spectra.QuantumMechanics.Channels.TraceClass.HilbertSchmidt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Stage D — cyclicity of the trace `tr (A B) = tr (B A)`

For a trace-class operator `A` and a bounded operator `B` the trace is cyclic:
`tr (A B) = tr (B A)`. The engine is the Hilbert–Schmidt case: if `X, Y` are both Hilbert–Schmidt
then `tr (X Y) = tr (Y X)`, proved by expanding both diagonals in the basis, inserting a resolution
of the identity, and swapping the resulting absolutely-convergent double sum (Fubini).  The general
case factors `A = (U |A|^{1/2}) · |A|^{1/2}` into two Hilbert–Schmidt operators and rearranges
through the Hilbert–Schmidt case using that the Hilbert–Schmidt operators form a two-sided ideal.

## Main results

* `trace_comp_comm_hs` — `X, Y` Hilbert–Schmidt ⟹ `tr (X Y) = tr (Y X)`.
* `trace_comp_comm` — `A` trace-class, `B` bounded ⟹ `tr (A B) = tr (B A)`.

## Context

Fourth brick of the trace-class / von Neumann predual development (the discharge-first route to the
Tomita–Takesaki fundamental theorem), building on the complex trace (`Trace.lean`) and the
Hilbert–Schmidt ideal (`HilbertSchmidt.lean`).
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The double-sum absolute summability (Stage C's `C4`) -/

/-- For a Hilbert–Schmidt `Z`, the product family `(i, j) ↦ ‖⟪eⱼ, Z eᵢ⟫‖²` is summable: for each `i`
the `j`-sum is `‖Z eᵢ‖²` (Parseval), and `∑ᵢ ‖Z eᵢ‖² < ∞` since `Z` is Hilbert–Schmidt. -/
private lemma summable_prod_norm_inner_sq {ι : Type*} (b : HilbertBasis ι ℂ H) {Z : H →L[ℂ] H}
    (hZ : IsHilbertSchmidt Z) :
    Summable (fun p : ι × ι => ‖⟪b p.2, Z (b p.1)⟫_ℂ‖ ^ 2) := by
  rw [summable_prod_of_nonneg fun p => sq_nonneg _]
  refine ⟨fun i => (hasSum_norm_inner_sq b (Z (b i))).summable, ?_⟩
  have hZsum : Summable (fun i => ‖Z (b i)‖ ^ 2) := by
    have h := (isHilbertSchmidt_iff_summable b Z).mp hZ
    simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.summable_coe.mpr h
  exact hZsum.congr fun i => ((hasSum_norm_inner_sq b (Z (b i))).tsum_eq).symm

/-- **`C4`.** For `X, Y` Hilbert–Schmidt, the trace double-sum family
`(i, j) ↦ ⟪X⋆ eᵢ, eⱼ⟫ ⟪eⱼ, Y eᵢ⟫` is (absolutely) summable over `ι × ι`.  Each of the two factor
families is `ℓ²` (Parseval + Hilbert–Schmidt), so the product is summable by the
arithmetic–geometric comparison `|ab| ≤ (a² + b²)/2`. -/
private lemma summable_uncurry_trace_family {ι : Type*} (b : HilbertBasis ι ℂ H)
    {X Y : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (hY : IsHilbertSchmidt Y) :
    Summable (Function.uncurry (fun i j => ⟪(X†) (b i), b j⟫_ℂ * ⟪b j, Y (b i)⟫_ℂ)) := by
  apply Summable.of_norm
  have hXadj : IsHilbertSchmidt (X†) := (isHilbertSchmidt_adjoint X).mpr hX
  have hA : Summable (fun p : ι × ι => ‖⟪(X†) (b p.1), b p.2⟫_ℂ‖ ^ 2) :=
    (summable_prod_norm_inner_sq b hXadj).congr fun p => by rw [norm_inner_symm]
  have hB : Summable (fun p : ι × ι => ‖⟪b p.2, Y (b p.1)⟫_ℂ‖ ^ 2) :=
    summable_prod_norm_inner_sq b hY
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) ((hA.add hB).div_const 2)
  change ‖⟪(X†) (b p.1), b p.2⟫_ℂ * ⟪b p.2, Y (b p.1)⟫_ℂ‖
      ≤ (‖⟪(X†) (b p.1), b p.2⟫_ℂ‖ ^ 2 + ‖⟪b p.2, Y (b p.1)⟫_ℂ‖ ^ 2) / 2
  rw [norm_mul]
  nlinarith [sq_nonneg (‖⟪(X†) (b p.1), b p.2⟫_ℂ‖ - ‖⟪b p.2, Y (b p.1)⟫_ℂ‖),
    norm_nonneg ⟪(X†) (b p.1), b p.2⟫_ℂ, norm_nonneg ⟪b p.2, Y (b p.1)⟫_ℂ]

/-! ## Cyclicity -/

/-- **Cyclicity, Hilbert–Schmidt case.** For `X, Y` Hilbert–Schmidt, `tr (X Y) = tr (Y X)`.  Both
sides expand to the same absolutely convergent double sum
`∑ᵢⱼ ⟪X⋆ eᵢ, eⱼ⟫ ⟪eⱼ, Y eᵢ⟫`, related by Fubini. -/
theorem trace_comp_comm_hs {X Y : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (hY : IsHilbertSchmidt Y) :
    trace (X ∘L Y) = trace (Y ∘L X) := by
  have hXY : trace (X ∘L Y) = ∑' i, ∑' j, ⟪(X†) (stdHilbertBasis H i), stdHilbertBasis H j⟫_ℂ
      * ⟪stdHilbertBasis H j, Y (stdHilbertBasis H i)⟫_ℂ := by
    rw [trace]
    refine tsum_congr fun i => ?_
    rw [ContinuousLinearMap.comp_apply,
      ← adjoint_inner_left X (Y (stdHilbertBasis H i)) (stdHilbertBasis H i)]
    exact ((stdHilbertBasis H).tsum_inner_mul_inner ((X†) (stdHilbertBasis H i))
      (Y (stdHilbertBasis H i))).symm
  have hYX : trace (Y ∘L X) = ∑' j, ∑' i, ⟪(X†) (stdHilbertBasis H i), stdHilbertBasis H j⟫_ℂ
      * ⟪stdHilbertBasis H j, Y (stdHilbertBasis H i)⟫_ℂ := by
    rw [trace]
    refine tsum_congr fun j => ?_
    rw [ContinuousLinearMap.comp_apply,
      ← adjoint_inner_left Y (X (stdHilbertBasis H j)) (stdHilbertBasis H j),
      ← (stdHilbertBasis H).tsum_inner_mul_inner ((Y†) (stdHilbertBasis H j))
        (X (stdHilbertBasis H j))]
    refine tsum_congr fun i => ?_
    rw [adjoint_inner_left X (stdHilbertBasis H j) (stdHilbertBasis H i),
      ← adjoint_inner_left Y (stdHilbertBasis H i) (stdHilbertBasis H j), mul_comm]
  rw [hXY, hYX]
  exact ((summable_uncurry_trace_family (stdHilbertBasis H) hX hY).tsum_comm).symm

/-- **Cyclicity.** For a trace-class `A` and a bounded `B`, `tr (A B) = tr (B A)`.  Factor
`A = C D` with `C = U |A|^{1/2}`, `D = |A|^{1/2}` both Hilbert–Schmidt, and rearrange through the
Hilbert–Schmidt case, keeping the intermediate products Hilbert–Schmidt by the ideal property. -/
theorem trace_comp_comm {A : H →L[ℂ] H} (hA : IsTraceClass A) (B : H →L[ℂ] H) :
    trace (A ∘L B) = trace (B ∘L A) := by
  set D := sqrtOp (absOp A) with hD_def
  set C := polarIsometry A ∘L D with hC_def
  have hDD : D ∘L D = absOp A := by
    rw [hD_def, ← ContinuousLinearMap.mul_def, sqrtOp_mul_self (absOp A) (absOp_nonneg A)]
  have hCD : C ∘L D = A := by
    rw [hC_def, ContinuousLinearMap.comp_assoc, hDD, polar_decomposition]
  have hD_hs : IsHilbertSchmidt D := (isHilbertSchmidt_sqrtOp_absOp A).mpr hA
  have hC_hs : IsHilbertSchmidt C := hD_hs.comp_left (polarIsometry A)
  calc trace (A ∘L B)
      = trace (C ∘L (D ∘L B)) := by rw [← hCD, ContinuousLinearMap.comp_assoc]
    _ = trace ((D ∘L B) ∘L C) := trace_comp_comm_hs hC_hs (hD_hs.comp_right B)
    _ = trace (D ∘L (B ∘L C)) := by rw [ContinuousLinearMap.comp_assoc]
    _ = trace ((B ∘L C) ∘L D) := trace_comp_comm_hs hD_hs (hC_hs.comp_left B)
    _ = trace (B ∘L (C ∘L D)) := by rw [ContinuousLinearMap.comp_assoc]
    _ = trace (B ∘L A) := by rw [hCD]

end Spectra.QuantumMechanics.Channels

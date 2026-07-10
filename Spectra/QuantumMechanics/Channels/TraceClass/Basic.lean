/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.PolarDecomp
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Trace of a positive operator

For a positive bounded operator `T ≥ 0` on a complex Hilbert space, the trace is
`tr T = ∑ᵢ ⟪eᵢ, T eᵢ⟫`.  Writing `T = (T^{1/2})²` makes each summand manifestly non-negative:
`⟪eᵢ, T eᵢ⟫ = ‖T^{1/2} eᵢ‖²`.  This file establishes that per-term identity and defines the trace
of a positive operator as an `ℝ≥0∞`-valued sum (possibly `∞`).

## Main results

* `norm_sqrtOp_sq` — for `0 ≤ T`, `‖T^{1/2} x‖² = re ⟪x, T x⟫`.
* `posTrace b T` — `∑' i, ‖T^{1/2} (b i)‖²` in `ℝ≥0∞`, for a Hilbert basis `b`.

Basis-independence of `posTrace` (Parseval/Tonelli) and the trace norm `‖T‖₁ = tr |T|` are the next
bricks. Part of the trace-class / von Neumann predual development.
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The operator square root and the per-term identity -/

/-- `T^{1/2}` for a bounded operator, via the continuous functional calculus. -/
noncomputable def sqrtOp (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt T

lemma sqrtOp_nonneg (T : H →L[ℂ] H) : 0 ≤ sqrtOp T := CFC.sqrt_nonneg T

lemma sqrtOp_isSelfAdjoint (T : H →L[ℂ] H) : IsSelfAdjoint (sqrtOp T) :=
  (CFC.sqrt_nonneg T).isSelfAdjoint

/-- `T^{1/2} · T^{1/2} = T` for `0 ≤ T`. -/
lemma sqrtOp_mul_self (T : H →L[ℂ] H) (hT : 0 ≤ T) : sqrtOp T * sqrtOp T = T :=
  CFC.sqrt_mul_sqrt_self T hT

/-- `(T^{1/2})⋆ ∘ T^{1/2} = T` for `0 ≤ T`. -/
lemma sqrtOp_comp_self (T : H →L[ℂ] H) (hT : 0 ≤ T) : (sqrtOp T)† ∘L sqrtOp T = T := by
  rw [← star_eq_adjoint, ← mul_def, (sqrtOp_isSelfAdjoint T).star_eq]
  exact sqrtOp_mul_self T hT

/-- **The per-term trace identity.** For `0 ≤ T`, `‖T^{1/2} x‖² = re ⟪x, T x⟫` (and `⟪x, T x⟫` is
real since `T ≥ 0`, so this is the real number `⟪x, T x⟫`). This is what makes
`tr T = ∑ᵢ ⟪eᵢ, T eᵢ⟫ = ∑ᵢ ‖T^{1/2} eᵢ‖²` a sum of non-negative terms. -/
lemma norm_sqrtOp_sq (T : H →L[ℂ] H) (hT : 0 ≤ T) (x : H) :
    ‖sqrtOp T x‖ ^ 2 = re ⟪x, T x⟫_ℂ := by
  rw [apply_norm_sq_eq_inner_adjoint_right, sqrtOp_comp_self T hT]

/-! ## The trace of a positive operator -/

/-- The trace of a positive operator with respect to a Hilbert basis `b`, `∑' i, ‖T^{1/2} (b i)‖²`,
valued in `ℝ≥0∞` (possibly `∞`). Basis-independence is `posTrace_indep`. -/
noncomputable def posTrace {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, (‖sqrtOp T (b i)‖₊ : ℝ≥0∞) ^ 2

/-! ## Basis-independence (Parseval + Tonelli) -/

variable {ι : Type*}

omit [CompleteSpace H] in
/-- **Parseval** (real form): `∑' i, ‖⟪b i, v⟫‖² = ‖v‖²`. -/
lemma hasSum_norm_inner_sq (b : HilbertBasis ι ℂ H) (v : H) :
    HasSum (fun i => ‖⟪b i, v⟫_ℂ‖ ^ 2) (‖v‖ ^ 2) := by
  have key : (fun i => ‖⟪b i, v⟫_ℂ‖ ^ 2) = fun i => re (⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ) := by
    funext i
    rw [← inner_conj_symm v (b i), RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hsum : (‖v‖ ^ 2 : ℝ) = re ⟪v, v⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [key, hsum]
  have h := (b.hasSum_inner_mul_inner v v).mapL (RCLike.reCLM (K := ℂ))
  simpa only [RCLike.reCLM_apply] using h

omit [CompleteSpace H] in
/-- **Parseval** in `ℝ≥0∞`: `(‖v‖₊)² = ∑' i, (‖⟪b i, v⟫‖₊)²`. -/
lemma tsum_enorm_inner_sq (b : HilbertBasis ι ℂ H) (v : H) :
    (‖v‖₊ : ℝ≥0∞) ^ 2 = ∑' i, (‖⟪b i, v⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := by
  have hnn : HasSum (fun i => ‖⟪b i, v⟫_ℂ‖₊ ^ 2) (‖v‖₊ ^ 2) := by
    rw [← NNReal.hasSum_coe]; push_cast; exact hasSum_norm_inner_sq b v
  simp_rw [← ENNReal.coe_pow]
  rw [← ENNReal.coe_tsum hnn.summable, hnn.tsum_eq, ENNReal.coe_pow]

/-- For a **self-adjoint** `A`, the Hilbert–Schmidt sum `∑' ‖A eᵢ‖²` is basis-independent. -/
lemma tsum_enorm_apply_sq_comm {κ : Type*} (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H) :
    ∑' i, (‖A (b i)‖₊ : ℝ≥0∞) ^ 2 = ∑' j, (‖A (b' j)‖₊ : ℝ≥0∞) ^ 2 := by
  have hAadj : A† = A := by rw [← star_eq_adjoint, hA.star_eq]
  have h_sym : ∀ i j, ‖⟪b' j, A (b i)⟫_ℂ‖₊ = ‖⟪b i, A (b' j)⟫_ℂ‖₊ := by
    intro i j
    rw [← adjoint_inner_left A (b i) (b' j), hAadj, ← inner_conj_symm (b i) (A (b' j))]
    exact (nnnorm_star _).symm
  calc ∑' i, (‖A (b i)‖₊ : ℝ≥0∞) ^ 2
      = ∑' i, ∑' j, (‖⟪b' j, A (b i)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := by
        simp_rw [tsum_enorm_inner_sq b']
    _ = ∑' j, ∑' i, (‖⟪b' j, A (b i)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, (‖⟪b i, A (b' j)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun j => tsum_congr fun i =>
          congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ 2) (h_sym i j)
    _ = ∑' j, (‖A (b' j)‖₊ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun j => (tsum_enorm_inner_sq b (A (b' j))).symm

/-- **Basis-independence of the positive trace.** `posTrace` does not depend on the Hilbert basis.
-/
theorem posTrace_indep {κ : Type*} (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H)
    (T : H →L[ℂ] H) :
    posTrace b T = posTrace b' T :=
  tsum_enorm_apply_sq_comm (sqrtOp T) (sqrtOp_isSelfAdjoint T) b b'

end Spectra.QuantumMechanics.Channels

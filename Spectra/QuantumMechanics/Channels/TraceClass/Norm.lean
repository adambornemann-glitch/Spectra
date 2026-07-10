/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Basic

/-!
# The trace norm `‖T‖₁` and the trace-class predicate

For a bounded operator `T : H →L[ℂ] H` on a complex Hilbert space, the **trace norm** is
`‖T‖₁ = tr |T| = ∑ᵢ ⟪eᵢ, |T| eᵢ⟫`, where `|T| = (T⋆T)^{1/2}` is the modulus.  The positive trace
`posTrace` is basis-independent (`posTrace_indep`), so the norm is well-defined without reference to
a basis; we fix a canonical Hilbert basis `stdHilbertBasis H` via `exists_hilbertBasis` purely to
package it.

## Main definitions

* `Spectra.QuantumMechanics.Channels.stdHilbertBasis H` — a canonical Hilbert basis of `H`.
* `Spectra.QuantumMechanics.Channels.traceNorm T` — the trace norm `‖T‖₁ = (posTrace |T|).toReal`,
  valued in `ℝ` (junk value `0` when `T` is not trace-class, i.e. when `posTrace |T| = ∞`).
* `Spectra.QuantumMechanics.Channels.IsTraceClass T` — the predicate `posTrace |T| ≠ ∞`.

## Main results

* `traceNorm_eq` / `isTraceClass_iff` — basis-independence: the norm and the predicate agree with
  the positive trace of `|T|` computed in *any* Hilbert basis.
* `traceNorm_nonneg`, `traceNorm_zero`, `isTraceClass_zero`.
* `traceNorm_of_nonneg` — for `0 ≤ T` the trace norm is the honest trace `(posTrace T).toReal`.
* `traceNorm_absOp` — `‖ |T| ‖₁ = ‖T‖₁`.
* `traceNorm_smul` — the absolute homogeneity `‖c • T‖₁ = ‖c‖ · ‖T‖₁` (holds unconditionally, junk
  values included).
* `isTraceClass_iff_summable` — `T` is trace-class iff `∑ᵢ ‖|T|^{1/2} eᵢ‖²` is summable in `ℝ≥0`.

## Context

Second brick of the trace-class / von Neumann predual development (the discharge-first route to the
Tomita–Takesaki fundamental theorem), building on the basis-independence `posTrace_indep`.  The
remaining `‖·‖₁` core — the triangle inequality, the complex trace functional with `|tr T| ≤ ‖T‖₁`,
cyclicity `tr (AB) = tr (BA)`, and Banach completeness — is the next brick.
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

/-! ## Modulus algebra: scaling and the nonnegative/zero cases -/

/-- `|c • T| = ‖c‖ • |T|`. -/
lemma absOp_smul (c : ℂ) (T : H →L[ℂ] H) : absOp (c • T) = ‖c‖ • absOp T := by
  simp only [absOp, CFC.abs_smul]

/-- `|0| = 0`. -/
@[simp] lemma absOp_zero : absOp (0 : H →L[ℂ] H) = 0 := CFC.abs_zero

/-- `|T| = T` for a positive operator. -/
lemma absOp_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) : absOp T = T := CFC.abs_of_nonneg T hT

/-- The modulus is idempotent: `| |T| | = |T|` since `|T| ≥ 0`. -/
@[simp] lemma absOp_absOp (T : H →L[ℂ] H) : absOp (absOp T) = absOp T :=
  absOp_of_nonneg (absOp_nonneg T)

/-! ## The positive trace as a sum of `re ⟪eᵢ, S eᵢ⟫`, and its behaviour under scaling -/

/-- For `0 ≤ S`, the positive trace is `∑ᵢ ⟪eᵢ, S eᵢ⟫` written through `ENNReal.ofReal` and the
per-term identity `‖S^{1/2} eᵢ‖² = re ⟪eᵢ, S eᵢ⟫`. -/
lemma posTrace_eq_tsum_ofReal (b : HilbertBasis ι ℂ H) {S : H →L[ℂ] H} (hS : 0 ≤ S) :
    posTrace b S = ∑' i, ENNReal.ofReal (re ⟪b i, S (b i)⟫_ℂ) := by
  simp only [posTrace]
  refine tsum_congr fun i => ?_
  have hcoe : (‖sqrtOp S (b i)‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖sqrtOp S (b i)‖ := by
    rw [show ‖sqrtOp S (b i)‖ = ((‖sqrtOp S (b i)‖₊ : ℝ≥0) : ℝ) from rfl, ENNReal.ofReal_coe_nnreal]
  rw [hcoe, ← ENNReal.ofReal_pow (norm_nonneg _), norm_sqrtOp_sq S hS (b i)]

/-- **Absolute homogeneity of the positive trace of the modulus.** `tr |c • T| = ‖c‖ · tr |T|` in
`ℝ≥0∞` (so `∞` is handled correctly). -/
lemma posTrace_absOp_smul (b : HilbertBasis ι ℂ H) (c : ℂ) (T : H →L[ℂ] H) :
    posTrace b (absOp (c • T)) = ENNReal.ofReal ‖c‖ * posTrace b (absOp T) := by
  rw [posTrace_eq_tsum_ofReal b (absOp_nonneg (c • T)),
      posTrace_eq_tsum_ofReal b (absOp_nonneg T), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [absOp_smul, ContinuousLinearMap.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_right, RCLike.re_ofReal_mul, ENNReal.ofReal_mul (norm_nonneg c)]

/-- `posTrace b 0 = 0`. -/
@[simp] lemma posTrace_zero (b : HilbertBasis ι ℂ H) : posTrace b (0 : H →L[ℂ] H) = 0 := by
  simp [posTrace, sqrtOp, CFC.sqrt_zero]

/-! ## The canonical basis, the trace norm, and the trace-class predicate -/

variable (H) in
/-- A canonical Hilbert basis of `H`, chosen via `exists_hilbertBasis`.  Its only role is to
package a basis-free trace: `posTrace` is basis-independent (`posTrace_indep`), so any choice
would do. -/
noncomputable def stdHilbertBasis : HilbertBasis (exists_hilbertBasis ℂ H).choose ℂ H :=
  (exists_hilbertBasis ℂ H).choose_spec.choose

/-- The **trace norm** `‖T‖₁ = tr |T|`, valued in `ℝ`.  Junk value `0` when `T` is not trace-class
(`posTrace |T| = ∞`); real lemmas about it are paired with `IsTraceClass`. -/
noncomputable def traceNorm (T : H →L[ℂ] H) : ℝ :=
  (posTrace (stdHilbertBasis H) (absOp T)).toReal

/-- `T` is **trace-class** when `tr |T| = ∑ᵢ ⟪eᵢ, |T| eᵢ⟫` is finite. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  posTrace (stdHilbertBasis H) (absOp T) ≠ ⊤

/-! ## Basis-independence bridges -/

/-- The trace norm equals the positive trace of `|T|` in *any* Hilbert basis. -/
lemma traceNorm_eq (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    traceNorm T = (posTrace b (absOp T)).toReal := by
  unfold traceNorm
  rw [posTrace_indep (stdHilbertBasis H) b (absOp T)]

/-- Trace-class is detected in *any* Hilbert basis. -/
lemma isTraceClass_iff (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    IsTraceClass T ↔ posTrace b (absOp T) ≠ ⊤ := by
  unfold IsTraceClass
  rw [posTrace_indep (stdHilbertBasis H) b (absOp T)]

/-! ## Elementary properties of the trace norm -/

/-- The trace norm is nonnegative. -/
lemma traceNorm_nonneg (T : H →L[ℂ] H) : 0 ≤ traceNorm T := ENNReal.toReal_nonneg

/-- `‖0‖₁ = 0`. -/
@[simp] lemma traceNorm_zero : traceNorm (0 : H →L[ℂ] H) = 0 := by
  unfold traceNorm
  rw [absOp_zero, posTrace_zero]
  simp

/-- The zero operator is trace-class. -/
lemma isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) := by
  unfold IsTraceClass
  rw [absOp_zero, posTrace_zero]
  exact ENNReal.zero_ne_top

/-- For a positive operator the trace norm is the honest trace `(posTrace T).toReal`. -/
lemma traceNorm_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) (b : HilbertBasis ι ℂ H) :
    traceNorm T = (posTrace b T).toReal := by
  rw [traceNorm_eq b, absOp_of_nonneg hT]

/-- `‖ |T| ‖₁ = ‖T‖₁`. -/
@[simp] lemma traceNorm_absOp (T : H →L[ℂ] H) : traceNorm (absOp T) = traceNorm T := by
  unfold traceNorm
  rw [absOp_absOp]

/-- Trace-class is invariant under taking the modulus. -/
@[simp] lemma isTraceClass_absOp (T : H →L[ℂ] H) : IsTraceClass (absOp T) ↔ IsTraceClass T := by
  unfold IsTraceClass
  rw [absOp_absOp]

/-- **Absolute homogeneity** of the trace norm: `‖c • T‖₁ = ‖c‖ · ‖T‖₁`.  Holds unconditionally
(including junk values: if `T` is not trace-class then both sides are `0` for `c = 0` and remain
equal for `c ≠ 0`). -/
lemma traceNorm_smul (c : ℂ) (T : H →L[ℂ] H) : traceNorm (c • T) = ‖c‖ * traceNorm T := by
  unfold traceNorm
  rw [posTrace_absOp_smul (stdHilbertBasis H) c T, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (norm_nonneg c)]

/-- `T` is trace-class iff the Hilbert–Schmidt sum `∑ᵢ ‖|T|^{1/2} eᵢ‖²` is summable in `ℝ≥0`. -/
lemma isTraceClass_iff_summable (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    IsTraceClass T ↔ Summable (fun i => ‖sqrtOp (absOp T) (b i)‖₊ ^ 2) := by
  rw [isTraceClass_iff b, ← ENNReal.tsum_coe_ne_top_iff_summable]
  simp only [posTrace, ENNReal.coe_pow]

end Spectra.QuantumMechanics.Channels

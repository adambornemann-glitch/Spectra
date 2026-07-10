/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Norm
import Spectra.QuantumMechanics.Channels.TraceClass.PartialIsometry

/-!
# Stage C — the Hilbert–Schmidt ideal

A minimal Hilbert–Schmidt toolkit for the trace-class hard core: the predicate `IsHilbertSchmidt`
(`∑ᵢ ‖A eᵢ‖² < ∞`), its basis-independence, and the two-sided-ideal structure.  This is **not** a
packaged Hilbert-space structure (no HS inner product, no completeness) — only the predicate and
the summability facts needed for cyclicity `tr (AB) = tr (BA)` (Stage D), where `A` trace-class
factors as `A = (U |A|^{1/2})·(|A|^{1/2})` with both factors Hilbert–Schmidt.

## Main results

* `IsHilbertSchmidt A` — `∑ᵢ ‖A eᵢ‖² ≠ ∞`, packaged over `stdHilbertBasis` but basis-independent.
* `hsSum_adjoint_swap` / `hsSum_indep` — the adjoint cross-swap and basis-independence of
  `∑ᵢ ‖A eᵢ‖²`.
* `isHilbertSchmidt_iff` / `isHilbertSchmidt_iff_summable` — basis-independence.
* `isHilbertSchmidt_adjoint` — `A⋆` is Hilbert–Schmidt iff `A` is.
* `isHilbertSchmidt_sqrtOp_absOp` — `|A|^{1/2}` is Hilbert–Schmidt iff `A` is **trace-class**
  (definitionally `tr |A|`); the factorization input for cyclicity.
* `IsHilbertSchmidt.comp_left` / `comp_right` — the Hilbert–Schmidt operators form a two-sided
  ideal.
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι κ : Type*}

/-- **Adjoint cross-swap** of the Hilbert–Schmidt sum: `∑ᵢ ‖A cᵢ‖² = ∑ⱼ ‖A⋆ c'ⱼ‖²` for any two
Hilbert bases (Parseval + Tonelli + `⟪c'ⱼ, A cᵢ⟫ = conj ⟪cᵢ, A⋆ c'ⱼ⟫`). -/
theorem hsSum_adjoint_swap (A : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H) :
    ∑' i, (‖A (b i)‖₊ : ℝ≥0∞) ^ 2 = ∑' j, (‖(A†) (b' j)‖₊ : ℝ≥0∞) ^ 2 := by
  have h_sym : ∀ i j, ‖⟪b' j, A (b i)⟫_ℂ‖₊ = ‖⟪b i, (A†) (b' j)⟫_ℂ‖₊ := by
    intro i j
    rw [← adjoint_inner_left A (b i) (b' j), ← inner_conj_symm (b i) ((A†) (b' j)),
      RCLike.nnnorm_conj]
  calc ∑' i, (‖A (b i)‖₊ : ℝ≥0∞) ^ 2
      = ∑' i, ∑' j, (‖⟪b' j, A (b i)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := by simp_rw [tsum_enorm_inner_sq b']
    _ = ∑' j, ∑' i, (‖⟪b' j, A (b i)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, (‖⟪b i, (A†) (b' j)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun j => tsum_congr fun i =>
          congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ 2) (h_sym i j)
    _ = ∑' j, (‖(A†) (b' j)‖₊ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun j => (tsum_enorm_inner_sq b ((A†) (b' j))).symm

/-- **Basis-independence of the Hilbert–Schmidt sum** for any bounded `A`. -/
theorem hsSum_indep (A : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) (b' : HilbertBasis κ ℂ H) :
    ∑' i, (‖A (b i)‖₊ : ℝ≥0∞) ^ 2 = ∑' j, (‖A (b' j)‖₊ : ℝ≥0∞) ^ 2 := by
  rw [hsSum_adjoint_swap A b b', ← hsSum_adjoint_swap A b' b']

/-- `A` is **Hilbert–Schmidt** when `∑ᵢ ‖A eᵢ‖² < ∞`.  Packaged over `stdHilbertBasis`; basis-free
by `isHilbertSchmidt_iff`. -/
def IsHilbertSchmidt (A : H →L[ℂ] H) : Prop :=
  ∑' i, (‖A (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤

/-- Hilbert–Schmidt is detected in *any* Hilbert basis. -/
lemma isHilbertSchmidt_iff (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) :
    IsHilbertSchmidt A ↔ ∑' i, (‖A (b i)‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ := by
  unfold IsHilbertSchmidt
  rw [hsSum_indep A (stdHilbertBasis H) b]

/-- `A` is Hilbert–Schmidt iff `∑ᵢ ‖A eᵢ‖²` is summable in `ℝ≥0`. -/
lemma isHilbertSchmidt_iff_summable (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) :
    IsHilbertSchmidt A ↔ Summable (fun i => ‖A (b i)‖₊ ^ 2) := by
  rw [isHilbertSchmidt_iff b, ← ENNReal.tsum_coe_ne_top_iff_summable]
  simp only [ENNReal.coe_pow]

/-- `A⋆` is Hilbert–Schmidt iff `A` is. -/
@[simp] lemma isHilbertSchmidt_adjoint (A : H →L[ℂ] H) :
    IsHilbertSchmidt (A†) ↔ IsHilbertSchmidt A := by
  unfold IsHilbertSchmidt
  rw [← tsum_enorm_apply_sq_adjoint A (stdHilbertBasis H)]

/-- **`|A|^{1/2}` is Hilbert–Schmidt iff `A` is trace-class** — definitionally, since
`∑ᵢ ‖|A|^{1/2} eᵢ‖² = tr |A|`.  The factorization input for cyclicity
(`A = (U |A|^{1/2})·(|A|^{1/2})`). -/
lemma isHilbertSchmidt_sqrtOp_absOp (A : H →L[ℂ] H) :
    IsHilbertSchmidt (sqrtOp (absOp A)) ↔ IsTraceClass A := Iff.rfl

/-! ## The two-sided ideal -/

omit [CompleteSpace H] in
/-- `‖(B ∘L A) x‖² ≤ ‖B‖² ‖A x‖²`, in `ℝ≥0∞`. -/
private lemma enorm_comp_le (A B : H →L[ℂ] H) (x : H) :
    (‖(B ∘L A) x‖₊ : ℝ≥0∞) ^ 2 ≤ (‖B‖₊ : ℝ≥0∞) ^ 2 * (‖A x‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : ‖(B ∘L A) x‖₊ ≤ ‖B‖₊ * ‖A x‖₊ := by
    rw [ContinuousLinearMap.comp_apply]; exact_mod_cast B.le_opNorm (A x)
  rw [← mul_pow]
  gcongr
  exact_mod_cast h1

/-- **Left ideal:** `B ∘L A` is Hilbert–Schmidt when `A` is and `B` is bounded. -/
lemma IsHilbertSchmidt.comp_left {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (B : H →L[ℂ] H) :
    IsHilbertSchmidt (B ∘L A) := by
  rw [isHilbertSchmidt_iff (stdHilbertBasis H)] at hA ⊢
  have hb : (‖B‖₊ : ℝ≥0∞) ^ 2 * ∑' i, (‖A (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hA
  have hle : ∑' i, (‖(B ∘L A) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2
      ≤ (‖B‖₊ : ℝ≥0∞) ^ 2 * ∑' i, (‖A (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun i => enorm_comp_le A B (stdHilbertBasis H i)
  exact (hle.trans_lt hb.lt_top).ne

/-- **Right ideal:** `A ∘L B` is Hilbert–Schmidt when `A` is and `B` is bounded. -/
lemma IsHilbertSchmidt.comp_right {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (B : H →L[ℂ] H) :
    IsHilbertSchmidt (A ∘L B) := by
  rw [← isHilbertSchmidt_adjoint, ContinuousLinearMap.adjoint_comp]
  exact ((isHilbertSchmidt_adjoint A).mpr hA).comp_left (B†)

end Spectra.QuantumMechanics.Channels

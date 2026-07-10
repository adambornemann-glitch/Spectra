/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.HilbertSchmidtNorm
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Hilbert–Schmidt and trace-class operators are compact

Every Hilbert–Schmidt operator — and hence every trace-class operator — on a Hilbert space is a
**compact operator**.  The proof is the textbook finite-rank approximation: a Hilbert–Schmidt `A` is
the operator-norm limit of its finite truncations `A ∘L Pₛ` (`Pₛ` the finite-rank projection onto
the span of the basis vectors indexed by `s`), each of which has finite-dimensional range and is
therefore compact; the tail bound `‖A - A ∘L Pₛ‖ ≤ (Hilbert–Schmidt tail) → 0` uses the
operator-norm-`≤`-Hilbert–Schmidt-norm inequality together with the summability of `∑ᵢ ‖A eᵢ‖²`.

## Main results

* `opNorm_le_hsNorm` — `‖A‖ ≤ ‖A‖₂` (operator norm bounded by the Hilbert–Schmidt norm).
* `IsHilbertSchmidt.isCompactOperator` — a Hilbert–Schmidt operator is compact.
* `IsTraceClass.isCompactOperator` — a trace-class operator is compact.
* `isCompactOperator_of_nonneg` — a positive trace-class operator is compact (the positive case,
  the form used downstream for density operators).
-/

open ContinuousLinearMap RCLike Filter Topology
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## An `ℓ²`-Cauchy–Schwarz for `tsum` -/

/-- **Cauchy–Schwarz for `ℓ²` sums.** For nonnegative real sequences `a, b` with `a²`, `b²`
summable, `∑ᵢ aᵢ bᵢ ≤ (∑ᵢ aᵢ²)^{1/2} (∑ᵢ bᵢ²)^{1/2}`. -/
private lemma tsum_mul_le_sqrt_mul_sqrt {ι : Type*} {a b : ι → ℝ} (hna : ∀ i, 0 ≤ a i)
    (hnb : ∀ i, 0 ≤ b i) (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    ∑' i, a i * b i ≤ Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, b i ^ 2) := by
  refine Real.tsum_le_of_sum_le (fun i => mul_nonneg (hna i) (hnb i)) fun s => ?_
  have hcs : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * ∑ i ∈ s, b i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s a b
  have hsa : ∑ i ∈ s, a i ^ 2 ≤ ∑' i, a i ^ 2 := Summable.sum_le_tsum s (fun i _ => sq_nonneg _) ha
  have hsb : ∑ i ∈ s, b i ^ 2 ≤ ∑' i, b i ^ 2 := Summable.sum_le_tsum s (fun i _ => sq_nonneg _) hb
  have hprod : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑' i, a i ^ 2) * ∑' i, b i ^ 2 :=
    hcs.trans (mul_le_mul hsa hsb (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (tsum_nonneg fun i => sq_nonneg _))
  calc ∑ i ∈ s, a i * b i
      = Real.sqrt ((∑ i ∈ s, a i * b i) ^ 2) :=
        (Real.sqrt_sq (Finset.sum_nonneg fun i _ => mul_nonneg (hna i) (hnb i))).symm
    _ ≤ Real.sqrt ((∑' i, a i ^ 2) * ∑' i, b i ^ 2) := Real.sqrt_le_sqrt hprod
    _ = Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, b i ^ 2) :=
        Real.sqrt_mul (tsum_nonneg fun i => sq_nonneg _) _

/-! ## The operator norm is bounded by the Hilbert–Schmidt norm -/

/-- The real Hilbert–Schmidt sum `∑' i, ‖A eᵢ‖²` is summable when `A` is Hilbert–Schmidt. -/
private lemma summable_norm_apply_sq {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) :
    Summable (fun i => ‖A (stdHilbertBasis H i)‖ ^ 2) := by
  have h := (isHilbertSchmidt_iff_summable (stdHilbertBasis H) A).mp hA
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.summable_coe.mpr h

/-- **The operator norm is bounded by the Hilbert–Schmidt norm:** `‖A‖ ≤ ‖A‖₂`.

For any `x`, `A x = ∑ᵢ ⟪eᵢ, x⟫ • A eᵢ`, so by the `ℓ²`-Cauchy–Schwarz on the diagonal and Parseval
`∑ᵢ ‖⟪eᵢ, x⟫‖² = ‖x‖²`, `‖A x‖ ≤ ∑ᵢ ‖⟪eᵢ, x⟫‖ · ‖A eᵢ‖ ≤ ‖x‖ · ‖A‖₂`. -/
lemma opNorm_le_hsNorm {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) : ‖A‖ ≤ hsNorm A := by
  refine A.opNorm_le_bound (hsNorm_nonneg A) fun x => ?_
  -- `A x = ∑ᵢ ⟪eᵢ, x⟫ • A eᵢ`.
  have hsum : HasSum (fun i => ⟪stdHilbertBasis H i, x⟫_ℂ • A (stdHilbertBasis H i)) (A x) := by
    have := A.hasSum ((stdHilbertBasis H).hasSum_repr x)
    simpa only [map_smul, (stdHilbertBasis H).repr_apply_apply] using this
  -- Summabilities of the two `ℓ²` sequences.
  have hAsummable : Summable (fun i => ‖A (stdHilbertBasis H i)‖ ^ 2) := summable_norm_apply_sq hA
  have hxsummable : Summable (fun i => ‖⟪stdHilbertBasis H i, x⟫_ℂ‖ ^ 2) :=
    (hasSum_norm_inner_sq (stdHilbertBasis H) x).summable
  -- The product sequence `‖⟪eᵢ, x⟫‖ · ‖A eᵢ‖` is summable, and its `tsum` bounds `‖A x‖`.
  have hprod_summable : Summable
      (fun i => ‖⟪stdHilbertBasis H i, x⟫_ℂ‖ * ‖A (stdHilbertBasis H i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun i => ?_) ((hxsummable.add hAsummable).div_const 2)
    nlinarith [sq_nonneg (‖⟪stdHilbertBasis H i, x⟫_ℂ‖ - ‖A (stdHilbertBasis H i)‖),
      norm_nonneg ⟪stdHilbertBasis H i, x⟫_ℂ, norm_nonneg (A (stdHilbertBasis H i))]
  have hnorm_le : ‖A x‖
      ≤ ∑' i, ‖⟪stdHilbertBasis H i, x⟫_ℂ‖ * ‖A (stdHilbertBasis H i)‖ := by
    refine hsum.norm_le_of_bounded hprod_summable.hasSum fun i => ?_
    rw [norm_smul]
  -- Cauchy–Schwarz and Parseval finish it.
  calc ‖A x‖
      ≤ ∑' i, ‖⟪stdHilbertBasis H i, x⟫_ℂ‖ * ‖A (stdHilbertBasis H i)‖ := hnorm_le
    _ ≤ Real.sqrt (∑' i, ‖⟪stdHilbertBasis H i, x⟫_ℂ‖ ^ 2)
          * Real.sqrt (∑' i, ‖A (stdHilbertBasis H i)‖ ^ 2) :=
        tsum_mul_le_sqrt_mul_sqrt (fun i => norm_nonneg _) (fun i => norm_nonneg _)
          hxsummable hAsummable
    _ = hsNorm A * ‖x‖ := by
        rw [(hasSum_norm_inner_sq (stdHilbertBasis H) x).tsum_eq, Real.sqrt_sq (norm_nonneg x),
          hsNorm_of_isHilbertSchmidt hA, mul_comm]

/-! ## The finite-rank truncation and its compactness -/

/-- The finite-rank **truncation** `Aₛ = A ∘L Pₛ`, written directly as the finite sum of rank-one
operators `x ↦ ⟪eᵢ, x⟫ • A eᵢ` over `i ∈ s`.  Its range lies in the span of `{A eᵢ : i ∈ s}`. -/
private noncomputable def hsTrunc (A : H →L[ℂ] H) (s : Finset (exists_hilbertBasis ℂ H).choose) :
    H →L[ℂ] H :=
  ∑ i ∈ s, (innerSL ℂ (stdHilbertBasis H i)).smulRight (A (stdHilbertBasis H i))

/-- `Aₛ x = ∑ᵢ∈ₛ ⟪eᵢ, x⟫ • A eᵢ`. -/
private lemma hsTrunc_apply (A : H →L[ℂ] H) (s : Finset (exists_hilbertBasis ℂ H).choose) (x : H) :
    hsTrunc A s x = ∑ i ∈ s, ⟪stdHilbertBasis H i, x⟫_ℂ • A (stdHilbertBasis H i) := by
  simp [hsTrunc, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

omit [CompleteSpace H] in
/-- A **rank-one operator** `x ↦ ⟪v, x⟫ • w` is compact: it factors through the locally compact
scalar field `ℂ` as `(c ↦ c • w) ∘L (innerSL ℂ v)`. -/
private lemma isCompactOperator_rankOne (v w : H) :
    IsCompactOperator ((innerSL ℂ v).smulRight w) := by
  have hfac : (innerSL ℂ v).smulRight w
      = ((ContinuousLinearMap.id ℂ ℂ).smulRight w) ∘L (innerSL ℂ v) := by
    ext x; simp [ContinuousLinearMap.smulRight_apply]
  rw [hfac]
  exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ v)).clm_comp
    ((ContinuousLinearMap.id ℂ ℂ).smulRight w)

/-- The truncation is a **compact operator**: a finite sum of rank-one operators. -/
private lemma hsTrunc_isCompactOperator (A : H →L[ℂ] H)
    (s : Finset (exists_hilbertBasis ℂ H).choose) : IsCompactOperator (hsTrunc A s) := by
  classical
  rw [hsTrunc]
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty]
      exact isCompactOperator_zero
  | insert i t hi ih =>
      rw [Finset.sum_insert hi]
      exact (isCompactOperator_rankOne (stdHilbertBasis H i) (A (stdHilbertBasis H i))).add ih

/-! ## The tail bound and the finite-rank approximation -/

open scoped Classical in
/-- On a basis vector `eⱼ`, the truncation reproduces it exactly inside `s` and kills it outside:
`Aₛ(eⱼ) = A eⱼ` for `j ∈ s` and `= 0` for `j ∉ s`. -/
private lemma hsTrunc_apply_basis (A : H →L[ℂ] H)
    (s : Finset (exists_hilbertBasis ℂ H).choose) (j : (exists_hilbertBasis ℂ H).choose) :
    hsTrunc A s (stdHilbertBasis H j)
      = if j ∈ s then A (stdHilbertBasis H j) else 0 := by
  rw [hsTrunc_apply]
  have hterm : ∀ i ∈ s, ⟪stdHilbertBasis H i, stdHilbertBasis H j⟫_ℂ • A (stdHilbertBasis H i)
      = if i = j then A (stdHilbertBasis H j) else 0 := by
    intro i _
    rcases eq_or_ne i j with rfl | hij
    · simp [(stdHilbertBasis H).orthonormal.1 i]
    · simp [(stdHilbertBasis H).orthonormal.2 hij, hij]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j]

/-- `(A - Aₛ) eⱼ = 0` for `j ∈ s`. -/
private lemma sub_hsTrunc_apply_basis_mem (A : H →L[ℂ] H)
    {s : Finset (exists_hilbertBasis ℂ H).choose} {j : (exists_hilbertBasis ℂ H).choose}
    (hj : j ∈ s) : (A - hsTrunc A s) (stdHilbertBasis H j) = 0 := by
  rw [ContinuousLinearMap.sub_apply, hsTrunc_apply_basis, if_pos hj, sub_self]

/-- `(A - Aₛ) eⱼ = A eⱼ` for `j ∉ s`. -/
private lemma sub_hsTrunc_apply_basis_not_mem (A : H →L[ℂ] H)
    {s : Finset (exists_hilbertBasis ℂ H).choose} {j : (exists_hilbertBasis ℂ H).choose}
    (hj : j ∉ s) : (A - hsTrunc A s) (stdHilbertBasis H j) = A (stdHilbertBasis H j) := by
  rw [ContinuousLinearMap.sub_apply, hsTrunc_apply_basis, if_neg hj, sub_zero]

/-- The **Hilbert–Schmidt tail sum** of `A - Aₛ`, in `ℝ≥0∞`, is the tail `∑_{j ∉ s} ‖A eⱼ‖²`. -/
private lemma tsum_enorm_sub_hsTrunc (A : H →L[ℂ] H)
    (s : Finset (exists_hilbertBasis ℂ H).choose) :
    ∑' j, (‖(A - hsTrunc A s) (stdHilbertBasis H j)‖₊ : ℝ≥0∞) ^ 2
      = ∑' j : ↥((s : Set (exists_hilbertBasis ℂ H).choose)ᶜ),
          (‖A (stdHilbertBasis H (j : _))‖₊ : ℝ≥0∞) ^ 2 := by
  classical
  rw [← ENNReal.sum_add_tsum_compl s
        (fun j => (‖(A - hsTrunc A s) (stdHilbertBasis H j)‖₊ : ℝ≥0∞) ^ 2)]
  have h0 : ∑ i ∈ s, (‖(A - hsTrunc A s) (stdHilbertBasis H i)‖₊ : ℝ≥0∞) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [sub_hsTrunc_apply_basis_mem A hi]; simp
  rw [h0, zero_add]
  refine tsum_congr fun j => ?_
  rw [sub_hsTrunc_apply_basis_not_mem A j.2]

/-! ## Hilbert–Schmidt operators are compact -/

/-- The (`ℝ≥0∞`-valued) Hilbert–Schmidt tail of `A`, `∑_{j ∉ s} ‖A eⱼ‖²`, which is the squared
Hilbert–Schmidt norm of `A - Aₛ` and tends to `0` as `s` grows. -/
private noncomputable def hsTail (A : H →L[ℂ] H) (s : Finset (exists_hilbertBasis ℂ H).choose) :
    ℝ≥0∞ :=
  ∑' j : ↥((s : Set (exists_hilbertBasis ℂ H).choose)ᶜ),
    (‖A (stdHilbertBasis H (j : _))‖₊ : ℝ≥0∞) ^ 2

/-- `A - Aₛ` is Hilbert–Schmidt when `A` is: its Hilbert–Schmidt sum is the tail of `A`'s. -/
private lemma isHilbertSchmidt_sub_hsTrunc {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (s : Finset (exists_hilbertBasis ℂ H).choose) : IsHilbertSchmidt (A - hsTrunc A s) := by
  have hle : ∑' j, (‖(A - hsTrunc A s) (stdHilbertBasis H j)‖₊ : ℝ≥0∞) ^ 2
      ≤ ∑' j, (‖A (stdHilbertBasis H j)‖₊ : ℝ≥0∞) ^ 2 := by
    rw [tsum_enorm_sub_hsTrunc A s]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective _
  exact ne_top_of_le_ne_top hA hle

/-- `hsNorm (A - Aₛ) = (hsTail A s).toReal ^ {1/2}`. -/
private lemma hsNorm_sub_hsTrunc (A : H →L[ℂ] H) (s : Finset (exists_hilbertBasis ℂ H).choose) :
    hsNorm (A - hsTrunc A s) = Real.sqrt (hsTail A s).toReal := by
  rw [hsNorm, tsum_enorm_sub_hsTrunc A s]; rfl

/-- **Every Hilbert–Schmidt operator is a compact operator.**

`A` is the operator-norm limit of its finite-rank truncations `Aₛ`: the tail bound
`‖A - Aₛ‖ ≤ ‖A - Aₛ‖₂ = (hsTail A s)^{1/2} → 0` (the last limit is `tendsto_tsum_compl_atTop_zero`)
places `A` in the closure of the compact operators. -/
theorem IsHilbertSchmidt.isCompactOperator {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) :
    IsCompactOperator A := by
  -- The truncations converge to `A` in operator norm.
  have htail0 : Tendsto (fun s => hsTail A s) atTop (𝓝 0) := by
    have hfin : ∑' j, (‖A (stdHilbertBasis H j)‖₊ : ℝ≥0∞) ^ 2 ≠ ⊤ := hA
    have h := ENNReal.tendsto_tsum_compl_atTop_zero hfin
    exact h.congr fun s => rfl
  have htailR0 : Tendsto (fun s => Real.sqrt (hsTail A s).toReal) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s => (hsTail A s).toReal) atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal (by simp)).comp htail0
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa only [Function.comp_def, Real.sqrt_zero] using h2
  have hnorm0 : Tendsto (fun s => ‖A - hsTrunc A s‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) htailR0
    rw [← hsNorm_sub_hsTrunc A s]
    exact opNorm_le_hsNorm (isHilbertSchmidt_sub_hsTrunc hA s)
  have htendsto : Tendsto (fun s => hsTrunc A s) atTop (𝓝 A) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hnorm0
  exact isCompactOperator_of_tendsto htendsto
    (Eventually.of_forall fun s => hsTrunc_isCompactOperator A s)

/-! ## Trace-class operators are compact -/

/-- **A positive trace-class operator is a compact operator.**

For `0 ≤ T`, `|T| = T` and `T = T^{1/2} ∘ T^{1/2}` with `T^{1/2}` Hilbert–Schmidt (as `T` is
trace class), so `T` is the composition of compact operators. -/
theorem isCompactOperator_of_nonneg {T : H →L[ℂ] H} (hT : 0 ≤ T) (hTC : IsTraceClass T) :
    IsCompactOperator T := by
  have hHS : IsHilbertSchmidt (sqrtOp T) := by
    have : sqrtOp T = sqrtOp (absOp T) := by rw [absOp_of_nonneg hT]
    rw [this]; exact (isHilbertSchmidt_sqrtOp_absOp T).mpr hTC
  have hcompact : IsCompactOperator (sqrtOp T) := hHS.isCompactOperator
  have hTeq : T = sqrtOp T ∘L sqrtOp T := by
    rw [← ContinuousLinearMap.mul_def, sqrtOp_mul_self T hT]
  rw [hTeq]
  exact hcompact.comp_clm (sqrtOp T)

/-- **Every trace-class operator is a compact operator.**

`T^{1/2} := |T|^{1/2}` is Hilbert–Schmidt (`T` is trace class), hence compact; then `|T| = T^{1/2} ∘
T^{1/2}` is compact, and `T = U |T|` (polar decomposition) is compact. -/
theorem IsTraceClass.isCompactOperator {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsCompactOperator T := by
  have hHS : IsHilbertSchmidt (sqrtOp (absOp T)) := (isHilbertSchmidt_sqrtOp_absOp T).mpr hT
  have hcompact : IsCompactOperator (sqrtOp (absOp T)) := hHS.isCompactOperator
  -- `|T| = T^{1/2} ∘ T^{1/2}` is compact.
  have habs : IsCompactOperator (absOp T) := by
    have : absOp T = sqrtOp (absOp T) ∘L sqrtOp (absOp T) := by
      rw [← ContinuousLinearMap.mul_def, sqrtOp_mul_self (absOp T) (absOp_nonneg T)]
    rw [this]; exact hcompact.comp_clm (sqrtOp (absOp T))
  -- `T = U |T|` is compact.
  rw [← polar_decomposition T]
  exact habs.clm_comp (polarIsometry T)

end Spectra.QuantumMechanics.Channels

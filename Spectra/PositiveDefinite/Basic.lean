/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/PositiveDefinite/Basic.lean
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
/-!
# Properties of Positive-Definite Functions

## Main results

### From `PositiveDefinite` alone (the `.re ≥ 0` condition):
* `pd_at_zero_nonneg`: `0 ≤ (f 0).re`
* `pd_two_point_add`: `0 ≤ 2 * (f 0).re + (f t + f (-t)).re`
* `pd_two_point_sub`: `0 ≤ 2 * (f 0).re - (f t + f (-t)).re`

### Hermitian symmetry:
* `IsHermitian`: `f(-t) = conj(f(t))` — holds for all unitary correlation functions
* `hermitian_at_zero_im`: `(f 0).im = 0`
* `hermitian_at_zero_ofReal`: `f 0 = ↑(f 0).re`
* `hermitian_sum_eq_two_re`: `f t + f (-t) = ↑(2 * (f t).re)`
* `hermitian_diff_eq_two_im`: `f t - f (-t) = ↑(2 * (f t).im) * I`

### Combined PD + Hermitian (the load-bearing results for Bochner):
* `pd_hermitian_re_le`: `(f t).re ≤ (f 0).re`
* `pd_hermitian_re_neg_le`: `-(f 0).re ≤ (f t).re`
* `pd_hermitian_re_abs_le`: `|(f t).re| ≤ (f 0).re`
* `pd_hermitian_im_abs_le`: `|(f t).im| ≤ (f 0).re`
* `pd_hermitian_norm_bound`: `‖f t‖ ≤ (f 0).re` — the sharp bound

## References

* Rudin, *Functional Analysis*, 2nd ed., §1.4.3 (Properties of positive-definite functions)
* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VII (Bochner's lemma)

## Tags

positive-definite, Bochner lemma, Hermitian symmetry, Fourier transform
-/
open Complex Filter Topology MeasureTheory
variable {f : ℝ → ℂ}
namespace Spectra.PositiveDefinite

/-- A function f : ℝ → ℂ is positive-definite if for all finite collections of points
    and coefficients, the quadratic form ∑ᵢⱼ c̄ᵢcⱼf(tᵢ - tⱼ) is non-negative. -/
def IsPositiveDefinite (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * f (t i - t j)).re

/-- Continuous positive-definite function: positive-definite and continuous at 0.
    Continuity at 0 plus positive-definiteness implies continuity everywhere. -/
def PositiveDefiniteContinuous (f : ℝ → ℂ) : Prop :=
  IsPositiveDefinite f ∧ ContinuousAt f 0

/-- right-continuity from continuity on the right.
    Used in constructing Stieltjes functions from spectral measures. -/
lemma tendsto_nhdsWithin_Ici_of_tendsto_nhdsWithin_Ioi {f : ℝ → ℝ} {x : ℝ}
    (h : Tendsto f (𝓝[>] x) (𝓝 (f x))) : ContinuousWithinAt f (Set.Ici x) x := by
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ_pos, hδ⟩ := h ε hε
  refine ⟨δ, hδ_pos, fun t ht_Ici ht_dist => ?_⟩
  obtain rfl | h_lt := (Set.mem_Ici.mp ht_Ici).eq_or_lt
  · rw [dist_self]; exact hε
  · exact hδ h_lt ht_dist

/-! ## Section 1: Properties from `PositiveDefinite` alone -/

/-- **f(0).re ≥ 0** for positive-definite f.

Proof: take n=1, t₁=0, c₁=1. The sum is f(0), and `.re ≥ 0`. -/
lemma pd_at_zero_nonneg (hf : IsPositiveDefinite f) : 0 ≤ (f 0).re := by
  have h := hf 1 (fun _ => 0) (fun _ => 1)
  simp only [Fin.sum_univ_one, map_one, one_mul, sub_self] at h
  exact h

/-- Two-point PD with c = ![1, 1]: adds the correlation at lag t and -t.

Gives: `0 ≤ 2·(f 0).re + Re(f(t) + f(-t))` -/
lemma pd_two_point_add (hf : IsPositiveDefinite f) (t : ℝ) :
    0 ≤ 2 * (f 0).re + (f t + f (-t)).re := by
  have h := hf 2 ![0, t] ![1, 1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  simp only [map_one, one_mul, sub_self, sub_zero, zero_sub] at h
  have : (f 0 + f (-t) + (f t + f 0)).re = 2 * (f 0).re + (f t + f (-t)).re := by
    simp only [add_re]; grind only
  linarith

/-- Two-point PD with c = ![1, -1]: subtracts the correlation at lag t and -t.

Gives: `0 ≤ 2·(f 0).re - Re(f(t) + f(-t))` -/
lemma pd_two_point_sub (hf : IsPositiveDefinite f) (t : ℝ) :
    0 ≤ 2 * (f 0).re - (f t + f (-t)).re := by
  have h := hf 2 ![0, t] ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  simp only [map_one, map_neg, one_mul, neg_mul, sub_self, sub_zero, zero_sub] at h
  have : (f 0 + -(f (-t)) + (-(f t) + f 0)).re = 2 * (f 0).re - (f t + f (-t)).re := by
    simp only [add_re, neg_re]; grind only
  grind only

/-- Two-point PD with c = ![1, I]: gives the imaginary part lower bound.

The sum evaluates to `2·f(0) + 2·Im(f(t))` under Hermitian symmetry,
so the PD condition yields `Im(f(t)) ≥ -(f 0).re`. -/
lemma pd_two_point_I (hf : IsPositiveDefinite f) (t : ℝ) :
    0 ≤ (f 0 + I * f (-t) + (-(I) * f t + f 0)).re := by
  have h := hf 2 ![0, t] ![1, I]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  simp only [map_one, one_mul, sub_self, sub_zero, zero_sub] at h
  convert h using 2
  simp only [conj_I, neg_mul, mul_one, I_mul_I, neg_neg, one_mul]

/-- Two-point PD with c = ![1, -I]: gives the imaginary part upper bound.

The sum evaluates to `2·f(0) - 2·Im(f(t))` under Hermitian symmetry,
so the PD condition yields `Im(f(t)) ≤ (f 0).re`. -/
lemma pd_two_point_neg_I (hf : IsPositiveDefinite f) (t : ℝ) :
    0 ≤ (f 0 + -(I * f (-t)) + (I * f t + f 0)).re := by
  have h := hf 2 ![0, t] ![1, -I]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  simp only [map_one, map_neg, one_mul, neg_mul, sub_self, sub_zero, zero_sub] at h
  convert h using 2
  simp only [conj_I, mul_one, neg_mul, neg_neg, mul_neg, I_mul_I, one_mul]

/-! ## Section 2: Hermitian symmetry -/

/-- A function f : ℝ → ℂ has **Hermitian symmetry** if f(-t) = conj(f(t)).

This holds automatically for:
- Unitary correlation functions: `t ↦ ⟨U(t)ψ, ψ⟩` (by `U(-t) = U(t)*`)
- Fourier transforms of positive measures: `t ↦ ∫ e^{iωt} dμ(ω)`

It does NOT follow from `IsPositiveDefinite` (the `.re ≥ 0` condition) alone. -/
def IsHermitian (f : ℝ → ℂ) : Prop :=
  ∀ t, f (-t) = starRingEnd ℂ (f t)

/-- f(0) has zero imaginary part for Hermitian functions. -/
lemma hermitian_at_zero_im (hH : IsHermitian f) : (f 0).im = 0 := by
  have h := hH 0
  simp only [neg_zero] at h
  -- h : f 0 = conj(f 0), so f 0 is real
  exact Complex.conj_eq_iff_im.mp h.symm

/-- f(0) equals its real part (as a complex number) for Hermitian functions. -/
lemma hermitian_at_zero_ofReal (hH : IsHermitian f) : f 0 = ↑((f 0).re) := by
  apply Complex.ext
  · simp
  · simp [hermitian_at_zero_im hH]

/-- f(0) is real and non-negative for PD + Hermitian functions. -/
lemma pd_hermitian_at_zero (hf : IsPositiveDefinite f) (hH : IsHermitian f) :
    f 0 = ↑((f 0).re) ∧ 0 ≤ (f 0).re :=
  ⟨hermitian_at_zero_ofReal hH, pd_at_zero_nonneg hf⟩

/-- Under Hermitian symmetry, f(t) + f(-t) = 2·Re(f(t)) (as a real number in ℂ). -/
lemma hermitian_sum_eq_two_re (hH : IsHermitian f) (t : ℝ) :
    f t + f (-t) = ↑(2 * (f t).re) := by
  rw [hH t]
  apply Complex.ext
  · simp [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
    exact Eq.symm (two_mul (f t).re)
  · simp [Complex.add_im, Complex.conj_im, Complex.ofReal_im]

/-- Under Hermitian symmetry, f(t) - f(-t) = 2i·Im(f(t)). -/
lemma hermitian_diff_eq_two_im (hH : IsHermitian f) (t : ℝ) :
    f t - f (-t) = ↑(2 * (f t).im) * I := by
  rw [hH t]
  apply Complex.ext <;> simp [mul_comm]
  exact Eq.symm (mul_two (f t).im)

/-! ## Section 3: Combined PD + Hermitian — component bounds -/

/-- **Real part upper bound**: Re(f(t)) ≤ f(0).re.

Proof: PD with c = ![1, -1] at points 0, t. Under Hermitian symmetry,
the sum becomes `2·(f(0).re - Re(f(t))) ≥ 0`. -/
lemma pd_hermitian_re_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    (f t).re ≤ (f 0).re := by
  have h := pd_two_point_sub hf t
  rw [hermitian_sum_eq_two_re hH t] at h
  simp only [Complex.ofReal_re] at h
  linarith

/-- **Real part lower bound**: -(f(0).re) ≤ Re(f(t)).

Proof: PD with c = ![1, 1] at points 0, t. -/
lemma pd_hermitian_re_neg_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    -(f 0).re ≤ (f t).re := by
  have h := pd_two_point_add hf t
  rw [hermitian_sum_eq_two_re hH t] at h
  simp only [Complex.ofReal_re] at h
  linarith

/-- **Real part absolute bound**: |Re(f(t))| ≤ f(0).re. -/
lemma pd_hermitian_re_abs_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    |(f t).re| ≤ (f 0).re :=
  abs_le.mpr ⟨by linarith [pd_hermitian_re_neg_le hf hH t],
               pd_hermitian_re_le hf hH t⟩

/-- **Imaginary part upper bound**: Im(f(t)) ≤ f(0).re.

Proof: PD with c = ![1, -I] at points 0, t. Under Hermitian symmetry,
Re(I·f(t)) = -(f t).im, so the sum becomes `2·(f(0).re - Im(f(t))) ≥ 0`. -/
lemma pd_hermitian_im_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    (f t).im ≤ (f 0).re := by
  have h := pd_two_point_neg_I hf t
  rw [hH t] at h
  have key : (f 0 + -(I * starRingEnd ℂ (f t)) + (I * f t + f 0)).re =
      2 * (f 0).re - 2 * (f t).im := by
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re,
               Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  linarith

/-- **Imaginary part lower bound**: -(f(0).re) ≤ Im(f(t)). -/
lemma pd_hermitian_im_neg_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    -(f 0).re ≤ (f t).im := by
  have h := pd_two_point_I hf t
  rw [hH t] at h
  have key : (f 0 + I * starRingEnd ℂ (f t) + (-I * f t + f 0)).re =
      2 * (f 0).re + 2 * (f t).im := by
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re,
               Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_im]
    ring
  linarith

/-- **Imaginary part absolute bound**: |Im(f(t))| ≤ f(0).re. -/
lemma pd_hermitian_im_abs_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    |(f t).im| ≤ (f 0).re :=
  abs_le.mpr ⟨by linarith [pd_hermitian_im_neg_le hf hH t],
               pd_hermitian_im_le hf hH t⟩

/-! ## Section 4: The sharp norm bound -/

/-- Auxiliary: `starRingEnd ℂ z * z` has real part `‖z‖²`.

This is the key identity for extracting norms from the PD quadratic form.

Note: If `Complex.sq_abs` doesn't resolve in your Mathlib version, replace
the last line with `simp [Complex.normSq_apply, Complex.norm_eq_abs,
Real.sq_sqrt (Complex.normSq_nonneg z)]` or prove directly via
`ext <;> simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] <;> ring`. -/
private lemma conj_mul_self_re (z : ℂ) : (starRingEnd ℂ z * z).re = ‖z‖ ^ 2 := by
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
  exact normSq_eq_norm_sq z

/-- Auxiliary: `starRingEnd ℂ z * z` is real (imaginary part is zero). -/
private lemma conj_mul_self_im (z : ℂ) : (starRingEnd ℂ z * z).im = 0 := by
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_im]

/-- Auxiliary: for z ≠ 0, `starRingEnd ℂ z * z / ↑‖z‖` equals `↑‖z‖` (as ℂ).

Not on the critical path — used only in alternative norm bound approaches. -/
private lemma conj_mul_div_norm (z : ℂ) (hz : z ≠ 0) :
    starRingEnd ℂ z * z / ↑‖z‖ = ↑‖z‖ := by
  have h_norm_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have h_re := conj_mul_self_re z
  have h_im := conj_mul_self_im z
  have h_eq : starRingEnd ℂ z * z = ↑(‖z‖ ^ 2) := by
    apply Complex.ext
    · exact Real.ext_cauchy (congrArg Real.cauchy h_re)
    · exact Real.ext_cauchy (congrArg Real.cauchy h_im)
  rw [h_eq, ← Complex.ofReal_div, sq, mul_div_cancel_left₀ _ (ne_of_gt h_norm_pos)]

/-- **The sharp norm bound**: `‖f(t)‖ ≤ f(0).re` for PD + Hermitian functions.

This is the critical estimate for Bochner's lemma. It says the
positive-definite function is uniformly bounded by its value at the origin,
which provides the dominated convergence control in the existence proof.

### Proof strategy

Use the 2-point PD condition with n=2, points `![0, t]`, and coefficients
`c = ![conj(f(t)), -‖f(t)‖]`. Under Hermitian symmetry, the quadratic form
evaluates to `2·‖f(t)‖²·((f 0).re - ‖f(t)‖)`, which must be ≥ 0. Since
`‖f(t)‖² > 0` (for f(t) ≠ 0), we get `‖f(t)‖ ≤ (f 0).re`. -/
lemma pd_hermitian_norm_bound (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    ‖f t‖ ≤ (f 0).re := by
  by_cases hft : f t = 0
  · simp [hft]; exact pd_at_zero_nonneg hf
  have h_norm_pos : (0 : ℝ) < ‖f t‖ := norm_pos_iff.mpr hft
  have hpd := hf 2 ![0, t] ![starRingEnd ℂ (f t), -(↑‖f t‖ : ℂ)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
             sub_self, sub_zero, zero_sub] at hpd
  rw [hH t] at hpd
  simp only [map_neg, Complex.conj_ofReal] at hpd
  have h_ww : (starRingEnd ℂ (f t) * f t).re = ‖f t‖ ^ 2 := conj_mul_self_re (f t)
  have h_ww' : (f t * starRingEnd ℂ (f t)).re = ‖f t‖ ^ 2 := by
    rw [mul_comm]; exact h_ww
  have h_ww_im : (starRingEnd ℂ (f t) * f t).im = 0 := conj_mul_self_im (f t)
  have h_ww_im' : (f t * starRingEnd ℂ (f t)).im = 0 := by
    rw [mul_comm]; exact h_ww_im
  simp only [starRingEnd_self_apply] at hpd
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
             Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.conj_re, Complex.conj_im] at hpd
  have hf0im : (f 0).im = 0 := hermitian_at_zero_im hH
  rw [hf0im] at hpd
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_add, neg_zero] at hpd
  have hnsq : ‖f t‖ ^ 2 = (f t).re ^ 2 + (f t).im ^ 2 := by
    rw [← normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h_factor : ∀ (z w f₀ : ℂ) (r : ℝ),
      (z * w * f₀ + z * -(↑r : ℂ) * w +
      (-(↑r : ℂ) * w * z + -(↑r : ℂ) * -(↑r : ℂ) * f₀)).re =
      ((z * w + (↑r : ℂ) * (↑r : ℂ)) * f₀ +
       (-2 : ℂ) * (↑r : ℂ) * (z * w)).re := by
    intro z w f₀ r; congr 1; ring
  have h_pos : (0 : ℝ) < 2 * ‖f t‖ ^ 2 := by positivity
  nlinarith [h_factor, h_pos]

/-- Corollary: ‖f(t)‖² ≤ (f 0).re² for PD + Hermitian functions. -/
lemma pd_hermitian_norm_sq_bound (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    ‖f t‖ ^ 2 ≤ (f 0).re ^ 2 :=
  sq_le_sq' (by linarith [norm_nonneg (f t), pd_hermitian_norm_bound hf hH t])
            (pd_hermitian_norm_bound hf hH t)

/-! ## Section 5: Continuity propagation

For PD + Hermitian + continuous at 0, we get uniform continuity everywhere.
The key estimate is: `‖f(t+h) - f(t)‖² ≤ 2·f(0).re·(f(0).re - Re(f(h)))`. -/

/-- The "variance" of the PD function: `f(0).re - Re(f(h))`.

This is always non-negative (by `pd_hermitian_re_le`), and measures how far
f(h) is from its maximum value f(0). Continuity at 0 means this tends to 0. -/
def pdVariance (f : ℝ → ℂ) (h : ℝ) : ℝ := (f 0).re - (f h).re

lemma pdVariance_nonneg (hf : IsPositiveDefinite f) (hH : IsHermitian f) (h : ℝ) :
    0 ≤ pdVariance f h :=
  sub_nonneg.mpr (pd_hermitian_re_le hf hH h)

lemma pdVariance_zero (_hH : IsHermitian f) : pdVariance f 0 = 0 := by
  simp [pdVariance]

lemma pdVariance_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (h : ℝ) :
    pdVariance f h ≤ 2 * (f 0).re := by
  unfold pdVariance
  linarith [pd_hermitian_re_neg_le hf hH h]

/-- The PD variance is continuous at 0 when f is continuous at 0. -/
lemma pdVariance_tendsto_zero (_hf : IsPositiveDefinite f) (_hH : IsHermitian f)
    (hcont : ContinuousAt f 0) :
    Filter.Tendsto (pdVariance f) (𝓝 0) (𝓝 0) := by
  have : Filter.Tendsto (fun h => (f 0).re - (f h).re) (𝓝 0) (𝓝 ((f 0).re - (f 0).re)) := by
    apply Filter.Tendsto.sub
    · exact tendsto_const_nhds
    · exact (Complex.continuous_re.continuousAt.comp hcont).tendsto
  rw [sub_self] at this
  exact this


end Spectra.PositiveDefinite

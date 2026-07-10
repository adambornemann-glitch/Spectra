/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
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

### `IsPositiveDefinite` alone (the `.re ≥ 0` quadratic-form condition):
* `IsPositiveDefinite`: `0 ≤ (∑ᵢⱼ conj(cᵢ)cⱼf(tᵢ-tⱼ)).re` for all finite `t`, `c`
* `pd_at_zero_nonneg`: `0 ≤ (f 0).re`
* `pd_two_point_add`: `0 ≤ 2 * (f 0).re + (f t + f (-t)).re`
* `pd_two_point_sub`: `0 ≤ 2 * (f 0).re - (f t + f (-t)).re`
* `pd_two_point_I`: `0 ≤ 2 * (f 0).re + (f t - f (-t)).im`
* `pd_two_point_neg_I`: `0 ≤ 2 * (f 0).re + (f (-t) - f t).im`

### Hermitian symmetry:
* `IsHermitian`: `f(-t) = conj(f(t))` — holds for all unitary correlation functions
* `hermitian_at_zero_im`: `(f 0).im = 0`
* `hermitian_at_zero_ofReal`: `f 0 = ↑(f 0).re`
* `hermitian_sum_eq_two_re`: `f t + f (-t) = ↑(2 * (f t).re)`
* `hermitian_diff_eq_two_im`: `f t - f (-t) = ↑(2 * (f t).im) * I`

### Combined PD + Hermitian (the load-bearing results for Bochner):
* `pd_hermitian_at_zero`: `f 0 = ↑(f 0).re ∧ 0 ≤ (f 0).re`
* `pd_hermitian_re_le`: `(f t).re ≤ (f 0).re`
* `pd_hermitian_re_neg_le`: `-(f 0).re ≤ (f t).re`
* `pd_hermitian_re_abs_le`: `|(f t).re| ≤ (f 0).re`
* `pd_hermitian_im_le`: `(f t).im ≤ (f 0).re`
* `pd_hermitian_im_neg_le`: `-(f 0).re ≤ (f t).im`
* `pd_hermitian_im_abs_le`: `|(f t).im| ≤ (f 0).re`
* `pd_hermitian_norm_bound`: `‖f t‖ ≤ (f 0).re` — the sharp bound
* `pd_hermitian_norm_sq_bound`: `‖f t‖ ^ 2 ≤ (f 0).re ^ 2`

### Continuity propagation (the PD "variance" `pdVariance f h = (f 0).re - (f h).re`):
* `pdVariance_nonneg`: `0 ≤ pdVariance f h`
* `pdVariance_zero`: `pdVariance f 0 = 0`
* `pdVariance_le`: `pdVariance f h ≤ 2 * (f 0).re`
* `pdVariance_tendsto_zero`: `pdVariance f → 0` at `0` when `f` is continuous at `0`

## References

* Rudin, *Functional Analysis*, 2nd ed., §1.4.3 (Properties of positive-definite functions)
* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VII (Bochner's lemma)

## Tags

positive-definite, Bochner lemma, Hermitian symmetry, Fourier transform
-/
open Complex Filter Topology MeasureTheory
namespace Spectra.PositiveDefinite

variable {f : ℝ → ℂ}

/-- A function f : ℝ → ℂ is positive-definite if for all finite collections of points
    and coefficients, the quadratic form ∑ᵢⱼ c̄ᵢcⱼf(tᵢ - tⱼ) is non-negative. -/
def IsPositiveDefinite (f : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * f (t i - t j)).re

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
    simp only [add_re]; ring
  linarith

/-- Two-point PD with c = ![1, -1]: subtracts the correlation at lag t and -t.

Gives: `0 ≤ 2·(f 0).re - Re(f(t) + f(-t))` -/
lemma pd_two_point_sub (hf : IsPositiveDefinite f) (t : ℝ) :
    0 ≤ 2 * (f 0).re - (f t + f (-t)).re := by
  have h := hf 2 ![0, t] ![1, -1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  simp only [map_one, map_neg, one_mul, neg_mul, neg_neg, sub_self, sub_zero, zero_sub] at h
  have : (f 0 + -(f (-t)) + (-(f t) + f 0)).re = 2 * (f 0).re - (f t + f (-t)).re := by
    simp only [add_re, neg_re]; ring
  linarith

/-- Two-point PD with c = ![1, I]: gives the imaginary part lower bound.

Gives: `0 ≤ 2·(f 0).re + Im(f(t) - f(-t))`, so under Hermitian symmetry
the PD condition yields `Im(f(t)) ≥ -(f 0).re`. -/
lemma pd_two_point_I (hf : IsPositiveDefinite f) (t : ℝ) :
    0 ≤ 2 * (f 0).re + (f t - f (-t)).im := by
  have hraw : 0 ≤ (f 0 + I * f (-t) + (-(I) * f t + f 0)).re := by
    have h := hf 2 ![0, t] ![1, I]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    simp only [map_one, one_mul, sub_self, sub_zero, zero_sub] at h
    convert h using 2
    simp only [conj_I, neg_mul, mul_one, I_mul_I, neg_neg, one_mul]
  have heq : (f 0 + I * f (-t) + (-(I) * f t + f 0)).re =
      2 * (f 0).re + (f t - f (-t)).im := by
    simp only [Complex.add_re, Complex.neg_re, Complex.neg_im, Complex.mul_re,
               Complex.I_re, Complex.I_im, Complex.sub_im]
    ring
  linarith [hraw, heq]

/-- Two-point PD with c = ![1, -I]: gives the imaginary part upper bound.

Gives: `0 ≤ 2·(f 0).re + Im(f(-t) - f(t))`, so under Hermitian symmetry
the PD condition yields `Im(f(t)) ≤ (f 0).re`. -/
lemma pd_two_point_neg_I (hf : IsPositiveDefinite f) (t : ℝ) :
    0 ≤ 2 * (f 0).re + (f (-t) - f t).im := by
  have hraw : 0 ≤ (f 0 + -(I * f (-t)) + (I * f t + f 0)).re := by
    have h := hf 2 ![0, t] ![1, -I]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    simp only [map_one, map_neg, one_mul, neg_mul, sub_self, sub_zero, zero_sub] at h
    convert h using 2
    simp only [conj_I, mul_one, neg_mul, neg_neg, mul_neg, I_mul_I, one_mul]
  have heq : (f 0 + -(I * f (-t)) + (I * f t + f 0)).re =
      2 * (f 0).re + (f (-t) - f t).im := by
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re,
               Complex.I_re, Complex.I_im, Complex.sub_im]
    ring
  linarith [hraw, heq]

/-! ## Section 2: Hermitian symmetry -/

/-- A function f : ℝ → ℂ has **Hermitian symmetry** if f(-t) = conj(f(t)).

Unrelated to `Matrix.IsHermitian`; this is a scalar-function symmetry condition, not a
matrix property. Namespaced under `Spectra.PositiveDefinite` to avoid a literal name
clash, but the two can still collide under `open Spectra.PositiveDefinite` alongside
matrix code. -/
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
  · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
    exact Eq.symm (two_mul (f t).re)
  · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im, add_neg_cancel]

/-- Under Hermitian symmetry, f(t) - f(-t) = 2i·Im(f(t)). -/
lemma hermitian_diff_eq_two_im (hH : IsHermitian f) (t : ℝ) :
    f t - f (-t) = ↑(2 * (f t).im) * I := by
  rw [hH t]
  apply Complex.ext <;> simp only [mul_comm, sub_re, conj_re, sub_self, ofReal_mul,
    ofReal_ofNat, mul_re, I_re, ofReal_re, re_ofNat, ofReal_im, im_ofNat, mul_zero, sub_zero,
    zero_mul, I_im, mul_im, add_zero]
  simp only [sub_im, conj_im, sub_neg_eq_add, one_mul, zero_add]
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
  simp only [Complex.sub_im, Complex.conj_im] at h
  linarith

/-- **Imaginary part lower bound**: -(f(0).re) ≤ Im(f(t)). -/
lemma pd_hermitian_im_neg_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    -(f 0).re ≤ (f t).im := by
  have h := pd_two_point_I hf t
  rw [hH t] at h
  simp only [Complex.sub_im, Complex.conj_im] at h
  linarith

/-- **Imaginary part absolute bound**: |Im(f(t))| ≤ f(0).re. -/
lemma pd_hermitian_im_abs_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    |(f t).im| ≤ (f 0).re :=
  abs_le.mpr ⟨by linarith [pd_hermitian_im_neg_le hf hH t],
               pd_hermitian_im_le hf hH t⟩

/-! ## Section 4: The sharp norm bound -/

/-- **The sharp norm bound**: `‖f(t)‖ ≤ f(0).re` for PD + Hermitian functions. -/
lemma pd_hermitian_norm_bound (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    ‖f t‖ ≤ (f 0).re := by
  by_cases hft : f t = 0
  · simp only [hft, norm_zero]
    exact pd_at_zero_nonneg hf
  have _h_norm_pos : (0 : ℝ) < ‖f t‖ := norm_pos_iff.mpr hft
  have hpd := hf 2 ![0, t] ![starRingEnd ℂ (f t), -(↑‖f t‖ : ℂ)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
             sub_self, sub_zero, zero_sub] at hpd
  rw [hH t] at hpd
  simp only [map_neg, Complex.conj_ofReal, starRingEnd_self_apply] at hpd
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
             Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.conj_re, Complex.conj_im] at hpd
  have hf0im : (f 0).im = 0 := hermitian_at_zero_im hH
  rw [hf0im] at hpd
  simp only [mul_zero, zero_mul, sub_zero, add_zero, zero_add, neg_zero] at hpd
  have hnsq : ‖f t‖ ^ 2 = (f t).re ^ 2 + (f t).im ^ 2 := by
    rw [← normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h_pos : (0 : ℝ) < 2 * ‖f t‖ ^ 2 := by positivity
  -- Substituting `hnsq` (‖f t‖² = (f t).re² + (f t).im²) into `hpd` twice — once scaled by
  -- `(f 0).re`, once by `‖f t‖` — collapses it to `0 ≤ 2‖f t‖²·((f 0).re - ‖f t‖)`; dividing by
  -- the positive `2‖f t‖²` gives the goal.
  have hnsq' : (f 0).re * ‖f t‖ ^ 2 = (f 0).re * ((f t).re ^ 2 + (f t).im ^ 2) := by rw [hnsq]
  have hnsq'' : ‖f t‖ * ‖f t‖ ^ 2 = ‖f t‖ * ((f t).re ^ 2 + (f t).im ^ 2) := by rw [hnsq]
  have key : 0 ≤ 2 * ‖f t‖ ^ 2 * ((f 0).re - ‖f t‖) := by nlinarith [hpd, hnsq', hnsq'']
  nlinarith [key, h_pos]

/-- Corollary: ‖f(t)‖² ≤ (f 0).re² for PD + Hermitian functions. -/
lemma pd_hermitian_norm_sq_bound (hf : IsPositiveDefinite f) (hH : IsHermitian f) (t : ℝ) :
    ‖f t‖ ^ 2 ≤ (f 0).re ^ 2 :=
  sq_le_sq' (by linarith [norm_nonneg (f t), pd_hermitian_norm_bound hf hH t])
            (pd_hermitian_norm_bound hf hH t)

/-! ## Section 5: Continuity propagation

For PD + Hermitian + continuous at 0, we get uniform continuity everywhere.
The key estimate is: `‖f(t+h) - f(t)‖² ≤ 2·f(0).re·(f(0).re - Re(f(h)))`. -/

/-- The "variance" of the PD function: `f(0).re - Re(f(h))`. -/
def pdVariance (f : ℝ → ℂ) (h : ℝ) : ℝ := (f 0).re - (f h).re

lemma pdVariance_nonneg (hf : IsPositiveDefinite f) (hH : IsHermitian f) (h : ℝ) :
    0 ≤ pdVariance f h :=
  sub_nonneg.mpr (pd_hermitian_re_le hf hH h)

lemma pdVariance_zero : pdVariance f 0 = 0 := by
  simp [pdVariance]

lemma pdVariance_le (hf : IsPositiveDefinite f) (hH : IsHermitian f) (h : ℝ) :
    pdVariance f h ≤ 2 * (f 0).re := by
  unfold pdVariance
  linarith [pd_hermitian_re_neg_le hf hH h]

/-- The PD variance is continuous at 0 when f is continuous at 0. -/
lemma pdVariance_tendsto_zero (hcont : ContinuousAt f 0) :
    Filter.Tendsto (pdVariance f) (𝓝 0) (𝓝 0) := by
  have : Filter.Tendsto (fun h => (f 0).re - (f h).re) (𝓝 0) (𝓝 ((f 0).re - (f 0).re)) := by
    apply Filter.Tendsto.sub
    · exact tendsto_const_nhds
    · exact (Complex.continuous_re.continuousAt.comp hcont).tendsto
  rw [sub_self] at this
  exact this


end Spectra.PositiveDefinite

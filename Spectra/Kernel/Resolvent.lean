/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Kernel.Defs
/-!
# Resolvent Kernel Analysis

This file develops the analytical properties of the resolvent kernel `(s - z)⁻¹`
and the associated Lorentzian approximation to the delta function.

## Main statements

### Resolvent kernel
* `resolvent_integrand_bound`: `|(s - z)⁻¹| ≤ 1/|Im(z)|` for all `s ∈ ℝ`
* `resolvent_kernel_im`: `Im((s - (t + iε))⁻¹) = ε/((s-t)² + ε²)`
* `resolvent_kernel_diff`: `(s - (t+iε))⁻¹ - (s - (t-iε))⁻¹ = 2iε/((s-t)² + ε²)`

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VII
* Stone, "Linear Transformations in Hilbert Space" (1932)

## Tags

resolvent, Lorentzian, approximate identity, Poisson kernel
-/
open Complex MeasureTheory
namespace Spectra.Kernels

/-- The resolvent integrand is bounded by `1/|Im(z)|`.
This is the key estimate: for `z` off the real axis, the kernel `(s - z)⁻¹`
is uniformly bounded in `s ∈ ℝ`, with bound depending only on `|Im(z)|`. -/
lemma resolvent_integrand_bound (z : ℂ) (hz : z.im ≠ 0) (s : ℝ) :
    ‖resolventIntegrand z s‖ ≤ 1 / |z.im| := by
  unfold resolventIntegrand
  have h_im : ((s : ℂ) - z).im = -z.im := by simp
  have h_norm_ge : ‖(s : ℂ) - z‖ ≥ |z.im| := by
    calc ‖(s : ℂ) - z‖
        ≥ |((s : ℂ) - z).im| := Complex.abs_im_le_norm _
      _ = |-z.im| := by rw [h_im]
      _ = |z.im| := abs_neg _
  have h_pos : |z.im| > 0 := abs_pos.mpr hz
  calc ‖((s : ℂ) - z)⁻¹‖
      = 1 / ‖(s : ℂ) - z‖ := by rw [norm_inv]; simp only [one_div]
    _ ≤ 1 / |z.im| := by
        apply div_le_div_of_nonneg_left (by norm_num) h_pos h_norm_ge

/-! ### Lorentzian kernel -/

/-- Imaginary part of resolvent kernel: `Im((s - z)⁻¹) = ε/((s-t)² + ε²)` for `z = t + iε`.
This shows that the imaginary part of the resolvent kernel is exactly the
Lorentzian (Cauchy/Poisson) kernel, which is an approximation to the delta function. -/
lemma resolvent_kernel_im (s t ε : ℝ) (hε : ε > 0) :
    (((s : ℂ) - (↑t + ↑ε * I))⁻¹).im = ε / ((s - t)^2 + ε^2) := by
  have _h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  have h_diff : (s : ℂ) - (↑t + ↑ε * I) = (s - t : ℝ) - ε * I := by
    simp only [Complex.ofReal_sub]
    ring
  rw [h_diff]
  -- ((s-t) - εi)⁻¹ = ((s-t) + εi) / ((s-t)² + ε²)
  have h_conj : ((s - t : ℝ) - ε * I)⁻¹ =
      ((s - t : ℝ) + ε * I) / ((s - t)^2 + ε^2 : ℂ) := by
    have h_mul : ((s - t : ℝ) - ε * I) * ((s - t : ℝ) + ε * I) =
        ((s - t)^2 + ε^2 : ℂ) := by
      push_cast
      have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
      linear_combination (norm := ring) -ε^2 * hI2
    have h_conj_ne : (↑(s - t) : ℂ) + ↑ε * I ≠ 0 := by
      intro h
      have : ε = 0 := by simpa using congrArg Complex.im h
      linarith
    rw [← h_mul]
    field_simp [h_conj_ne]
  rw [h_conj]
  have h_real : ((s - t)^2 + ε^2 : ℂ) = ((s - t)^2 + ε^2 : ℝ) := by push_cast; ring
  rw [h_real, Complex.div_ofReal_im]
  simp [Complex.add_im, Complex.mul_im]

/-- Key identity: difference of resolvent kernels at conjugate points.
`(s - (t + iε))⁻¹ - (s - (t - iε))⁻¹ = 2iε / ((s-t)² + ε²)` -/
lemma resolvent_kernel_diff (s t ε : ℝ) (hε : ε > 0) :
    ((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹ =
    (2 * ε * I) / ((s - t)^2 + ε^2 : ℂ) := by
  have _h_z_plus : (↑t + ↑ε * I : ℂ) - (↑t - ↑ε * I) = 2 * ε * I := by ring
  have h_denom : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) =
      ((s - t)^2 + ε^2 : ℂ) := by
    have hI2 : (I : ℂ)^2 = -1 := Complex.I_sq
    linear_combination (norm := ring) -ε^2 * hI2
  have h_denom_ne : ((s - t : ℝ)^2 + ε^2 : ℂ) ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  have h_prod_ne : ((s : ℂ) - (↑t + ↑ε * I)) * ((s : ℂ) - (↑t - ↑ε * I)) ≠ 0 := by
    rw [h_denom]
    push_cast at h_denom_ne ⊢
    exact h_denom_ne
  have h_left_ne : (s : ℂ) - (↑t + ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, zero_mul]
  have h_right_ne : (s : ℂ) - (↑t - ↑ε * I) ≠ 0 := by
    intro h
    apply h_prod_ne
    rw [h, mul_zero]
  -- Main calculation
  have h_denom_ne' : (↑s - ↑t : ℂ) ^ 2 + ↑ε ^ 2 ≠ 0 := by
    have h : (s - t)^2 + ε^2 > 0 := by positivity
    exact_mod_cast h.ne'
  field_simp [h_left_ne, h_right_ne, h_denom_ne']
  push_cast [sq]
  ring_nf
  simp only [I_pow_three, mul_neg, neg_mul, sub_neg_eq_add]

/-- Normalized resolvent difference equals the Lorentzian kernel.
    This is the kernel-level form of Stone's formula. (Currently unused.) -/
lemma resolvent_kernel_diff_normalized (s t ε : ℝ) (hε : ε > 0) :
    (1 / (2 * Real.pi * I)) *
      (((s : ℂ) - (↑t + ↑ε * I))⁻¹ - ((s : ℂ) - (↑t - ↑ε * I))⁻¹) =
    ↑(ε / ((s - t)^2 + ε^2) / Real.pi) := by
  rw [resolvent_kernel_diff s t ε hε]
  have _hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  have _h_denom : (s - t) ^ 2 + ε ^ 2 > 0 := by positivity
  push_cast
  field_simp

/-- Off-the-vertical-strip decay of the Cauchy kernel: if `|z.re| < R` and
`|l| ≥ R`, then `|l - z| ≥ R - |z.re|`, hence the inverse is bounded. -/
lemma cauchy_kernel_norm_le_of_abs_ge {z : ℂ} {R : ℝ} (hR : |z.re| < R)
    {l : ℝ} (hl : R ≤ |l|) :
    ‖((l : ℂ) - z)⁻¹‖ ≤ 1 / (R - |z.re|) := by
  have hRgap : 0 < R - |z.re| := by linarith
  have h_lzre : R - |z.re| ≤ |l - z.re| :=
    calc R - |z.re| ≤ |l| - |z.re| := by linarith
      _ ≤ |l - z.re| := abs_sub_abs_le_abs_sub _ _
  have h_lz : R - |z.re| ≤ ‖(l : ℂ) - z‖ :=
    calc R - |z.re| ≤ |l - z.re| := h_lzre
      _ = |((l : ℂ) - z).re| := by simp [Complex.sub_re, Complex.ofReal_re]
      _ ≤ ‖(l : ℂ) - z‖ := Complex.abs_re_le_norm _
  rw [norm_inv, ← one_div]
  exact div_le_div_of_nonneg_left (by norm_num) hRgap h_lz

/-- Tail bound: outside `Ioc (-R) R`, the Cauchy transform of any finite
measure on `ℝ` is controlled by total mass over `R - |z.re|`. -/
lemma norm_setIntegral_cauchy_kernel_outside_le
    {ν : Measure ℝ} [IsFiniteMeasure ν] {z : ℂ} {R : ℝ} (hR : |z.re| < R) :
    ‖∫ l in (Set.Ioc (-R) R)ᶜ, ((l : ℂ) - z)⁻¹ ∂ν‖
      ≤ (ν Set.univ).toReal / (R - |z.re|) := by
  have _hRgap : 0 < R - |z.re| := by linarith
  have hbd : ∀ l ∈ (Set.Ioc (-R) R)ᶜ, ‖((l : ℂ) - z)⁻¹‖ ≤ 1 / (R - |z.re|) := by
    intro l hl
    have h_absL : R ≤ |l| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hl
      rcases hl with hL | hR'
      · calc R ≤ -l := by linarith
          _ ≤ |l| := neg_le_abs l
      · linarith [le_abs_self l]
    exact cauchy_kernel_norm_le_of_abs_ge hR h_absL
  calc ‖∫ l in (Set.Ioc (-R) R)ᶜ, ((l : ℂ) - z)⁻¹ ∂ν‖
      ≤ (1 / (R - |z.re|)) * ν.real (Set.Ioc (-R) R)ᶜ :=
        norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hbd
    _ ≤ (1 / (R - |z.re|)) * (ν Set.univ).toReal := by
        have h_le : ν.real (Set.Ioc (-R) R)ᶜ ≤ (ν Set.univ).toReal := by
          rw [MeasureTheory.measureReal_def]
          exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
        gcongr
    _ = (ν Set.univ).toReal / (R - |z.re|) := by ring

end Spectra.Kernels

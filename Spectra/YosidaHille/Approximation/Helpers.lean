/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.PNat.Basic

/-!
# Basic lemmas for the Yosida approximation

Foundational facts used throughout the Yosida-approximation construction: arithmetic of the
imaginary parts and norms of `I * n` and `-I * n` for `n : ℕ+` (these supply the off-axis
spectral parameters `z = I * n`).

## Main statements

* `I_mul_pnat_im_ne_zero` / `neg_I_mul_pnat_im_ne_zero` — `± I * n` has nonzero imaginary part,
  so it lies off the real axis and the resolvent is defined there.
* `norm_I_mul_pnat` — `‖I * n‖ = n`.
* `I_mul_pnat_im` / `abs_I_mul_pnat_im` / `norm_pnat_sq` — auxiliary arithmetic facts supporting
  the headline results above.
-/

open Complex

namespace Spectra.YosidaHille.Approximation

/-! ### Arithmetic of `I * n` for `n : ℕ+` -/

/-- The imaginary part of `I * n` is nonzero for `n : ℕ+`, so `I * n` is off the real axis. -/
lemma I_mul_pnat_im_ne_zero (n : ℕ+) : (I * (n : ℂ)).im ≠ 0 := by
  simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  exact Nat.cast_ne_zero.mpr n.ne_zero

/-- The imaginary part of `-I * n` is nonzero for `n : ℕ+`. -/
lemma neg_I_mul_pnat_im_ne_zero (n : ℕ+) : (-I * (n : ℂ)).im ≠ 0 := by
  simp only [neg_mul, neg_im]
  exact neg_ne_zero.mpr (I_mul_pnat_im_ne_zero n)

/-- The imaginary part of `I * n` equals `n` for `n : ℕ+`. -/
lemma I_mul_pnat_im (n : ℕ+) : (I * (n : ℂ)).im = (n : ℝ) := by
  simp [mul_im]

/-- The absolute value of the imaginary part of `I * n` equals `n` for `n : ℕ+`. -/
lemma abs_I_mul_pnat_im (n : ℕ+) : |(I * (n : ℂ)).im| = (n : ℝ) := by
  rw [I_mul_pnat_im]
  exact abs_of_pos (Nat.cast_pos.mpr n.pos)

/-- The norm of `(n : ℂ)²` equals `n²` for `n : ℕ+`. -/
lemma norm_pnat_sq (n : ℕ+) : ‖((n : ℂ)^2)‖ = (n : ℝ)^2 := by
  rw [Complex.norm_pow, Complex.norm_natCast]

/-- The norm of `I * n` equals `n` for `n : ℕ+`. -/
lemma norm_I_mul_pnat (n : ℕ+) : ‖I * (n : ℂ)‖ = (n : ℝ) := by
  rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]

end Spectra.YosidaHille.Approximation

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion

/-!
# L¹-Fourier injectivity

A continuous integrable function on `ℝ` whose Fourier transform (in the non-`2π`-normalized
kernel `∫ t, e^{-i ξ t} f t`) vanishes for every real frequency `ξ` is identically zero.

This is an engine FOR the base-`M` Tomita theorem build (fields 6/7/8 of `ModularData`): the
strip argument for `Δ^{it} M Δ^{-it} = M` produces, for matrix elements of the would-be
defect, exactly a vanishing Fourier transform in the non-normalized kernel; this file
converts that analytic output into the pointwise vanishing needed to close the theorem.

The proof translates the hypothesis into Mathlib's `𝓕` normalization (kernel `e^{-2πi ξ t}`,
so `𝓕 f w` is our kernel evaluated at `ξ = 2πw`) and then applies continuous-function
Fourier inversion `Continuous.fourierInv_fourier_eq`: since `𝓕 f = 0` is trivially
integrable, `f = 𝓕⁻ (𝓕 f) = 𝓕⁻ 0 = 0`.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

namespace Spectra.Fourier

/-- **L¹-Fourier injectivity.** A continuous integrable function on `ℝ` whose
non-`2π`-normalized Fourier transform `∫ t, e^{-i ξ t} f t` vanishes for every `ξ : ℝ`
is identically zero. -/
theorem eq_zero_of_fourierIntegral_eq_zero {f : ℝ → ℂ}
    (hf : Continuous f) (hint : MeasureTheory.Integrable f)
    (h : ∀ ξ : ℝ, ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * f t = 0) :
    f = 0 := by
  -- Step 1: Mathlib's Fourier transform of `f` vanishes: `𝓕 f w` is the hypothesis
  -- kernel at frequency `ξ = 2πw`.
  have hFf_zero : 𝓕 f = 0 := by
    funext w
    rw [Pi.zero_apply, Real.fourier_eq']
    simp only [Real.inner_apply, smul_eq_mul]
    rw [← h (2 * Real.pi * w)]
    refine integral_congr_ae (.of_forall fun v => ?_)
    have h_phase : Complex.exp (((-2 * Real.pi * (v * w) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (-(Complex.I * ((2 * Real.pi * w : ℝ) : ℂ) * (v : ℂ))) := by
      congr 1; push_cast; ring
    simp only [h_phase]
  -- Step 2: Fourier inversion; `𝓕 f = 0` is trivially integrable.
  have hFf_int : Integrable (𝓕 f) volume := by
    rw [hFf_zero]; exact integrable_zero ℝ ℂ volume
  have h_inv := hf.fourierInv_fourier_eq hint hFf_int
  rw [hFf_zero] at h_inv
  have h_zero_inv : 𝓕⁻ (0 : ℝ → ℂ) = 0 := by
    funext w; rw [Real.fourierInv_eq]; simp
  rw [h_zero_inv] at h_inv
  exact h_inv.symm

/-- Pointwise form of `eq_zero_of_fourierIntegral_eq_zero`. -/
theorem apply_eq_zero_of_fourierIntegral_eq_zero {f : ℝ → ℂ}
    (hf : Continuous f) (hint : MeasureTheory.Integrable f)
    (h : ∀ ξ : ℝ, ∫ t : ℝ, Complex.exp (-(Complex.I * ξ * t)) * f t = 0) (t : ℝ) :
    f t = 0 :=
  congr_fun (eq_zero_of_fourierIntegral_eq_zero hf hint h) t

end Spectra.Fourier

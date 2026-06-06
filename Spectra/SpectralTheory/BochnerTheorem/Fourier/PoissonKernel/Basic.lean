/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: BochnerTheorem/Fourier/PoissonKernel.lean
-/
import Spectra.SpectralTheory.BochnerTheorem.Fourier.PoissonKernel.Lemmas
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
/-!
# Fourier Uniqueness for Finite Measures

A finite positive Borel measure on ℝ is uniquely determined by its
characteristic function (Fourier–Stieltjes transform).


## References

* Lévy, P. "Calcul des Probabilités" (1925), §24 (inversion formula)
* Rudin, *Real and Complex Analysis*, 3rd ed., §9.5
* Connects to `lorentzian` already defined in `Routes.lean`

## Tags

Fourier uniqueness, characteristic function, Lévy inversion, Poisson kernel
-/
namespace QuantumMechanics.Bochner.FourierUniqueness

open Complex MeasureTheory Filter Topology Set Fourier FourierTransform

/-- **Fourier transform of the Poisson kernel**: `∫ P_ε(x) e^{ixt} dx = e^{-ε|t|}`.

This is the key identity connecting the Poisson kernel to characteristic functions.
It asserts that the two-sided exponential `t ↦ e^{-ε|t|}` is the Fourier transform
of the Poisson kernel `P_ε(x) = (1/π) · ε/(x² + ε²)`.
-/
theorem poissonKernel_fourier {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∫ x, (poissonKernel ε x : ℂ) * exp (I * ↑x * ↑t) = exp (-(↑ε * ↑|t|) : ℂ) := by
  set f : ℝ → ℂ := fun s => cexp (-(↑ε * ↑|s|)) with hf_def
  have hf_int : Integrable f volume := by
    refine (integrable_two_sided_exp hε 0).congr ?_
    filter_upwards with s
    simp [f, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  have hf_cont : Continuous f :=
    Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_abs)).neg)
  -- (1) closed form for the transform, in the new convention
  have h_Ff : ∀ w : ℝ, 𝓕 f w =
      (((2 * ε) / ((2 * Real.pi * w) ^ 2 + ε ^ 2) : ℝ) : ℂ) := by
    intro w
    rw [Real.fourier_eq']
    have key := fourier_two_sided_exp hε (-(2 * Real.pi * w))
    rw [neg_sq] at key; rw [← key]
    refine integral_congr_ae (.of_forall fun v => ?_)
    simp only [Real.inner_apply, smul_eq_mul, hf_def]
    rw [mul_comm]; norm_num; ring_nf   -- ↑(-2π(v*w))·I  =  I·↑(-(2πw))·↑v
  -- (2) 𝓕 f is integrable: it is a rescaled Poisson kernel
  have h_Ff_int : Integrable (𝓕 f) volume := by
    have hεne : ε ≠ 0 := ne_of_gt hε
    have hR : (2 * Real.pi / ε) ≠ 0 := by positivity
    have h1 : Integrable (fun w : ℝ => (1 + (2 * Real.pi / ε * w) ^ 2)⁻¹) volume :=
      integrable_inv_one_add_sq.comp_mul_left' hR
    have hg : Integrable (fun w : ℝ => 2 * ε / ((2 * Real.pi * w) ^ 2 + ε ^ 2)) volume := by
      refine (h1.const_mul (2 / ε)).congr (.of_forall fun w => ?_)
      have hden : (2 * Real.pi * w) ^ 2 + ε ^ 2 ≠ 0 := by positivity
      have hden2 : (1 : ℝ) + (2 * Real.pi / ε * w) ^ 2 ≠ 0 := by positivity
      field_simp; ring
    rw [show (𝓕 f) = fun w => ((2 * ε / ((2 * Real.pi * w) ^ 2 + ε ^ 2) : ℝ) : ℂ)
          from funext h_Ff]
    exact hg.ofReal
  -- (3) inversion + change of variables x = 2πw
  have h_inv : 𝓕⁻ (𝓕 f) t = f t :=
    hf_int.fourierInv_fourier_eq h_Ff_int hf_cont.continuousAt
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  set g : ℝ → ℂ := fun x => (poissonKernel ε x : ℂ) * Complex.exp (I * ↑x * ↑t) with hg_def
  show (∫ x, g x) = f t
  rw [← h_inv, Real.fourierInv_eq']
  simp_rw [h_Ff, Real.inner_apply, smul_eq_mul]
  -- RHS integrand = ↑(2π) · g(2πv)
  have hStepA :
      (∫ v, Complex.exp (↑(2 * Real.pi * (v * t)) * I)
              * ((2 * ε / ((2 * Real.pi * v) ^ 2 + ε ^ 2) : ℝ) : ℂ))
      = (↑(2 * Real.pi) : ℂ) * ∫ v, g (2 * Real.pi * v) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun v => ?_)
    have hden : ((2 * Real.pi * v) ^ 2 + ε ^ 2 : ℝ) ≠ 0 := by positivity
    have hexp : Complex.exp (↑(2 * Real.pi * (v * t)) * I)
              = Complex.exp (I * ↑(2 * Real.pi * v) * ↑t) := by
      congr 1; push_cast; ring
    have hcoef : ((2 * ε / ((2 * Real.pi * v) ^ 2 + ε ^ 2) : ℝ) : ℂ)
               = ↑(2 * Real.pi) * (↑(poissonKernel ε (2 * Real.pi * v)) : ℂ) := by
      rw [← Complex.ofReal_mul]; congr 1
      unfold poissonKernel; field_simp
    simp only [hg_def]
    rw [hexp, hcoef]; ring
  rw [hStepA]
  have hcomp : (∫ v, g (2 * Real.pi * v)) = |(2 * Real.pi)⁻¹| • ∫ x, g x :=
    Measure.integral_comp_mul_left g (2 * Real.pi)
  rw [hcomp, abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹), Complex.real_smul,
      ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), Complex.ofReal_one, one_mul]


end QuantumMechanics.Bochner.FourierUniqueness

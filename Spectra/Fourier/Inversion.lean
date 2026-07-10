/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Fourier.IsUnique
import Spectra.Kernel.Poisson.Lemmas
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier uniqueness via exponential regularization

This file proves `eq_of_fourier_decay_eq`: if two continuous bounded functions on `ℝ` have
identical regularized Fourier–Laplace transforms `∫ e^{-ist} e^{-ε|t|} f(t) dt` for every
regularization parameter `ε > 0` and every frequency `s`, then the functions are equal.

The proof reduces to ordinary Fourier inversion: fixing `ε = 1`, the difference
`φ(t) = e^{-|t|}(f(t) - g(t))` is continuous and `L¹`, its Fourier transform vanishes identically
by hypothesis, so continuous-function Fourier inversion forces `φ ≡ 0`; since `e^{-|t|} ≠ 0`, this
gives `f = g` pointwise.

## Main results

* `eq_of_fourier_decay_eq` : Fourier uniqueness for continuous bounded functions via
  exponential-decay regularization.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

namespace Spectra.Fourier

/-- **Fourier uniqueness for continuous bounded functions via exponential regularization.**

If two continuous bounded functions on ℝ have identical Fourier–Laplace transforms
`∫ e^{-ist} e^{-ε|t|} f(t) dt` for every regularization parameter `ε > 0` and every
frequency `s ∈ ℝ`, then the functions are equal.

The proof is the standard Fourier-uniqueness argument: for each fixed `ε > 0`,
`φ_ε(t) := e^{-ε|t|}(f(t) − g(t))` is continuous and `L¹` (its norm is dominated by
the integrable two-sided exponential `e^{-ε|t|}`), and its Fourier transform vanishes
identically because the hypothesis is the linearity-difference of the two sides.
Continuous-function Fourier inversion (`Continuous.fourierInv_fourier_eq`) then gives
`φ_ε ≡ 0`, and since `e^{-ε|t|} ≠ 0`, we conclude `f = g` pointwise. -/
theorem eq_of_fourier_decay_eq {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hfb : ∃ C, ∀ t, ‖f t‖ ≤ C) (hgb : ∃ C, ∀ t, ‖g t‖ ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ∀ s : ℝ,
    (∫ (t : ℝ), cexp (-(I * (s : ℂ) * (t : ℂ))) *
                cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ))) * f t)
      = ∫ (t : ℝ), cexp (-(I * (s : ℂ) * (t : ℂ))) *
                   cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ))) * g t) :
    f = g := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  -- Define φ(t) := e^{-|t|}(f(t) − g(t)); we specialize ε = 1.
  set φ : ℝ → ℂ := fun t => cexp (-((|t| : ℝ) : ℂ)) * (f t - g t) with hφ_def
  -- φ is continuous.
  have hφ_cont : Continuous φ := by
    refine Continuous.mul ?_ (hf.sub hg)
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_abs).neg)
  -- e^{-|t|} is integrable (specialize integrable_two_sided_exp at ε = 1, ξ = 0).
  have h_exp_int : Integrable (fun t : ℝ => cexp (-((|t| : ℝ) : ℂ))) volume := by
    refine (integrable_two_sided_exp one_pos 0).congr ?_
    filter_upwards with t; simp
  -- φ is integrable: e^{-|t|} integrable times the bounded function (f − g).
  have hφ_int : Integrable φ volume := by
    refine h_exp_int.mul_bdd (c := Cf + Cg) (hf.sub hg).aestronglyMeasurable ?_
    filter_upwards with t
    exact (norm_sub_le _ _).trans (by linarith [hCf t, hCg t])
  -- Key step: 𝓕 φ = 0 everywhere.
  have hFφ_zero : 𝓕 φ = 0 := by
    funext w
    rw [Pi.zero_apply, Real.fourier_eq']
    simp only [Real.inner_apply, smul_eq_mul, hφ_def]
    -- Specialize the hypothesis at ε = 1, s = 2π·w; this is exactly 𝓕 φ at w
    -- (modulo Mathlib's 2π convention and a trivial sign / cast rearrangement).
    have h_at := h 1 one_pos (2 * Real.pi * w)
    -- Rewrite the 𝓕-integrand as a difference (f-side) − (g-side) matching `h_at`.
    have h_integrand : ∀ v : ℝ,
        Complex.exp (((-2 * Real.pi * (v * w) : ℝ) : ℂ) * Complex.I) *
          (cexp (-((|v| : ℝ) : ℂ)) * (f v - g v)) =
        cexp (-(I * ((2 * Real.pi * w : ℝ) : ℂ) * ((v : ℝ) : ℂ))) *
            cexp (-(((1 : ℝ) : ℂ) * ((|v| : ℝ) : ℂ))) * f v -
        cexp (-(I * ((2 * Real.pi * w : ℝ) : ℂ) * ((v : ℝ) : ℂ))) *
            cexp (-(((1 : ℝ) : ℂ) * ((|v| : ℝ) : ℂ))) * g v := by
      intro v
      have h_phase :
          Complex.exp (((-2 * Real.pi * (v * w) : ℝ) : ℂ) * Complex.I) =
          cexp (-(I * ((2 * Real.pi * w : ℝ) : ℂ) * ((v : ℝ) : ℂ))) := by
        congr 1; push_cast; ring
      have h_decay :
          cexp (-((|v| : ℝ) : ℂ)) =
          cexp (-(((1 : ℝ) : ℂ) * ((|v| : ℝ) : ℂ))) := by
        congr 1; push_cast; ring
      rw [h_phase, h_decay]; ring
    -- The phase × decay kernel is integrable (a sign-flip away from `integrable_two_sided_exp`).
    have h_kernel : Integrable (fun v : ℝ =>
        cexp (-(I * ((2 * Real.pi * w : ℝ) : ℂ) * ((v : ℝ) : ℂ))) *
        cexp (-(((1 : ℝ) : ℂ) * ((|v| : ℝ) : ℂ)))) volume := by
      refine (integrable_two_sided_exp one_pos (-(2 * Real.pi * w))).congr ?_
      filter_upwards with v
      have h_phase' :
          cexp (I * ((-(2 * Real.pi * w) : ℝ) : ℂ) * ((v : ℝ) : ℂ)) =
          cexp (-(I * ((2 * Real.pi * w : ℝ) : ℂ) * ((v : ℝ) : ℂ))) := by
        congr 1; push_cast; ring
      rw [h_phase']; ring
    -- Both sides are integrable (kernel × bounded function).
    have h_int_F : Integrable (fun v : ℝ =>
        cexp (-(I * ((2 * Real.pi * w : ℝ) : ℂ) * ((v : ℝ) : ℂ))) *
        cexp (-(((1 : ℝ) : ℂ) * ((|v| : ℝ) : ℂ))) * f v) volume :=
      h_kernel.mul_bdd hf.aestronglyMeasurable (.of_forall hCf)
    have h_int_G : Integrable (fun v : ℝ =>
        cexp (-(I * ((2 * Real.pi * w : ℝ) : ℂ) * ((v : ℝ) : ℂ))) *
        cexp (-(((1 : ℝ) : ℂ) * ((|v| : ℝ) : ℂ))) * g v) volume :=
      h_kernel.mul_bdd hg.aestronglyMeasurable (.of_forall hCg)
    rw [integral_congr_ae (.of_forall h_integrand), integral_sub h_int_F h_int_G]
    exact sub_eq_zero.mpr h_at
  -- Fourier inversion: φ continuous + 𝓕 φ = 0 (hence integrable) ⟹ φ = 𝓕⁻ 0 = 0.
  have hφ_zero : φ = 0 := by
    have hFφ_int : Integrable (𝓕 φ) volume := by
      rw [hFφ_zero]; exact integrable_zero ℝ ℂ volume
    have h_inv := hφ_cont.fourierInv_fourier_eq hφ_int hFφ_int
    rw [hFφ_zero] at h_inv
    have h_zero_inv : 𝓕⁻ (0 : ℝ → ℂ) = 0 := by
      funext w; rw [Real.fourierInv_eq]; simp
    rw [h_zero_inv] at h_inv
    exact h_inv.symm
  -- Pointwise: e^{-|t|} ≠ 0 forces f(t) − g(t) = 0, hence f = g.
  funext t
  have hφt : φ t = 0 := congr_fun hφ_zero t
  simp only [hφ_def] at hφt
  rcases mul_eq_zero.mp hφt with h_exp_zero | h_diff_zero
  · exact absurd h_exp_zero (Complex.exp_ne_zero _)
  · exact sub_eq_zero.mp h_diff_zero


end Spectra.Fourier

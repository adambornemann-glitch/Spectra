/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Fourier.Identity
/-!
# Regularized Fubini for the Poisson-Density Fourier Identity

The single lemma `fubini_regularized` is the regularized-Fubini step between
`Spectra.Fourier.fourier_identity` and the Poisson-density identity it feeds
(`fourier_integral_eq_density` in `Bochner/Borel/Density.lean`): it swaps the order of the
double integral `∫_λ (∫_t e^{-iλt} e^{-ε|t|} ⟨ξ,U(t)ξ⟩ dt) · e^{-δ|λ|} dλ` and evaluates the
resulting inner λ-integral against the Poisson kernel, collapsing the whole expression to
`∫_t e^{-ε|t|} ⟨ξ,U(t)ξ⟩ · (2δ/(t²+δ²)) dt`.

## Main statements

* `fubini_regularized` — the double-integral swap and Poisson-kernel evaluation described above.

## Implementation notes

The swap itself is ordinary Fubini for the jointly-integrable product kernel; the inner
λ-integral is then evaluated via `Spectra.Fourier.fourier_kernel_eval` (`Fourier/Identity.lean`),
the Fourier transform of the two-sided exponential specialized to the Poisson kernel.
-/
open Complex MeasureTheory
open scoped InnerProductSpace
open Spectra.OneParameterUnitaryGroup
open Spectra.Fourier
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Borel
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Integrate `fourier_identity`'s integrand `e^{-iλt}e^{-ε|t|}⟨ξ,U(t)ξ⟩` against `e^{-δ|λ|}`,
swap the order of integration, and evaluate the resulting λ-integral against the Poisson
kernel: the double integral collapses to `∫_t e^{-ε|t|}⟨ξ,U(t)ξ⟩·(2δ/(t²+δ²))dt`, the input to
the Poisson-kernel density in `Bochner/Borel/Density.lean`. -/
lemma fubini_regularized
    (ξ : H)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    (∫ lambda : ℝ,
        (∫ t : ℝ, cexp (-(I * (lambda : ℂ) * (t : ℂ))) *
                  cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ)
        * (Real.exp (-(δ * |lambda|)) : ℂ))
      = ∫ t : ℝ,
          cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ
          * ((2 * δ / (t ^ 2 + δ ^ 2) : ℝ) : ℂ) := by
  let F : ℝ → ℝ → ℂ := fun lambda t =>
    cexp (-(I * (lambda : ℂ) * (t : ℂ))) * cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ *
    (Real.exp (-(δ * |lambda|)) : ℂ)
  -- e^{-δ|·|} and e^{-ε|·|} are integrable (integrable_two_sided_exp at frequency 0).
  have hδ_int : Integrable (fun lambda : ℝ => Real.exp (-(δ * |lambda|))) volume := by
    refine ((integrable_two_sided_exp hδ 0).norm).congr ?_
    filter_upwards with lambda
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, Complex.norm_exp]
    congr 1; simp [Complex.mul_re]
  have hε_int : Integrable (fun t : ℝ => Real.exp (-(ε * |t|))) volume := by
    refine ((integrable_two_sided_exp hε 0).norm).congr ?_
    filter_upwards with t
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, Complex.norm_exp]
    congr 1; simp [Complex.mul_re]
  -- Joint integrability of uncurry F via the product dominator.
  have hF_int : Integrable (Function.uncurry F) (volume.prod volume) := by
    have h_meas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
      apply Continuous.aestronglyMeasurable
      change Continuous (fun p : ℝ × ℝ =>
        cexp (-(I * (p.1 : ℂ) * (p.2 : ℂ))) * cexp (-(↑ε * ↑|p.2|)) * ⟪ξ, U_grp.U p.2 ξ⟫_ℂ *
        (Real.exp (-(δ * |p.1|)) : ℂ))
      refine Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) ?_
      · exact Complex.continuous_exp.comp (by fun_prop)
      · exact Complex.continuous_exp.comp (by fun_prop)
      · exact (Continuous.inner continuous_const (U_grp.strong_continuous ξ)).comp continuous_snd
      · exact Complex.continuous_ofReal.comp (by fun_prop)
    have h_dom : Integrable
        (fun p : ℝ × ℝ => ‖ξ‖ ^ 2 * (Real.exp (-(δ * |p.1|)) * Real.exp (-(ε * |p.2|))))
        (volume.prod volume) :=
      (hδ_int.mul_prod hε_int).const_mul _
    refine h_dom.mono' h_meas ?_
    filter_upwards with p
    change ‖cexp (-(I * (p.1 : ℂ) * (p.2 : ℂ))) * cexp (-(↑ε * ↑|p.2|)) * ⟪ξ, U_grp.U p.2 ξ⟫_ℂ *
          (Real.exp (-(δ * |p.1|)) : ℂ)‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_real]
    have h1 : (-(I * (p.1 : ℂ) * (p.2 : ℂ))).re = 0 := by
      rw [Complex.neg_re, re_I_mul_ofReal_mul_ofReal, neg_zero]
    have h2 : (-((ε : ℂ) * (|p.2|))).re = -(ε * |p.2|) := by
      simp [Complex.mul_re]
    simp only [h1, h2, Real.exp_zero, one_mul, Real.norm_eq_abs, Real.abs_exp, ge_iff_le]
    have h_inner : ‖⟪ξ, U_grp.U p.2 ξ⟫_ℂ‖ ≤ ‖ξ‖ ^ 2 :=
      calc ‖⟪ξ, U_grp.U p.2 ξ⟫_ℂ‖ ≤ ‖ξ‖ * ‖U_grp.U p.2 ξ‖ := norm_inner_le_norm _ _
        _ = ‖ξ‖ * ‖ξ‖ := by rw [norm_preserving U_grp p.2 ξ]
        _ = ‖ξ‖ ^ 2 := by ring
    calc Real.exp (-(ε * |p.2|)) * ‖⟪ξ, U_grp.U p.2 ξ⟫_ℂ‖ * Real.exp (-(δ * |p.1|))
        ≤ Real.exp (-(ε * |p.2|)) * ‖ξ‖ ^ 2 * Real.exp (-(δ * |p.1|)) := by gcongr
      _ = ‖ξ‖ ^ 2 * (Real.exp (-(δ * |p.1|)) * Real.exp (-(ε * |p.2|))) := by ring
  -- Pull e^{-δ|λ|} inside, swap, evaluate the λ-integral.
  have h_pullin : (∫ lambda : ℝ,
        (∫ t : ℝ, cexp (-(I * (lambda : ℂ) * (t : ℂ))) *
                  cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ)
        * (Real.exp (-(δ * |lambda|)) : ℂ)) = ∫ lambda : ℝ, ∫ t : ℝ, F lambda t := by
    congr 1; funext lambda; rw [← integral_mul_const]
  rw [h_pullin, integral_integral_swap (f := F) hF_int]
  congr 1; funext t
  have hreorder : (fun lambda : ℝ => F lambda t) =
        (fun lambda : ℝ => (cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ) *
          (cexp (-(I * (lambda : ℂ) * (t : ℂ))) * (Real.exp (-(δ * |lambda|)) : ℂ))) := by
    funext lambda; show F lambda t = _; simp only [F]; ring
  rw [hreorder, integral_const_mul, fourier_kernel_eval hδ t]

end Spectra.Borel

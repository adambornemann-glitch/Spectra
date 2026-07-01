/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Bochner/Borel/Fubini.lean
-/
import Spectra.Fourier.Identity
import Spectra.Resolvent.Diagonal.Basic

open Complex MeasureTheory
open scoped InnerProductSpace
open Spectra.OneParameterUnitaryGroup
open Spectra.Fourier
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Borel
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Integrate `key_identity`'s integrand
against `e^{-δ|λ|}`, swap, evaluate. -/
lemma fubini_regularized
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
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
      show Continuous (fun p : ℝ × ℝ =>
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
    show ‖cexp (-(I * (p.1 : ℂ) * (p.2 : ℂ))) * cexp (-(↑ε * ↑|p.2|)) * ⟪ξ, U_grp.U p.2 ξ⟫_ℂ *
          (Real.exp (-(δ * |p.1|)) : ℂ)‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_real]
    have h1 : (-(I * (p.1 : ℂ) * (p.2 : ℂ))).re = 0 := by simp [Complex.mul_re]
    have h2 : (-((ε : ℂ) * (|p.2|))).re = -(ε * |p.2|) := by
      simp [Complex.mul_re]
    simp [h1, h2, Real.exp_zero, one_mul, abs_of_pos (Real.exp_pos _)]
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

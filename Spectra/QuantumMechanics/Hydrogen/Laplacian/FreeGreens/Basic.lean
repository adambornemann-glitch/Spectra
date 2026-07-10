/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Basic
import Spectra.SpectralTheory.Essential.Weyl
/-! ## The free Green's function

For explicit spectral computations we record the free Green's function
`G_z(x) = e^{−√(−z)|x|} / (4π|x|)`, with the principal branch of the square root
(so `Re √(−z) > 0` whenever `Im z ≠ 0`). This file proves, fully and without `sorry`:
the exponential decay of `G_z` (`freeGreensFunction_decay`), the Fourier-multiplier
form of the resolvent `(−Δ − z)⁻¹` (`fourierL2_selfAdjointResolvent`), and a
Laplace-type integral identity (`integral_exp_neg_mul_sin`) feeding the radial
Fourier computation. What remains future work (not attempted here) is tying the
*explicit* kernel `G_z` itself to the resolvent via convolution, i.e. showing
`R_z f =ᵐ G_z ⋆ f`; the Track-A route to the essential spectrum of the hydrogen
Laplacian bypasses that identity entirely (see `SpectralTheory.Essential.Weyl`),
so it is banked here but not needed downstream. -/
open MeasureTheory Complex
open Spectra.Sobolev
open Spectra.Resolvent
open Spectra.Essential
open Spectra.Operator
open Spectra.QuantumMechanics.SpectralTheory
open FourierTransform
open scoped Topology NNReal ENNReal SchwartzMap ContDiff

namespace Spectra.QuantumMechanics.Hydrogen

/-- **A Laplace-type integral** `∫₀^∞ e^{−w r} sin(a r) dr = a / (w² + a²)` for `Re w > 0`.

After the angular integration, the 3-D Fourier transform of the radial Yukawa profile `e^{−w r}`
reduces to exactly this one-dimensional integral (with `w = (−z)^{1/2}`, `a = 2π‖ξ‖`). Proof:
expand `sin` via complex exponentials and integrate the two decaying exponentials `e^{−(w ± ia) r}`,
both of which have strictly negative real part in the exponent. -/
theorem integral_exp_neg_mul_sin (w : ℂ) (hw : 0 < w.re) (a : ℝ) :
    ∫ r in Set.Ioi (0 : ℝ), Complex.exp (-w * r) * (Real.sin (a * r) : ℂ)
      = (a : ℂ) / (w ^ 2 + (a : ℂ) ^ 2) := by
  have hp : (-(w + (a : ℂ) * Complex.I)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero]; linarith
  have hm : (-(w - (a : ℂ) * Complex.I)).re < 0 := by
    simp only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_zero]; linarith
  have hne1 : w + (a : ℂ) * Complex.I ≠ 0 := by intro h; rw [h] at hp; simp at hp
  have hne2 : w - (a : ℂ) * Complex.I ≠ 0 := by intro h; rw [h] at hm; simp at hm
  have hfactor : w ^ 2 + (a : ℂ) ^ 2
      = (w + (a : ℂ) * Complex.I) * (w - (a : ℂ) * Complex.I) := by
    linear_combination ((a : ℂ) ^ 2) * Complex.I_sq
  -- rewrite the integrand as a difference of two decaying exponentials.
  have hcongr : ∀ r : ℝ, Complex.exp (-w * r) * (Real.sin (a * r) : ℂ)
      = Complex.I / 2 * Complex.exp (-(w + (a : ℂ) * Complex.I) * (r : ℂ))
        - Complex.I / 2 * Complex.exp (-(w - (a : ℂ) * Complex.I) * (r : ℂ)) := by
    intro r
    rw [Complex.ofReal_sin, Complex.ofReal_mul]
    simp only [Complex.sin]
    rw [show -(w + (a : ℂ) * Complex.I) * (r : ℂ)
          = -w * (r : ℂ) + -((a : ℂ) * (r : ℂ)) * Complex.I from by ring,
        show -(w - (a : ℂ) * Complex.I) * (r : ℂ)
          = -w * (r : ℂ) + (a : ℂ) * (r : ℂ) * Complex.I from by ring,
        Complex.exp_add, Complex.exp_add]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => hcongr r),
    MeasureTheory.integral_sub
      ((integrableOn_exp_mul_complex_Ioi hp 0).const_mul (Complex.I / 2))
      ((integrableOn_exp_mul_complex_Ioi hm 0).const_mul (Complex.I / 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_exp_mul_complex_Ioi hp 0, integral_exp_mul_complex_Ioi hm 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, mul_one_div]
  rw [div_sub_div _ _ hne1 hne2, ← hfactor]
  congr 1
  linear_combination (-(a : ℂ)) * Complex.I_sq

/-- The free Green's function `G_z(x) = e^{−√(−z)|x|}/(4π|x|)`, principal branch of
the square root; `0` at the origin. -/
noncomputable def freeGreensFunction (z : ℂ) : R3 → ℂ := fun x =>
  if ‖x‖ = 0 then 0
  else Complex.exp (-((-z) ^ ((1 : ℂ) / 2)) * (‖x‖ : ℂ)) /
    ((4 * Real.pi * ‖x‖ : ℝ) : ℂ)

/-- The Green's function decays exponentially with rate `Re √(−z) > 0`.

Direct from the explicit formula: the witness is `c = Re((−z)^{1/2}) > 0`, since
`−z ∉ [0, ∞)` when `Im z ≠ 0` and the principal branch maps `ℂ ∖ [0, ∞)` into the
open right half-plane. -/
theorem freeGreensFunction_decay (z : ℂ) (hz : z.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : R3, x ≠ 0 →
      ‖freeGreensFunction z x‖ ≤
        Real.exp (-c * ‖x‖) / (4 * Real.pi * ‖x‖) := by
  have hz' : -z ≠ 0 := neg_ne_zero.mpr (by rintro rfl; simp at hz)
  set w : ℂ := (-z) ^ ((1 : ℂ) / 2) with hw
  refine ⟨w.re, ?_, ?_⟩
  · -- `Re((−z)^{1/2}) = ‖−z‖^{1/2}·cos(arg(−z)/2) > 0`, since `arg(−z) ∈ (−π, π)`.
    have harg_gt : -Real.pi < Complex.arg (-z) := Complex.neg_pi_lt_arg (-z)
    have harg_lt : Complex.arg (-z) < Real.pi := by
      rcases (Complex.arg_le_pi (-z)).lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.arg_eq_pi_iff.mp h).2 (by simpa using hz)
    rw [hw, Complex.cpow_def_of_ne_zero hz', Complex.exp_re]
    refine mul_pos (Real.exp_pos _) ?_
    have h12 : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    have him : (Complex.log (-z) * ((1 : ℂ) / 2)).im = Complex.arg (-z) / 2 := by
      rw [h12, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.log_im]; ring
    rw [him]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  · intro x hx
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hdenom_pos : 0 < 4 * Real.pi * ‖x‖ :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) hxpos
    refine le_of_eq ?_
    have hval : freeGreensFunction z x
        = Complex.exp (-w * (‖x‖ : ℂ)) / ((4 * Real.pi * ‖x‖ : ℝ) : ℂ) := by
      rw [freeGreensFunction, if_neg hxn, ← hw]
    have hre : (-w * (‖x‖ : ℂ)).re = -w.re * ‖x‖ := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hval, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdenom_pos, hre]

/-- **The free resolvent acts as the Fourier multiplier `(laplacianSymbol ξ − z)⁻¹`.**

In momentum space `(−Δ − z)⁻¹` is division by `laplacianSymbol ξ − z = (2π)²‖ξ‖² − z`,
which never vanishes because `z.im ≠ 0` forces `Im(laplacianSymbol ξ − z) = −z.im ≠ 0`.

This expresses the resolvent as multiplication on the Fourier side, with **no
Green's-function analytics**. The proof applies the (linear, isometric) Fourier
transform to the resolvent equation `(−Δ − z)(R_z f) = f`
(`selfAdjointResolvent_solves`) and diagonalises `−Δ` with `fourier_weakLaplacian`.
Connecting this to the *explicit* kernel `G_z` (i.e. `R_z f =ᵐ G_z ⋆ f`) would need
the Fourier transform of `G_z` itself, which is future work (see the module
docstring above); it is not needed for the current Track-A route to the essential
spectrum. -/
theorem fourierL2_selfAdjointResolvent (z : ℂ) (hz : z.im ≠ 0) (f : l2R3) :
    (fourierL2 (selfAdjointResolvent laplacian_isSelfAdjoint z hz f) : R3 → ℂ)
      =ᵐ[volume] fun ξ => ((laplacianSymbol ξ : ℂ) - z)⁻¹ * (fourierL2 f : R3 → ℂ) ξ := by
  have hmem : MemSobolevH2 (selfAdjointResolvent laplacian_isSelfAdjoint z hz f) :=
    selfAdjointResolvent_mem_domain laplacian_isSelfAdjoint z hz f
  -- the resolvent equation in L²: `(−Δ)(R_z f) − z • (R_z f) = f`.
  have hsolve : weakLaplacian (selfAdjointResolvent laplacian_isSelfAdjoint z hz f) hmem
      - z • selfAdjointResolvent laplacian_isSelfAdjoint z hz f = f := by
    have h := selfAdjointResolvent_solves laplacian_isSelfAdjoint z hz f
    rwa [laplacianPMap_apply] at h
  set u : l2R3 := selfAdjointResolvent laplacian_isSelfAdjoint z hz f with _hu
  -- apply the linear isometry `fourierL2` to the resolvent equation.
  have hF : fourierL2 (weakLaplacian u hmem) - z • fourierL2 u = fourierL2 f := by
    rw [← hsolve, map_sub, map_smul]
  -- a.e. identities of the L² representatives, using `fourier_weakLaplacian`.
  have hWL := fourier_weakLaplacian u hmem
  have hf_ae : (fourierL2 f : R3 → ℂ)
      =ᵐ[volume] fun ξ => ((laplacianSymbol ξ : ℂ) - z) * (fourierL2 u : R3 → ℂ) ξ := by
    rw [← hF]
    filter_upwards [Lp.coeFn_sub (fourierL2 (weakLaplacian u hmem)) (z • fourierL2 u),
      Lp.coeFn_smul z (fourierL2 u), hWL] with ξ hsub hsmul hwl
    rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hwl]; ring
  -- divide through by the non-vanishing symbol.
  filter_upwards [hf_ae] with ξ hξ
  have hne : (laplacianSymbol ξ : ℂ) - z ≠ 0 := by
    intro hcontra
    apply hz
    have him : -z.im = 0 := by
      have := congrArg Complex.im hcontra
      simpa [Complex.sub_im, Complex.ofReal_im] using this
    linarith
  rw [hξ, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Spectra.QuantumMechanics.Hydrogen

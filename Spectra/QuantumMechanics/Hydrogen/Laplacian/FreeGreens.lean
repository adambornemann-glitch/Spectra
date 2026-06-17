/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Basic

noncomputable section

open MeasureTheory Complex Filter InnerProductSpace
open Spectra.Sobolev
open Spectra.OneParameterUnitaryGroup
open Spectra.Stoneslemma
open Spectra.StonesTheorem
open Spectra.Resolvent
open Spectra.QuantumMechanics.Observable
open Spectra.QuantumMechanics.SpectralTheory
open FourierTransform
open scoped Topology NNReal ENNReal SchwartzMap ContDiff

namespace Spectra.QuantumMechanics.Hydrogen
/-! ## The free Green's function

For explicit spectral computations we record the free Green's function
`G_z(x) = e^{−√(−z)|x|} / (4π|x|)`, with the principal branch of the square root
(so `Re √(−z) > 0` whenever `Im z ≠ 0`). Tying it to `selfAdjointResolvent`, and
the exponential decay, both require the radial Fourier computation, so the two
identities below are left open. -/

/-- The free Green's function `G_z(x) = e^{−√(−z)|x|}/(4π|x|)`, principal branch of
the square root; `0` at the origin. -/
def freeGreensFunction (z : ℂ) : R3 → ℂ := fun x =>
  if ‖x‖ = 0 then 0
  else Complex.exp (-((-z) ^ ((1 : ℂ) / 2)) * (‖x‖ : ℂ)) /
    ((4 * Real.pi * ‖x‖ : ℝ) : ℂ)

/-- The Green's function decays exponentially with rate `Re √(−z) > 0`.

Direct from the explicit formula: the witness is `c = Re((−z)^{1/2}) > 0`, since
`−z ∉ [0, ∞)` when `Im z ≠ 0` and the principal branch maps `ℂ ∖ [0, ∞)` into the
open right half-plane. Left open (elementary but `cpow`-fiddly). -/
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

/-
/-- The Green's function is the integral kernel of the free resolvent.

Verify `𝓕[G_z](ξ) = 1/(|ξ|² − z)` by the radial contour computation, then
Plancherel turns multiplication by `1/(|ξ|² − z)` into convolution with `G_z`.
Needs the Fourier characterization of `−Δ`; left open. -/
theorem freeGreensFunction_is_resolvent_kernel
    (z : ℂ) (hz : z.im ≠ 0) (f : L2_R3) :
    ∀ᵐ x : R3,
      (selfAdjointResolvent laplacian_isSelfAdjoint z hz f : R3 → ℂ) x =
      ∫ y, freeGreensFunction z (x - y) * (f : R3 → ℂ) y :=
  sorry
-/

end Spectra.QuantumMechanics.Hydrogen

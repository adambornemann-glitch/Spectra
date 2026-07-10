/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.SphereIntegral

/-!
# The free resolvent symbol as an L² element

Toward Coulomb relative compactness we need the free Green's function `G_z ∈ L²(ℝ³)`, but
**only that it is square-integrable** — not its explicit form `e^{−√(−z)|x|}/(4π|x|)`.  Square
integrability is elementary: by Plancherel `‖G_z‖₂ = ‖(laplacianSymbol · − z)⁻¹‖₂`, and the
resolvent symbol `(laplacianSymbol ξ − z)⁻¹` is in `L²` because
`∫_{ℝ³}|(4π²‖ξ‖² − z)|⁻² dξ < ∞` (the integrand is **radial**, decaying like `‖ξ‖⁻⁴`).
This file proves square integrability of that momentum-space symbol, sidestepping the whole
Yukawa-Fourier-transform / sphere-integration thread.

## Main statements

- `memLp_inv_laplacianSymbol_sub` — the free resolvent symbol `(laplacianSymbol ξ − z)⁻¹` is
  in `L²(ℝ³)` for every `z` with `z.im ≠ 0`.
-/
open MeasureTheory Set Complex
open Spectra.Sobolev

namespace Spectra.QuantumMechanics.Hydrogen

/-- The radial profile of `‖(laplacianSymbol ξ − z)⁻¹‖²`:
`1/(((2π)²r² − a)² + b²)`. -/
private noncomputable def resolventRadial (a b r : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * r ^ 2 - a) ^ 2 + b ^ 2)⁻¹

/-- The one-dimensional radial integrand `r² · resolventRadial` is integrable on `(0,∞)`:
continuous near `0`, and `O(r⁻²)` at infinity. -/
private lemma integrableOn_sq_resolventRadial (a b : ℝ) (hb : b ≠ 0) :
    IntegrableOn (fun r : ℝ => r ^ 2 * resolventRadial a b r) (Ioi 0) := by
  have hden_pos : ∀ r : ℝ, (0 : ℝ) < ((2 * Real.pi) ^ 2 * r ^ 2 - a) ^ 2 + b ^ 2 := by
    intro r; have : (0 : ℝ) < b ^ 2 := by positivity
    positivity
  have hcont : Continuous (fun r : ℝ => r ^ 2 * resolventRadial a b r) := by
    unfold resolventRadial
    refine (continuous_pow 2).mul (Continuous.inv₀ ?_ (fun r => (hden_pos r).ne'))
    fun_prop
  set R : ℝ := 1 + |a| with hR
  have hR0 : 0 < R := by rw [hR]; positivity
  rw [show Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R from (Ioc_union_Ioi_eq_Ioi hR0.le).symm]
  refine IntegrableOn.union ?_ ?_
  · -- near `0`: continuous on the compact `[0,R]`.
    exact ((hcont.continuousOn).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  · -- tail: dominate by `(4/(2π)⁴) · r⁻²`.
    have hpi36 : (36 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    have hdom : IntegrableOn (fun r : ℝ => (4 / (2 * Real.pi) ^ 4) * r ^ (-2 : ℝ)) (Ioi R) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hR0).const_mul _
    refine hdom.mono' (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [mem_Ioi] at hr
    have hr0 : 0 < r := hR0.trans hr
    have hr1 : (1 : ℝ) ≤ r := by rw [hR] at hr; linarith [abs_nonneg a]
    have hrabs : |a| ≤ r := by rw [hR] at hr; linarith
    have hr2 : |a| ≤ r ^ 2 := by
      nlinarith [hrabs, hr1, mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ r - 1)]
    have hge : a ≤ (2 * Real.pi) ^ 2 * r ^ 2 / 2 := by
      nlinarith [hpi36, hr2, le_abs_self a, abs_nonneg a, sq_nonneg r]
    have hineq : (2 * Real.pi) ^ 4 * r ^ 4
        ≤ 4 * (((2 * Real.pi) ^ 2 * r ^ 2 - a) ^ 2 + b ^ 2) := by
      have hu : (2 * Real.pi) ^ 2 * r ^ 2 / 2 ≤ (2 * Real.pi) ^ 2 * r ^ 2 - a := by linarith [hge]
      have hw0 : (0:ℝ) ≤ (2 * Real.pi) ^ 2 * r ^ 2 / 2 := by positivity
      nlinarith [hu, mul_nonneg (sub_nonneg.mpr hu) (by linarith [hu, hw0] :
        (0:ℝ) ≤ ((2 * Real.pi) ^ 2 * r ^ 2 - a) + (2 * Real.pi) ^ 2 * r ^ 2 / 2), sq_nonneg b]
    have hnn : 0 ≤ r ^ 2 * resolventRadial a b r :=
      mul_nonneg (sq_nonneg r) (le_of_lt (inv_pos.mpr (hden_pos r)))
    have hgr : (4 / (2 * Real.pi) ^ 4) * r ^ (-2 : ℝ) = 4 / ((2 * Real.pi) ^ 4 * r ^ 2) := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num, Real.rpow_neg hr0.le, Real.rpow_natCast]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hgr]
    rw [le_div_iff₀ (mul_pos (by positivity) (pow_pos hr0 2))]
    unfold resolventRadial
    rw [show r ^ 2 * (((2 * Real.pi) ^ 2 * r ^ 2 - a) ^ 2 + b ^ 2)⁻¹ * ((2 * Real.pi) ^ 4 * r ^ 2)
        = ((2 * Real.pi) ^ 4 * r ^ 4) / (((2 * Real.pi) ^ 2 * r ^ 2 - a) ^ 2 + b ^ 2) from by ring]
    rw [div_le_iff₀ (hden_pos r)]
    nlinarith [hineq]

/-- **A1: the resolvent symbol `(laplacianSymbol ξ − z)⁻¹` is in `L²(ℝ³)`** for
`z.im ≠ 0`. -/
theorem memLp_inv_laplacianSymbol_sub (z : ℂ) (hz : z.im ≠ 0) :
    MemLp (fun ξ : R3 => ((laplacianSymbol ξ : ℂ) - z)⁻¹) 2 volume := by
  have hne : ∀ ξ : R3, (laplacianSymbol ξ : ℂ) - z ≠ 0 := by
    intro ξ h
    apply hz
    have him : ((laplacianSymbol ξ : ℂ) - z).im = 0 := by rw [h]; simp
    simpa [Complex.sub_im, Complex.ofReal_im] using him
  have hcont : Continuous (fun ξ : R3 => ((laplacianSymbol ξ : ℂ) - z)⁻¹) := by
    refine Continuous.inv₀ (Continuous.sub ?_ continuous_const) hne
    exact Complex.continuous_ofReal.comp (by unfold laplacianSymbol; fun_prop)
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  -- `‖(symbol ξ − z)⁻¹‖² = resolventRadial z.re z.im ‖ξ‖`.
  have hsq : (fun ξ : R3 => ‖((laplacianSymbol ξ : ℂ) - z)⁻¹‖ ^ 2)
      = fun ξ : R3 => resolventRadial z.re z.im ‖ξ‖ := by
    funext ξ
    rw [norm_inv, inv_pow, resolventRadial]
    congr 1
    have hnsq : ‖(laplacianSymbol ξ : ℂ) - z‖ ^ 2
        = (laplacianSymbol ξ - z.re) ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hnsq]; unfold laplacianSymbol; ring
  rw [hsq, integrable_fun_norm_addHaar]
  have hfin : Module.finrank ℝ R3 - 1 = 2 := by simp
  rw [hfin]
  simpa only [smul_eq_mul] using integrableOn_sq_resolventRadial z.re z.im hz

end Spectra.QuantumMechanics.Hydrogen

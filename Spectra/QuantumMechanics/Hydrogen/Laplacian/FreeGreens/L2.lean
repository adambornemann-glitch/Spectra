/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The free Green's function as an `L¹` and `L²` element

The free Green's function `G_z(x) = e^{−√(−z)|x|}/(4π|x|)` decays exponentially
(`freeGreensFunction_decay`), so its only integrability worry is the `1/|x|` singularity at
the origin.  In dimension three the radial Jacobian `r² = r^{dim − 1}` cancels that singularity:

* **M1** `‖G_z‖₁`: the radial integrand is `r² · e^{−c r}/(4π r) = (1/4π) · r · e^{−c r}`,
  which is continuous at `0` and `O(e^{−c r})` at infinity, hence integrable on `(0,∞)`.
* **M2** `‖G_z‖₂²`: the radial integrand is `r² · (e^{−c r}/(4π r))² = (1/16π²) · e^{−2c r}`,
  again continuous at `0` and `O(e^{−2c r})` at infinity.

Both reductions use Mathlib's radial change of variables `integrable_fun_norm_addHaar`
(`∫ f(‖x‖) dx` ↔ a 1-D integral of `r^{dim−1} • f r` over `(0,∞)`) together with the exponential
decay test `integrable_of_isBigO_exp_neg`.  The genuine `‖G_z‖^p` is then dominated by the radial
profile via `Integrable.mono'`.

The `L²` witness is packaged as an honest `Lp` element `freeGreensL2 z hz` together with the a.e.
identification `coeFn_freeGreensL2` with `freeGreensFunction z`.

## Main statements

* `aestronglyMeasurable_freeGreensFunction` — `freeGreensFunction z` is a.e.-strongly measurable.
* `memL1_freeGreensFunction` — `freeGreensFunction z ∈ L¹(ℝ³)` for `Im z ≠ 0`.
* `memL2_freeGreensFunction` — `freeGreensFunction z ∈ L²(ℝ³)` for `Im z ≠ 0`.
* `freeGreensL2` — the packaged `L²` element represented by `freeGreensFunction z`.
* `coeFn_freeGreensL2` — `freeGreensL2 z hz` is a.e. equal to `freeGreensFunction z`.
-/
open MeasureTheory Set Complex Filter Asymptotics
open Spectra.Sobolev

namespace Spectra.QuantumMechanics.Hydrogen

/-- The radial dominating profile coming from the exponential decay bound, raised to the power `p`:
`(e^{−c r}/(4π r))^p`.  (Junk value `0` at `r = 0` since `1/0 = 0`.) -/
private noncomputable def greensRadial (c : ℝ) (p : ℕ) (r : ℝ) : ℝ :=
  (Real.exp (-c * r) / (4 * Real.pi * r)) ^ p

/-- The off-origin closed-form representative of `freeGreensFunction z`, defined on all of `ℝ³`
with the harmless junk value at `0` (division by `0`).  It is measurable everywhere. -/
private noncomputable def greensFormula (z : ℂ) : R3 → ℂ := fun x =>
  Complex.exp (-((-z) ^ ((1 : ℂ) / 2)) * (‖x‖ : ℂ)) / ((4 * Real.pi * ‖x‖ : ℝ) : ℂ)

/-- `freeGreensFunction z` agrees with its closed form `greensFormula z` away from the origin. -/
private lemma freeGreensFunction_eq_formula (z : ℂ) {x : R3} (hx : x ≠ 0) :
    freeGreensFunction z x = greensFormula z x := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [freeGreensFunction, if_neg hxn, greensFormula]

/-- The closed-form representative `greensFormula z` is measurable. -/
private lemma measurable_greensFormula (z : ℂ) : Measurable (greensFormula z) := by
  unfold greensFormula
  have hnorm : Measurable (fun x : R3 => (‖x‖ : ℂ)) :=
    Complex.measurable_ofReal.comp measurable_norm
  refine Measurable.div ?_ ?_
  · exact Complex.measurable_exp.comp (measurable_const.mul hnorm)
  · exact Complex.measurable_ofReal.comp
      (((measurable_const.mul measurable_norm)))

/-- `freeGreensFunction z` is a.e.-strongly measurable: it equals the measurable closed form
`greensFormula z` off the null set `{0}`. -/
theorem aestronglyMeasurable_freeGreensFunction (z : ℂ) :
    AEStronglyMeasurable (freeGreensFunction z) (volume : Measure R3) := by
  have hae : freeGreensFunction z =ᵐ[(volume : Measure R3)] greensFormula z := by
    have hne : ∀ᵐ x : R3 ∂(volume : Measure R3), x ≠ (0 : R3) := by
      rw [ae_iff]; simp
    filter_upwards [hne] with x hx using freeGreensFunction_eq_formula z hx
  exact (measurable_greensFormula z).aestronglyMeasurable.congr hae.symm

/-- The 1-D radial profile `r^{2} • greensRadial c 1 r = (1/4π) · r · e^{−c r}` is integrable
on `(0,∞)`: continuous (the `1/r` singularity cancels) and `O(e^{−c r})` at infinity. -/
private lemma integrableOn_radial_one (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => r ^ 2 • greensRadial c 1 r) (Ioi 0) := by
  -- On `(0,∞)`, `r² • greensRadial c 1 r = (1/4π) · r · e^{−c r}`.
  have hcongr : ∀ r ∈ Ioi (0 : ℝ),
      r ^ 2 • greensRadial c 1 r = (1 / (4 * Real.pi)) * (r * Real.exp (-c * r)) := by
    intro r hr
    rw [mem_Ioi] at hr
    unfold greensRadial
    rw [pow_one, smul_eq_mul]
    field_simp
  rw [integrableOn_congr_fun hcongr measurableSet_Ioi]
  -- the bare integrand `r · e^{−c r}` is integrable on `(0,∞)`; constant scales it.
  have hbase : IntegrableOn (fun r : ℝ => r * Real.exp (-c * r)) (Ioi 0) := by
    refine integrable_of_isBigO_exp_neg (b := c / 2) (by linarith) (by fun_prop) ?_
    -- `r · e^{−c r} = e^{−c r} · r^1 = O(e^{−(c/2) r})`, since `−c < −c/2`.
    have hlo : (fun t : ℝ => Real.exp (-c * t) * t ^ (1 : ℝ)) =o[atTop]
        fun t : ℝ => Real.exp (-(c / 2) * t) :=
      isLittleO_exp_mul_rpow_of_lt 1 (by linarith)
    refine hlo.isBigO.congr_left (fun r => ?_)
    rw [Real.rpow_one]; ring
  exact hbase.const_mul (1 / (4 * Real.pi))

/-- The 1-D radial profile `r^{2} • greensRadial c 2 r = (1/16π²) · e^{−2c r}` is integrable
on `(0,∞)`: continuous (the `1/r²` singularity fully cancels) and `O(e^{−2c r})` at infinity.
-/
private lemma integrableOn_radial_two (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => r ^ 2 • greensRadial c 2 r) (Ioi 0) := by
  have hcongr : ∀ r ∈ Ioi (0 : ℝ),
      r ^ 2 • greensRadial c 2 r = (1 / (4 * Real.pi) ^ 2) * Real.exp (-(2 * c) * r) := by
    intro r hr
    rw [mem_Ioi] at hr
    unfold greensRadial
    rw [smul_eq_mul, div_pow, ← Real.exp_nat_mul]
    have _hr2 : (4 * Real.pi * r) ^ 2 ≠ 0 := by positivity
    field_simp
    ring_nf
  rw [integrableOn_congr_fun hcongr measurableSet_Ioi]
  have hbase : IntegrableOn (fun r : ℝ => Real.exp (-(2 * c) * r)) (Ioi 0) :=
    integrable_of_isBigO_exp_neg (b := 2 * c) (by linarith) (by fun_prop) (isBigO_refl _ _)
  exact hbase.const_mul (1 / (4 * Real.pi) ^ 2)

/-- **M1: the free Green's function is in `L¹(ℝ³)`** for `z.im ≠ 0`. -/
theorem memL1_freeGreensFunction (z : ℂ) (hz : z.im ≠ 0) :
    MemLp (freeGreensFunction z) 1 (volume : Measure R3) := by
  obtain ⟨c, hc, hbound⟩ := freeGreensFunction_decay z hz
  rw [memLp_one_iff_integrable]
  -- the radial dominating function `greensRadial c 1 ∘ ‖·‖` is integrable …
  have hdom : Integrable (fun x : R3 => greensRadial c 1 ‖x‖) volume := by
    rw [integrable_fun_norm_addHaar]
    have hfin : Module.finrank ℝ R3 - 1 = 2 := by simp
    rw [hfin]
    exact integrableOn_radial_one c hc
  -- … and it dominates `‖G_z‖` a.e. (everywhere off the null set `{0}`).
  refine hdom.mono' (aestronglyMeasurable_freeGreensFunction z) ?_
  have hne : ∀ᵐ x : R3, x ≠ (0 : R3) := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx
  have hb := hbound x hx
  unfold greensRadial
  rwa [pow_one]

/-- **M2: the free Green's function is in `L²(ℝ³)`** for `z.im ≠ 0`. -/
theorem memL2_freeGreensFunction (z : ℂ) (hz : z.im ≠ 0) :
    MemLp (freeGreensFunction z) 2 (volume : Measure R3) := by
  obtain ⟨c, hc, hbound⟩ := freeGreensFunction_decay z hz
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_freeGreensFunction z)]
  -- the radial dominating function `greensRadial c 2 ∘ ‖·‖` is integrable …
  have hdom : Integrable (fun x : R3 => greensRadial c 2 ‖x‖) volume := by
    rw [integrable_fun_norm_addHaar]
    have hfin : Module.finrank ℝ R3 - 1 = 2 := by simp
    rw [hfin]
    exact integrableOn_radial_two c hc
  -- … and it dominates `‖G_z‖²` a.e. (everywhere off the null set `{0}`).
  refine hdom.mono' ((aestronglyMeasurable_freeGreensFunction z).norm.pow 2) ?_
  have hne : ∀ᵐ x : R3, x ≠ (0 : R3) := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx
  have hb := hbound x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold greensRadial
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

/-- The packaged `L²` element represented by the free Green's function. -/
noncomputable def freeGreensL2 (z : ℂ) (hz : z.im ≠ 0) : Lp ℂ 2 (volume : Measure R3) :=
  (memL2_freeGreensFunction z hz).toLp _

/-- The `L²` element `freeGreensL2 z hz` is a.e. equal to `freeGreensFunction z`. -/
theorem coeFn_freeGreensL2 (z : ℂ) (hz : z.im ≠ 0) :
    (freeGreensL2 z hz : R3 → ℂ) =ᵐ[volume] freeGreensFunction z :=
  MemLp.coeFn_toLp _

end Spectra.QuantumMechanics.Hydrogen

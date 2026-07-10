/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Kernel.Poisson.Lemmas          -- fourier_two_sided_exp, integrable_two_sided_exp
import Spectra.Kernel.Resolvent               -- resolvent_kernel_im, resolvent_integrand_bound
import Spectra.Fourier.Inversion              -- eq_of_fourier_decay_eq
import Spectra.Mathlib.CharFunBridge          -- measure_ext_of_fourier
import Spectra.SpectralTheory.Measure.Polarized -- char_measurable, char_norm_le_one, integrable_of_bounded
/-!
# Injectivity of the Cauchy transform on finite measures

The scalar uniqueness engine for the keystone spectral theorem:

* `measure_ext_of_poisson` : two finite measures with the same Poisson integrals
  `∫ ε/((x−t)² + ε²) dμ(x)` for all `t ∈ ℝ`, `ε > 0` are equal.
* `measure_ext_of_cauchyTransform` : two finite measures with the same Cauchy
  transform `∫ (x − z)⁻¹ dμ(x)` on the upper half-plane are equal.

## Proof architecture

Everything is a closed loop through the existing library:

  equal Cauchy transforms
    ⟹ (imaginary parts, `resolvent_kernel_im`)  equal Poisson integrals
    ⟹ (Fubini + `fourier_two_sided_exp`)        equal `e^{−ε|t|}`-damped Fourier data
    ⟹ (`eq_of_fourier_decay_eq`)                equal Fourier data
    ⟹ (`measure_ext_of_fourier`)                equal measures.

The single genuinely new computation is `damped_fourierData_eq_poisson`: the
damped Fourier transform of `t ↦ ∫ e^{iωt} dμ(ω)` *is* twice the Poisson
integral of `μ`.  One Fubini, dominated by the integrable profile `e^{−ε|t|}`.

## Downstream use (the keystone)

For uniqueness of the spectral measure: a candidate PVM satisfying the diagonal
resolvent formula has, for each `ξ`, a diagonal measure whose Cauchy transform
agrees with that of `borelMeasure U_grp ξ`; `measure_ext_of_cauchyTransform`
then forces the diagonals to agree, and `ProjValMeasure.ext_of_diag` finishes.
(To match resolvent statements phrased at `⟨t, ε⟩ : ℂ`, recall
`Complex.mk_eq_add_mul_I`.)

## Mathlib dependencies (verified against v4.31.0-rc1 by grep)

`Integrable.mul_prod`, `Integrable.mono'`, `Integrable.norm`,
`integral_integral_swap`, `continuous_of_dominated`,
`norm_integral_le_of_norm_le_const`, `integral_const_mul`,
`integral_complex_ofReal`, `Complex.norm_exp`, `Complex.imCLM`,
`ContinuousLinearMap.integral_comp_comm`, `Continuous.inv₀`.
-/

open MeasureTheory Complex Filter
open scoped Topology
open Spectra.Resolvent
open Spectra.Fourier
open Spectra.Kernels
namespace Spectra.QuantumMechanics
namespace SpectralTheory

/-! ### The Fourier data of a finite measure: continuity and bound -/

/-- The Fourier data `t ↦ ∫ e^{iωt} dμ(ω)` of a finite measure is bounded by the
total mass. -/
lemma norm_fourierData_le (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    ‖∫ ω, cexp (I * ω * t) ∂μ‖ ≤ μ.real Set.univ := by
  simpa using norm_integral_le_of_norm_le_const
    (Eventually.of_forall fun ω => char_norm_le_one t ω)

/-- The Fourier data of a finite measure is continuous (dominated convergence
with constant bound `1`). -/
lemma continuous_fourierData (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous fun t : ℝ => ∫ ω, cexp (I * ω * t) ∂μ :=
  continuous_of_dominated
    (fun t => (char_measurable t).aestronglyMeasurable)
    (fun t => Eventually.of_forall fun ω => char_norm_le_one t ω)
    (integrable_const 1)
    (Eventually.of_forall fun _ω =>
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

/-! ### The bridge: damped Fourier data is a Poisson integral -/

/-- **The bridge.**  The `e^{−ε|t|}`-damped Fourier transform of the Fourier data
of a finite measure is twice its Poisson integral:

  `∫ₜ e^{−ist} e^{−ε|t|} (∫_ω e^{iωt} dμ) dt = 2 ∫_ω ε/((ω−s)² + ε²) dμ`.

One Fubini against the integrable profile `e^{−ε|t|}`, then
`fourier_two_sided_exp` slice by slice. -/
lemma damped_fourierData_eq_poisson (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    (∫ t : ℝ, cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
        * ∫ ω, cexp (I * ω * t) ∂μ)
      = ((2 * ∫ ω, ε / ((ω - s) ^ 2 + ε ^ 2) ∂μ : ℝ) : ℂ) := by
  -- joint continuity of the three exponential factors in `(t, ω)`
  have hc1 : Continuous fun p : ℝ × ℝ => cexp (-(I * (s : ℂ) * (p.1 : ℂ))) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).neg)
  have hc2 : Continuous fun p : ℝ × ℝ => cexp (-((ε : ℂ) * ((|p.1| : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_abs.comp continuous_fst))).neg)
  have hc3 : Continuous fun p : ℝ × ℝ => cexp (I * (p.2 : ℂ) * (p.1 : ℂ)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp continuous_fst))
  -- integrability of the joint integrand: dominated by the profile `e^{−ε|t|}`
  have hInt : Integrable (Function.uncurry fun t ω : ℝ =>
      cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
        * cexp (I * (ω : ℂ) * (t : ℂ))) (volume.prod μ) := by
    have hprof : Integrable (fun t : ℝ =>
        cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ))) * cexp (I * ((-s : ℝ) : ℂ) * (t : ℂ)))
        volume := integrable_two_sided_exp hε (-s)
    have hbig : Integrable (fun p : ℝ × ℝ =>
        ‖cexp (-((ε : ℂ) * ((|p.1| : ℝ) : ℂ))) * cexp (I * ((-s : ℝ) : ℂ) * (p.1 : ℂ))‖
          * (1 : ℝ)) (volume.prod μ) :=
      hprof.norm.mul_prod (integrable_const 1)
    refine hbig.mono' ((hc1.mul hc2).mul hc3).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have e1 : (-(I * (s : ℂ) * (p.1 : ℂ))).re = 0 := by simp [Complex.mul_re]
    have e3 : (I * (p.2 : ℂ) * (p.1 : ℂ)).re = 0 := by simp [Complex.mul_re]
    have _e4 : (I * ((-s : ℝ) : ℂ) * (p.1 : ℂ)).re = 0 := by simp [Complex.mul_re]
    simp [Function.uncurry, Complex.norm_exp, e1, e3]
  calc (∫ t : ℝ, cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
          * ∫ ω, cexp (I * ω * t) ∂μ)
      = ∫ t : ℝ, ∫ ω, cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
          * cexp (I * (ω : ℂ) * (t : ℂ)) ∂μ := by
        refine integral_congr_ae (.of_forall fun t => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ ω, (∫ t : ℝ, cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
          * cexp (I * (ω : ℂ) * (t : ℂ))) ∂μ := integral_integral_swap hInt
    _ = ∫ ω, ((2 * ε / ((ω - s) ^ 2 + ε ^ 2) : ℝ) : ℂ) ∂μ := by
        refine integral_congr_ae (.of_forall fun ω => ?_)
        have hpt : ∀ t : ℝ,
            cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
                * cexp (I * (ω : ℂ) * (t : ℂ))
              = cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
                * cexp (I * ((ω - s : ℝ) : ℂ) * (t : ℂ)) := fun t => by
          have hexp : -(I * (s : ℂ) * (t : ℂ)) + I * (ω : ℂ) * (t : ℂ)
              = I * ((ω - s : ℝ) : ℂ) * (t : ℂ) := by push_cast; ring
          rw [mul_right_comm, ← Complex.exp_add, hexp, mul_comm]
        simp only [integral_congr_ae (.of_forall hpt)]
        exact fourier_two_sided_exp hε (ω - s)
    _ = ((∫ ω, 2 * ε / ((ω - s) ^ 2 + ε ^ 2) ∂μ : ℝ) : ℂ) := integral_complex_ofReal
    _ = ((2 * ∫ ω, ε / ((ω - s) ^ 2 + ε ^ 2) ∂μ : ℝ) : ℂ) := by
        have h2 : (∫ ω, 2 * ε / ((ω - s) ^ 2 + ε ^ 2) ∂μ)
            = 2 * ∫ ω, ε / ((ω - s) ^ 2 + ε ^ 2) ∂μ := by
          rw [← integral_const_mul]
          exact integral_congr_ae (.of_forall fun ω =>
            mul_div_assoc 2 ε ((ω - s) ^ 2 + ε ^ 2))
        rw [h2]

/-! ### The injectivity theorems -/

/-- **Two finite measures with the same Poisson integrals are equal.**
The Poisson data is converted into damped Fourier data by the bridge, then
`eq_of_fourier_decay_eq` recovers the Fourier data and `measure_ext_of_fourier`
finishes. -/
theorem measure_ext_of_poisson (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t ε : ℝ, 0 < ε →
      (∫ x, ε / ((x - t) ^ 2 + ε ^ 2) ∂μ) = ∫ x, ε / ((x - t) ^ 2 + ε ^ 2) ∂ν) :
    μ = ν := by
  have hfg := eq_of_fourier_decay_eq
    (f := fun t : ℝ => ∫ ω, cexp (I * ω * t) ∂μ)
    (g := fun t : ℝ => ∫ ω, cexp (I * ω * t) ∂ν)
    (continuous_fourierData μ) (continuous_fourierData ν)
    ⟨μ.real Set.univ, norm_fourierData_le μ⟩
    ⟨ν.real Set.univ, norm_fourierData_le ν⟩
    (fun ε hε s => by
      show (∫ t : ℝ, cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
              * ∫ ω, cexp (I * ω * t) ∂μ)
          = ∫ t : ℝ, cexp (-(I * (s : ℂ) * (t : ℂ))) * cexp (-((ε : ℂ) * ((|t| : ℝ) : ℂ)))
              * ∫ ω, cexp (I * ω * t) ∂ν
      rw [damped_fourierData_eq_poisson μ hε s, damped_fourierData_eq_poisson ν hε s,
        h s ε hε])
  exact measure_ext_of_fourier fun t => congrFun hfg t

/-- **Injectivity of the Cauchy transform** on finite Borel measures: agreement of
`z ↦ ∫ (x − z)⁻¹ dμ(x)` on the upper half-plane forces `μ = ν`.  Taking imaginary
parts lands in `measure_ext_of_poisson` — the boundary values deliver the measure,
as a Poisson kernel should. -/
theorem measure_ext_of_cauchyTransform (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : ℂ, 0 < z.im →
      (∫ x, ((x : ℂ) - z)⁻¹ ∂μ) = ∫ x, ((x : ℂ) - z)⁻¹ ∂ν) :
    μ = ν := by
  refine measure_ext_of_poisson μ ν fun t ε hε => ?_
  set z : ℂ := ↑t + ↑ε * I with hz_def
  have hz_im : z.im = ε := by simp [hz_def]
  have hz_pos : 0 < z.im := by rw [hz_im]; exact hε
  have hz_ne : z.im ≠ 0 := hz_pos.ne'
  have hker_cont : Continuous fun x : ℝ => ((x : ℂ) - z)⁻¹ :=
    (Complex.continuous_ofReal.sub continuous_const).inv₀ fun x =>
      sub_ne_zero.mpr fun hx => hz_ne (by rw [← hx]; exact Complex.ofReal_im x)
  have hint_μ : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ :=
    integrable_of_bounded hker_cont.measurable (resolvent_integrand_bound z hz_ne)
  have hint_ν : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) ν :=
    integrable_of_bounded hker_cont.measurable (resolvent_integrand_bound z hz_ne)
  calc (∫ x, ε / ((x - t) ^ 2 + ε ^ 2) ∂μ)
      = ∫ x, (((x : ℂ) - z)⁻¹).im ∂μ := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        rw [hz_def]
        exact (resolvent_kernel_im x t ε hε).symm
    _ = (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im := by
        simpa only [Complex.imCLM_apply] using Complex.imCLM.integral_comp_comm hint_μ
    _ = (∫ x, ((x : ℂ) - z)⁻¹ ∂ν).im := by rw [h z hz_pos]
    _ = ∫ x, (((x : ℂ) - z)⁻¹).im ∂ν := by
        simpa only [Complex.imCLM_apply] using
          (Complex.imCLM.integral_comp_comm hint_ν).symm
    _ = ∫ x, ε / ((x - t) ^ 2 + ε ^ 2) ∂ν := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        rw [hz_def]
        exact resolvent_kernel_im x t ε hε


end Spectra.QuantumMechanics.SpectralTheory

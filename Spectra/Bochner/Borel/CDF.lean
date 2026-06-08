/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: QuantumMechanics/SpectralTheory/ScalarMeasure/Borel/CDF.lean
-/
import Spectra.Bochner.Borel.Density

open Complex MeasureTheory Filter Topology
open Spectra.Resolvent
open Spectra.Fourier
open Spectra.Kernels
open Spectra.QuantumMechanics
open OneParameterUnitaryGroup
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

namespace Spectra.Bochner

/-- The cumulative distribution function of the spectral density `borelDensity ε`. -/
noncomputable def borelCDF (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ℝ :=
  ∫ lambda in Set.Iic x, borelDensity U_grp ξ hε lambda

/-- `borelCDF ε` is monotone. -/
lemma borelCDF_mono (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) : Monotone (borelCDF U_grp ξ hε) := by
  have hD_int : Integrable (borelDensity U_grp ξ hε) volume := (borelDensity_mass U_grp ξ hε).1
  intro x y hxy
  exact MeasureTheory.setIntegral_mono_set hD_int.integrableOn
    (Filter.Eventually.of_forall (borelDensity_nonneg U_grp ξ hε))
    ((Set.Iic_subset_Iic.mpr hxy).eventuallyLE)

/-- `borelCDF ε` is nonnegative. -/
lemma borelCDF_nonneg (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ borelCDF U_grp ξ hε x := by
  unfold borelCDF
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic
    (fun lambda _ => borelDensity_nonneg U_grp ξ hε lambda)

/-- `borelCDF ε` is bounded above by the total mass `‖ξ‖²`. -/
lemma borelCDF_le (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : borelCDF U_grp ξ hε x ≤ ‖ξ‖ ^ 2 := by
  have hD := borelDensity_mass U_grp ξ hε
  unfold borelCDF
  rw [← hD.2]
  exact setIntegral_le_integral hD.1
    (Filter.Eventually.of_forall (borelDensity_nonneg U_grp ξ hε))

/-- The left tail of `borelCDF ε` vanishes. -/
lemma borelCDF_tendsto_atBot (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) : Tendsto (borelCDF U_grp ξ hε) atBot (𝓝 0) := by
  have hD_int : Integrable (borelDensity U_grp ξ hε) volume := (borelDensity_mass U_grp ξ hε).1
  have hrw : ∀ a : ℝ, borelCDF U_grp ξ hε a
      = ∫ x : ℝ, (Set.Iic a).indicator (borelDensity U_grp ξ hε) x := by
    intro a; unfold borelCDF; rw [MeasureTheory.integral_indicator measurableSet_Iic]
  have hmain : Tendsto (fun a : ℝ => ∫ x : ℝ, (Set.Iic a).indicator (borelDensity U_grp ξ hε) x)
      atBot (𝓝 0) := by
    have key : Tendsto (fun a : ℝ => ∫ x : ℝ, (Set.Iic a).indicator (borelDensity U_grp ξ hε) x)
        atBot (𝓝 (∫ _x : ℝ, (0 : ℝ))) := by
      apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (bound := borelDensity U_grp ξ hε)
      · exact Filter.Eventually.of_forall (fun a =>
          hD_int.aestronglyMeasurable.indicator measurableSet_Iic)
      · refine Filter.Eventually.of_forall (fun a => ?_)
        filter_upwards with x
        rw [Real.norm_eq_abs, Set.indicator_apply]
        split_ifs with h
        · exact (abs_of_nonneg (borelDensity_nonneg U_grp ξ hε x)).le
        · simpa using borelDensity_nonneg U_grp ξ hε x
      · exact hD_int
      · refine Filter.Eventually.of_forall (fun x => ?_)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_lt_atBot x] with a ha
        show (0 : ℝ) = (Set.Iic a).indicator (borelDensity U_grp ξ hε) x
        have hx : x ∉ Set.Iic a := by simp only [Set.mem_Iic, not_le]; exact ha
        exact Eq.symm (Set.indicator_of_notMem hx (borelDensity U_grp ξ hε))
    simpa using key
  exact hmain.congr (fun a => (hrw a).symm)

/-- `borelCDF ε` is continuous: its density is continuous and integrable, so the CDF
of the absolutely continuous measure `borelDensity ε · dλ` is continuous. -/
lemma borelCDF_continuous (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) : Continuous (borelCDF U_grp ξ hε) := by
  have hD_int : Integrable (borelDensity U_grp ξ hε) volume := (borelDensity_mass U_grp ξ hε).1
  have hrw : ∀ a : ℝ, borelCDF U_grp ξ hε a
      = ∫ t : ℝ, (Set.Iic a).indicator (borelDensity U_grp ξ hε) t := by
    intro a; unfold borelCDF; rw [MeasureTheory.integral_indicator measurableSet_Iic]
  rw [continuous_iff_continuousAt]
  intro x₀
  have hCA : Tendsto (fun x : ℝ => ∫ t : ℝ, (Set.Iic x).indicator (borelDensity U_grp ξ hε) t)
      (𝓝 x₀) (𝓝 (∫ t : ℝ, (Set.Iic x₀).indicator (borelDensity U_grp ξ hε) t)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := borelDensity U_grp ξ hε)
    · exact Filter.Eventually.of_forall (fun x =>
        hD_int.aestronglyMeasurable.indicator measurableSet_Iic)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      filter_upwards with t
      rw [Real.norm_eq_abs, Set.indicator_apply]
      split_ifs with h
      · exact (abs_of_nonneg (borelDensity_nonneg U_grp ξ hε t)).le
      · simpa using borelDensity_nonneg U_grp ξ hε t
    · exact hD_int
    · have hae : ∀ᵐ t : ℝ, t ≠ x₀ := by
        have hset : {t : ℝ | ¬ t ≠ x₀} = {x₀} := by ext t; simp
        rw [MeasureTheory.ae_iff, hset]; simp
      filter_upwards [hae] with t ht
      rcases lt_or_gt_of_ne ht with h | h
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr h.le)]
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_nhds h] with x hx
        show borelDensity U_grp ξ hε t = (Set.Iic x).indicator (borelDensity U_grp ξ hε) t
        rw [Set.indicator_of_mem (Set.mem_Iic.mpr (Set.mem_Ioi.mp hx).le)]
      · rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic, not_le]; exact h)]
        apply tendsto_const_nhds.congr'
        filter_upwards [Iio_mem_nhds h] with x hx
        show (0 : ℝ) = (Set.Iic x).indicator (borelDensity U_grp ξ hε) t
        rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic, not_le]; exact Set.mem_Iio.mp hx)]
  show Tendsto (borelCDF U_grp ξ hε) (𝓝 x₀) (𝓝 (borelCDF U_grp ξ hε x₀))
  rw [hrw x₀]
  exact hCA.congr (fun x => (hrw x).symm)

namespace Spectra.Bochner

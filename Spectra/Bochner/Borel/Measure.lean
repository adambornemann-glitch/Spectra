/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/BochnerTheorem/Borel/Measure.lean
-/
import Spectra.Herglotz.Stieltjes.Measure
import Spectra.Bochner.Borel.Hellys

open Complex MeasureTheory Filter Topology
open Spectra.Resolvent
open Spectra.Fourier
open Spectra.Kernels
open Spectra.Herglotz
open Spectra.QuantumMechanics
open OneParameterUnitaryGroup
open scoped InnerProductSpace ENNReal ComplexConjugate
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

namespace Spectra.Bochner

/-- **The spectral (Borel) measure.** -/
noncomputable def borelMeasure (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) : Measure ℝ :=
  hellyLimitMeasure (borelLimitCDF U_grp ξ) (borelLimitCDF_mono U_grp ξ)

/-- The Borel–Stieltjes measure has total mass at most `‖ξ‖²` (ENNReal form). -/
lemma borelMeasure_univ_le
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) :
    borelMeasure U_grp ξ Set.univ ≤ ENNReal.ofReal (‖ξ‖ ^ 2) := by
  have hbnd : ∀ x, borelLimitCDF U_grp ξ x ∈ Set.Icc (0 : ℝ) (‖ξ‖ ^ 2) :=
    (borelHelly U_grp ξ).choose_spec.choose_spec.2.2.1
  have htend : ∀ x, Tendsto (borelLimitCDF U_grp ξ) (𝓝[>] x)
      (𝓝 (Function.rightLim (borelLimitCDF U_grp ξ) x)) :=
    fun x => (borelLimitCDF_mono U_grp ξ).tendsto_rightLim x
  have hsf_le : ∀ x, (borelLimitCDF_mono U_grp ξ).stieltjesFunction x ≤ ‖ξ‖ ^ 2 := by
    intro x
    rw [show (borelLimitCDF_mono U_grp ξ).stieltjesFunction x
          = Function.rightLim (borelLimitCDF U_grp ξ) x from rfl]
    exact le_of_tendsto (htend x) (Filter.Eventually.of_forall fun y => (hbnd y).2)
  have hsf_nonneg : ∀ x, 0 ≤ (borelLimitCDF_mono U_grp ξ).stieltjesFunction x := by
    intro x
    rw [show (borelLimitCDF_mono U_grp ξ).stieltjesFunction x
          = Function.rightLim (borelLimitCDF U_grp ξ) x from rfl]
    exact ge_of_tendsto (htend x) (Filter.Eventually.of_forall fun y => (hbnd y).1)
  have hmono_sets : Monotone fun n : ℕ => Set.Ioc (-(n : ℝ)) (n : ℝ) := fun m n hmn =>
    Set.Ioc_subset_Ioc (neg_le_neg (by exact_mod_cast hmn)) (by exact_mod_cast hmn)
  have hcover : ⋃ n : ℕ, Set.Ioc (-(n : ℝ)) (n : ℝ) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    rw [abs_lt] at hn
    exact Set.mem_iUnion.mpr ⟨n, hn.1, hn.2.le⟩
  have hbound : ∀ n : ℕ,
      borelMeasure U_grp ξ (Set.Ioc (-(n : ℝ)) (n : ℝ)) ≤ ENNReal.ofReal (‖ξ‖ ^ 2) := by
    intro n
    unfold borelMeasure
    rw [hellyLimitMeasure_Ioc]
    exact ENNReal.ofReal_le_ofReal (by linarith [hsf_le (n : ℝ), hsf_nonneg (-(n : ℝ))])
  calc borelMeasure U_grp ξ Set.univ
      = borelMeasure U_grp ξ (⋃ n : ℕ, Set.Ioc (-(n : ℝ)) (n : ℝ)) := by rw [hcover]
    _ = ⨆ n : ℕ, borelMeasure U_grp ξ (Set.Ioc (-(n : ℝ)) (n : ℝ)) := hmono_sets.measure_iUnion
    _ ≤ ENNReal.ofReal (‖ξ‖ ^ 2) := iSup_le hbound

/-- The Borel–Stieltjes measure has total mass at most `‖ξ‖²` (real form). -/
lemma borelMeasure_real_univ_le
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) :
    (borelMeasure U_grp ξ Set.univ).toReal ≤ ‖ξ‖ ^ 2 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (borelMeasure_univ_le U_grp ξ)
  rwa [ENNReal.toReal_ofReal (sq_nonneg _)] at h

/-- The Borel–Stieltjes measure is finite (mass at most `‖ξ‖²`). -/
instance borelMeasure_isFiniteMeasure
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) :
    IsFiniteMeasure (borelMeasure U_grp ξ) :=
  ⟨lt_of_le_of_lt (borelMeasure_univ_le U_grp ξ) ENNReal.ofReal_lt_top⟩

end Spectra.Bochner

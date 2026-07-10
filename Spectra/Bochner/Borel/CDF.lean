/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.Borel.Density
import Spectra.Herglotz.Stieltjes.Hellys
/-!
# The Spectral (Borel–Stieltjes) Measure

This file assembles the spectral measure `borelMeasure U_grp ξ` of a one-parameter unitary
group `U_grp` at a vector `ξ`, via the classical pipeline: regularized Poisson density
(`borelDensity`, from `Bochner/Borel/Density.lean`) → cumulative distribution function
(`borelCDF`) → Helly selection along `εₙ = 1/(n+1)` (`borelHelly`, `borelLimitCDF`) →
Stieltjes measure of the limiting CDF (`borelMeasure`).

## Main definitions

* `borelCDF`: the CDF of the regularized density `borelDensity ε`
* `borelApproxCDF`: `borelCDF` along the regularization schedule `εₙ = 1/(n+1)`
* `borelLimitCDF`: the CDF obtained from `borelApproxCDF` by Helly selection
* `borelMeasure`: the Stieltjes measure of `borelLimitCDF` — **the spectral measure**

## Main statements

* `borelCDF_mono`, `borelCDF_nonneg`, `borelCDF_le_normSq`: basic CDF bounds
* `borelCDF_tendsto_atBot`, `borelCDF_continuous`: the regularity needed for Helly selection
* `borelHelly`: existence of a monotone, `[0,‖ξ‖²]`-valued limit `G` and subsequence `φ` with
  the convergence properties Helly's theorem provides
* `borelLimitCDF_mono`, `borelLimitCDF_bnd`, `borelLimitCDF_tendsto_rat`,
  `borelLimitCDF_tendsto_continuousAt`: named accessors for `borelHelly`'s existential witness,
  so consumers don't reach into raw `.choose_spec` projections
* `borelMeasure_univ_le`, `borelMeasure_real_univ_le`, `borelMeasure_isFiniteMeasure`: the
  spectral measure has total mass at most `‖ξ‖²`

## References

* Helly's selection theorem, e.g. Billingsley, *Convergence of Probability Measures*, Thm 25.9
-/
open Complex MeasureTheory Filter Topology
open Spectra.Resolvent
open Spectra.Herglotz
open Spectra.Fourier
open Spectra.Kernels
open Spectra.OneParameterUnitaryGroup
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Borel
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The cumulative distribution function of the spectral density `borelDensity ε`. -/
noncomputable def borelCDF (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ℝ :=
  ∫ lambda in Set.Iic x, borelDensity U_grp ξ hε lambda

/-- `borelCDF ε` is monotone. -/
lemma borelCDF_mono (ξ : H)
    {ε : ℝ} (hε : 0 < ε) : Monotone (borelCDF U_grp ξ hε) := by
  have hD_int : Integrable (borelDensity U_grp ξ hε) volume := (borelDensity_mass U_grp ξ hε).1
  intro x y hxy
  exact MeasureTheory.setIntegral_mono_set hD_int.integrableOn
    (Filter.Eventually.of_forall (borelDensity_nonneg U_grp ξ hε))
    ((Set.Iic_subset_Iic.mpr hxy).eventuallyLE)

/-- `borelCDF ε` is nonnegative. -/
lemma borelCDF_nonneg (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ borelCDF U_grp ξ hε x := by
  unfold borelCDF
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic
    (fun lambda _ => borelDensity_nonneg U_grp ξ hε lambda)

/-- `borelCDF ε` is bounded above by the total mass `‖ξ‖²`. -/
lemma borelCDF_le_normSq (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) : borelCDF U_grp ξ hε x ≤ ‖ξ‖ ^ 2 := by
  have hD := borelDensity_mass U_grp ξ hε
  unfold borelCDF
  rw [← hD.2]
  exact setIntegral_le_integral hD.1
    (Filter.Eventually.of_forall (borelDensity_nonneg U_grp ξ hε))

/-- `borelCDF ε a` unfolds to an integral of the indicator of `borelDensity ε` — the shared
first step of both `borelCDF_tendsto_atBot` and `borelCDF_continuous`. -/
private lemma borelCDF_eq_integral_indicator (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    borelCDF U_grp ξ hε a = ∫ x : ℝ, (Set.Iic a).indicator (borelDensity U_grp ξ hε) x := by
  unfold borelCDF; rw [MeasureTheory.integral_indicator measurableSet_Iic]

/-- The indicator of `borelDensity ε` on any `Set.Iic a` is a.e.-strongly measurable — the
measurability hypothesis shared by both `borelCDF_tendsto_atBot` and `borelCDF_continuous`'s
dominated-convergence arguments. -/
private lemma borelDensity_indicator_aestronglyMeasurable
    (ξ : H) {ε : ℝ} {hε : 0 < ε}
    (hD_int : Integrable (borelDensity U_grp ξ hε) volume) (a : ℝ) :
    AEStronglyMeasurable ((Set.Iic a).indicator (borelDensity U_grp ξ hε)) volume :=
  hD_int.aestronglyMeasurable.indicator measurableSet_Iic

/-- The indicator of `borelDensity ε` on any `Set.Iic a` is dominated in norm by `borelDensity
ε` itself — the domination hypothesis shared by both `borelCDF_tendsto_atBot` and
`borelCDF_continuous`'s dominated-convergence arguments. -/
private lemma borelDensity_indicator_norm_le (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (a x : ℝ) :
    ‖(Set.Iic a).indicator (borelDensity U_grp ξ hε) x‖ ≤ borelDensity U_grp ξ hε x := by
  rw [Real.norm_eq_abs, Set.indicator_apply]
  split_ifs with h
  · exact (abs_of_nonneg (borelDensity_nonneg U_grp ξ hε x)).le
  · simpa using borelDensity_nonneg U_grp ξ hε x

/-- The left tail of `borelCDF ε` vanishes. -/
lemma borelCDF_tendsto_atBot (ξ : H)
    {ε : ℝ} (hε : 0 < ε) : Tendsto (borelCDF U_grp ξ hε) atBot (𝓝 0) := by
  have hD_int : Integrable (borelDensity U_grp ξ hε) volume := (borelDensity_mass U_grp ξ hε).1
  have hrw := borelCDF_eq_integral_indicator U_grp ξ hε
  have hmain : Tendsto (fun a : ℝ => ∫ x : ℝ, (Set.Iic a).indicator (borelDensity U_grp ξ hε) x)
      atBot (𝓝 0) := by
    have key : Tendsto (fun a : ℝ => ∫ x : ℝ, (Set.Iic a).indicator (borelDensity U_grp ξ hε) x)
        atBot (𝓝 (∫ _x : ℝ, (0 : ℝ))) := by
      apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (bound := borelDensity U_grp ξ hε)
      · exact Filter.Eventually.of_forall
          (borelDensity_indicator_aestronglyMeasurable U_grp ξ hD_int)
      · exact Filter.Eventually.of_forall (fun a =>
          Filter.Eventually.of_forall (borelDensity_indicator_norm_le U_grp ξ hε a))
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
lemma borelCDF_continuous (ξ : H)
    {ε : ℝ} (hε : 0 < ε) : Continuous (borelCDF U_grp ξ hε) := by
  have hD_int : Integrable (borelDensity U_grp ξ hε) volume := (borelDensity_mass U_grp ξ hε).1
  have hrw := borelCDF_eq_integral_indicator U_grp ξ hε
  rw [continuous_iff_continuousAt]
  intro x₀
  have hCA : Tendsto (fun x : ℝ => ∫ t : ℝ, (Set.Iic x).indicator (borelDensity U_grp ξ hε) t)
      (𝓝 x₀) (𝓝 (∫ t : ℝ, (Set.Iic x₀).indicator (borelDensity U_grp ξ hε) t)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := borelDensity U_grp ξ hε)
    · exact Filter.Eventually.of_forall
        (borelDensity_indicator_aestronglyMeasurable U_grp ξ hD_int)
    · exact Filter.Eventually.of_forall (fun x =>
        Filter.Eventually.of_forall (borelDensity_indicator_norm_le U_grp ξ hε x))
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
  change Tendsto (borelCDF U_grp ξ hε) (𝓝 x₀) (𝓝 (borelCDF U_grp ξ hε x₀))
  rw [hrw x₀]
  exact hCA.congr (fun x => (hrw x).symm)

/-- `1/(n+1) > 0`, the regularization schedule used to build `borelApproxCDF`. -/
lemma borelEps_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

/-- Regularized CDFs along εₙ = 1/(n+1), packaged for Helly. -/
noncomputable def borelApproxCDF (ξ : H) : ℕ → ℝ → ℝ :=
  fun n => borelCDF U_grp ξ (borelEps_pos n)

/-- `borelApproxCDF ξ n` is monotone, for every `n`. -/
lemma borelApproxCDF_mono (ξ : H) (n : ℕ) : Monotone (borelApproxCDF U_grp ξ n) :=
  borelCDF_mono U_grp ξ (borelEps_pos n)

/-- `borelApproxCDF ξ n x` lies in `[0, ‖ξ‖²]`, for every `n` and `x`. -/
lemma borelApproxCDF_bnd (ξ : H)
    (n : ℕ) (x : ℝ) : borelApproxCDF U_grp ξ n x ∈ Set.Icc (0 : ℝ) (‖ξ‖ ^ 2) :=
  ⟨borelCDF_nonneg U_grp ξ (borelEps_pos n) x, borelCDF_le_normSq U_grp ξ (borelEps_pos n) x⟩

/-- The Helly existence, named once so the chosen `G`/`φ` are shared everywhere below. -/
lemma borelHelly (ξ : H) :
    ∃ (G : ℝ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Monotone G ∧
      (∀ x, G x ∈ Set.Icc (0 : ℝ) (‖ξ‖ ^ 2)) ∧
      (∀ q : ℚ, Tendsto (fun k => borelApproxCDF U_grp ξ (φ k) (q : ℝ)) atTop (𝓝 (G (q : ℝ)))) ∧
      (∀ x : ℝ, ContinuousAt G x →
        Tendsto (fun k => borelApproxCDF U_grp ξ (φ k) x) atTop (𝓝 (G x))) :=
  helly_selection (borelApproxCDF U_grp ξ) (‖ξ‖ ^ 2) (by positivity)
    (borelApproxCDF_mono U_grp ξ) (borelApproxCDF_bnd U_grp ξ)

/-- The limiting CDF (along the selected subsequence). -/
noncomputable def borelLimitCDF (ξ : H) : ℝ → ℝ :=
  (borelHelly U_grp ξ).choose

/-- `borelLimitCDF` is monotone. -/
lemma borelLimitCDF_mono (ξ : H) :
    Monotone (borelLimitCDF U_grp ξ) :=
  (borelHelly U_grp ξ).choose_spec.choose_spec.2.1

/-- `borelLimitCDF ξ x` lies in `[0, ‖ξ‖²]`, for every `x`. Named so consumers don't reach into
`borelHelly`'s raw `.choose_spec` projections, which would silently break if the conjunction in
`borelHelly`'s statement is ever reordered. -/
lemma borelLimitCDF_bnd (ξ : H) (x : ℝ) :
    borelLimitCDF U_grp ξ x ∈ Set.Icc (0 : ℝ) (‖ξ‖ ^ 2) :=
  (borelHelly U_grp ξ).choose_spec.choose_spec.2.2.1 x

/-- The regularized CDFs converge to `borelLimitCDF` at every rational point, along the
selected subsequence `φ` from `borelHelly`. -/
lemma borelLimitCDF_tendsto_rat (ξ : H) (q : ℚ) :
    Tendsto (fun k => borelApproxCDF U_grp ξ ((borelHelly U_grp ξ).choose_spec.choose k) (q : ℝ))
      atTop (𝓝 (borelLimitCDF U_grp ξ (q : ℝ))) :=
  (borelHelly U_grp ξ).choose_spec.choose_spec.2.2.2.1 q

/-- The regularized CDFs converge to `borelLimitCDF` at every continuity point of the limit,
along the selected subsequence `φ` from `borelHelly`. -/
lemma borelLimitCDF_tendsto_continuousAt (ξ : H)
    (x : ℝ) (hx : ContinuousAt (borelLimitCDF U_grp ξ) x) :
    Tendsto (fun k => borelApproxCDF U_grp ξ ((borelHelly U_grp ξ).choose_spec.choose k) x)
      atTop (𝓝 (borelLimitCDF U_grp ξ x)) :=
  (borelHelly U_grp ξ).choose_spec.choose_spec.2.2.2.2 x hx

/-- **The spectral (Borel) measure.** -/
noncomputable def borelMeasure (ξ : H) : Measure ℝ :=
  hellyLimitMeasure (borelLimitCDF U_grp ξ) (borelLimitCDF_mono U_grp ξ)

/-- The Borel–Stieltjes measure has total mass at most `‖ξ‖²` (ENNReal form). -/
lemma borelMeasure_univ_le (ξ : H) :
    borelMeasure U_grp ξ Set.univ ≤ ENNReal.ofReal (‖ξ‖ ^ 2) := by
  have hbnd : ∀ x, borelLimitCDF U_grp ξ x ∈ Set.Icc (0 : ℝ) (‖ξ‖ ^ 2) :=
    borelLimitCDF_bnd U_grp ξ
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
lemma borelMeasure_real_univ_le (ξ : H) :
    (borelMeasure U_grp ξ Set.univ).toReal ≤ ‖ξ‖ ^ 2 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (borelMeasure_univ_le U_grp ξ)
  rwa [ENNReal.toReal_ofReal (sq_nonneg _)] at h

/-- The Borel–Stieltjes measure is finite (mass at most `‖ξ‖²`). -/
instance borelMeasure_isFiniteMeasure (ξ : H) :
    IsFiniteMeasure (borelMeasure U_grp ξ) :=
  ⟨lt_of_le_of_lt (borelMeasure_univ_le U_grp ξ) ENNReal.ofReal_lt_top⟩

end Spectra.Borel

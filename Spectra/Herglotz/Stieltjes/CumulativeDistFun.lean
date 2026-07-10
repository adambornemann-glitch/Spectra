/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.PositiveDefinite.Unitary
import Spectra.Herglotz.FejerMeasure

/-!
# Cumulative distribution function of the Fejér measure

## Main definitions

* `fejerCDF`: the cumulative distribution function `F_N(x) = σ_N([0, x])` of the `N`-th Fejér
  mean measure `σ_N` (`Herglotz/FejerMeasure.lean`), clamped flat outside `[0, 2π]`.

## Main results

* `fejerCDF_zero`, `fejerCDF_two_pi`: the clamp values `F_N(0) = 0` and `F_N(2π) = ‖ψ‖²`.
* `fejerCDF_monotone`: `F_N` is monotone non-decreasing.
* `fejerCDF_bounded`: `0 ≤ F_N(x) ≤ ‖ψ‖²` for all `x`.
* `fejerCDF_continuous`: `F_N` is continuous.
* `fejerCDF_eq_measure`: the CDF-difference-equals-measure identity
  `F_N(b) − F_N(a) = σ_N((a, b])` for `0 ≤ a ≤ b ≤ 2π`.

## Implementation notes

`fejerCDF` itself takes no unitarity hypothesis — it doesn't need one to be well-defined — and
`hU : Operator.Unitary U` is added only on the lemmas whose proof actually uses positivity of the
Fejér density (`fejerCDF_monotone`, `fejerCDF_bounded`, `fejerCDF_eq_measure`); `fejerCDF_zero`,
`fejerCDF_two_pi`, and `fejerCDF_continuous` hold unconditionally.

All six results are currently unused elsewhere in the library: this file stages the CDF package
for the Helly-selection argument in `Stieltjes/Hellys.lean` (which imports it), but the actual
wiring — applying `helly_selection` to `fejerCDF U ψ N` to extract a convergent CDF subsequence —
has not been written yet.

Three internal facts recur across several proofs and are factored into private lemmas below to
avoid restating them: `fejerCDF_hR_two_pi` (`(1/2π) ∫₀^{2π} re(F_N) = ‖ψ‖²`, mirroring
`fejerMeasure_total` in `FejerMeasure.lean`) and `fejerCDF_hGset` (interval integral = set integral
for the primitive on `[0, x]`).
-/
open MeasureTheory
open Spectra.PositiveDefinite
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Herglotz

variable (U : H →L[ℂ] H)

/-- The **cumulative distribution function** of the `N`-th Fejér mean:
`F_N(x) = σ_N([0, x])` for `x ∈ [0, 2π]`, extended flat outside.

Concretely, `F_N(x) = (1/2π) ∫₀ˣ re(FejerDensity_N(θ)) dθ` for `x ∈ [0, 2π]`.

We define it on all of `ℝ` by clamping:
  - `F_N(x) = 0` for `x ≤ 0`
  - `F_N(x) = ‖ψ‖²` for `x ≥ 2π` -/
noncomputable def fejerCDF (ψ : H) (N : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0
  else if x ≥ 2 * Real.pi then ‖ψ‖ ^ 2
  else (1 / (2 * Real.pi)) *
    ∫ θ in Set.Icc 0 x, (fejerMeanDensity U ψ N θ).re

/-- `F_N(0) = 0`. -/
lemma fejerCDF_zero (ψ : H) (N : ℕ) : fejerCDF U ψ N 0 = 0 := by
  simp [fejerCDF]

/-- `F_N(2π) = ‖ψ‖²`. -/
lemma fejerCDF_two_pi (ψ : H) (N : ℕ) :
    fejerCDF U ψ N (2 * Real.pi) = ‖ψ‖ ^ 2 := by
  have h0 : ¬ (2 * Real.pi ≤ 0) := not_le.mpr (by positivity)
  unfold fejerCDF
  rw [if_neg h0, if_pos (le_refl (2 * Real.pi))]

/-- `(1/2π) ∫₀^{2π} re(F_N) = ‖ψ‖²`, unconditionally (mirrors `fejerMeasure_total`). Shared by
`fejerCDF_monotone`, `fejerCDF_continuous`, and `fejerCDF_eq_measure`. -/
private lemma fejerCDF_hR_two_pi (ψ : H) (N : ℕ) :
    (1 / (2 * Real.pi)) * (∫ θ in Set.Icc (0:ℝ) (2 * Real.pi),
      (fejerMeanDensity U ψ N θ).re) = ‖ψ‖ ^ 2 := by
  have hF_int : IntegrableOn (fejerMeanDensity U ψ N)
      (Set.Icc (0:ℝ) (2 * Real.pi)) volume :=
    (fejerMeanDensity_continuous U ψ N).continuousOn.integrableOn_compact isCompact_Icc
  have hint : (∫ θ in Set.Icc (0:ℝ) (2 * Real.pi), (fejerMeanDensity U ψ N θ).re)
      = 2 * Real.pi * ‖ψ‖ ^ 2 := by
    rw [show (fun θ => (fejerMeanDensity U ψ N θ).re)
          = (fun θ => Complex.reCLM (fejerMeanDensity U ψ N θ)) from rfl]
    rw [show (∫ θ in Set.Icc (0:ℝ) (2 * Real.pi), Complex.reCLM (fejerMeanDensity U ψ N θ))
          = Complex.reCLM (∫ θ in Set.Icc (0:ℝ) (2 * Real.pi), fejerMeanDensity U ψ N θ)
        from ContinuousLinearMap.integral_comp_comm _ hF_int]
    rw [fejerMeanDensity_integral U ψ N, unitaryCorrelation_zero, Complex.reCLM_apply,
        show ((2:ℂ) * (Real.pi:ℂ) * ((‖ψ‖ ^ 2 : ℝ):ℂ))
            = (((2 * Real.pi * ‖ψ‖ ^ 2 : ℝ)):ℂ) from by push_cast; ring,
        Complex.ofReal_re]
  rw [hint, one_div, inv_mul_cancel_left₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]

/-- Interval integral equals set integral for the Fejér-density primitive on `[0, x]`.
Shared by `fejerCDF_continuous` and `fejerCDF_eq_measure`. -/
private lemma fejerCDF_hGset (ψ : H) (N : ℕ) : ∀ x : ℝ, 0 ≤ x →
    (∫ t in (0:ℝ)..x, (fejerMeanDensity U ψ N t).re)
      = ∫ θ in Set.Icc 0 x, (fejerMeanDensity U ψ N θ).re := by
  intro x hx
  rw [intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc]

/-- `F_N` is monotone non-decreasing. -/
lemma fejerCDF_monotone (hU : Operator.Unitary U) (ψ : H) (N : ℕ) :
    Monotone (fejerCDF U ψ N) := by
  -- region evaluators (RHS written to match the def body exactly, so `rw` closes by rfl)
  have eval_le0 : ∀ x, x ≤ 0 → fejerCDF U ψ N x = 0 := by
    intro x hx; unfold fejerCDF; rw [if_pos hx]
  have eval_ge : ∀ x, ¬ x ≤ 0 → 2 * Real.pi ≤ x → fejerCDF U ψ N x = ‖ψ‖ ^ 2 := by
    intro x h0 h2; unfold fejerCDF; rw [if_neg h0, if_pos h2]
  have eval_mid : ∀ x, ¬ x ≤ 0 → ¬ (2 * Real.pi ≤ x) →
      fejerCDF U ψ N x
        = (1 / (2 * Real.pi)) * ∫ θ in Set.Icc 0 x, (fejerMeanDensity U ψ N θ).re := by
    intro x h0 h2; unfold fejerCDF; rw [if_neg h0, if_neg h2]
  -- integrand facts
  have hint_nn : ∀ x : ℝ, 0 ≤ ∫ θ in Set.Icc (0:ℝ) x, (fejerMeanDensity U ψ N θ).re :=
    fun x => setIntegral_nonneg measurableSet_Icc
      (fun θ _ => fejerMeanDensity_nonneg U hU ψ N θ)
  have hmono_int : ∀ {x y : ℝ}, x ≤ y →
      (∫ θ in Set.Icc (0:ℝ) x, (fejerMeanDensity U ψ N θ).re)
        ≤ ∫ θ in Set.Icc (0:ℝ) y, (fejerMeanDensity U ψ N θ).re := by
    intro x y hxy
    have hintOn : IntegrableOn (fun θ => (fejerMeanDensity U ψ N θ).re)
        (Set.Icc (0:ℝ) y) volume :=
      (Complex.continuous_re.comp
        (fejerMeanDensity_continuous U ψ N)).continuousOn.integrableOn_compact isCompact_Icc
    exact setIntegral_mono_set hintOn
      (ae_of_all _ (fun θ => fejerMeanDensity_nonneg U hU ψ N θ))
      (HasSubset.Subset.eventuallyLE (Set.Icc_subset_Icc_right hxy))
  have hR_two_pi := fejerCDF_hR_two_pi U ψ N
  -- F_N ≥ 0 everywhere
  have hF_nonneg : ∀ x : ℝ, 0 ≤ fejerCDF U ψ N x := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · exact (eval_le0 x hx).ge
    · rcases le_or_gt (2 * Real.pi) x with hx2 | hx2
      · rw [eval_ge x (not_le.mpr hx) hx2]; exact sq_nonneg _
      · rw [eval_mid x (not_le.mpr hx) (not_le.mpr hx2)]
        exact mul_nonneg (by positivity) (hint_nn x)
  -- main argument: region analysis on a, then on b
  intro a b hab
  rcases le_or_gt a 0 with ha0 | ha0
  · rw [eval_le0 a ha0]; exact hF_nonneg b
  · rcases le_or_gt (2 * Real.pi) a with ha2 | ha2
    · have hbpos : 0 < b := by linarith [Real.pi_pos]
      rw [eval_ge a (not_le.mpr ha0) ha2,
          eval_ge b (not_le.mpr hbpos) (le_trans ha2 hab)]
    · rw [eval_mid a (not_le.mpr ha0) (not_le.mpr ha2)]
      rcases le_or_gt (2 * Real.pi) b with hb2 | hb2
      · have hbpos : 0 < b := by linarith
        rw [eval_ge b (not_le.mpr hbpos) hb2]
        calc (1 / (2 * Real.pi)) * (∫ θ in Set.Icc (0:ℝ) a, (fejerMeanDensity U ψ N θ).re)
            ≤ (1 / (2 * Real.pi))
                * (∫ θ in Set.Icc (0:ℝ) (2 * Real.pi), (fejerMeanDensity U ψ N θ).re) :=
              mul_le_mul_of_nonneg_left (hmono_int (le_of_lt ha2)) (by positivity)
          _ = ‖ψ‖ ^ 2 := hR_two_pi
      · have hbpos : 0 < b := by linarith
        rw [eval_mid b (not_le.mpr hbpos) (not_le.mpr hb2)]
        exact mul_le_mul_of_nonneg_left (hmono_int hab) (by positivity)

/-- `0 ≤ F_N(x) ≤ ‖ψ‖²` for all `x`. (Currently unused.) -/
lemma fejerCDF_bounded (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (x : ℝ) :
    fejerCDF U ψ N x ∈ Set.Icc 0 (‖ψ‖ ^ 2) := by
  have hmono := fejerCDF_monotone U hU ψ N
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · -- lower bound: 0 ≤ F_N x
    rcases le_or_gt x 0 with hx | hx
    · -- x ≤ 0 → F_N x = 0
      have hval : fejerCDF U ψ N x = 0 := by unfold fejerCDF; rw [if_pos hx]
      exact hval.ge
    · -- 0 < x → F_N 0 ≤ F_N x, and F_N 0 = 0
      have h := hmono (le_of_lt hx)
      rwa [fejerCDF_zero] at h
  · -- upper bound: F_N x ≤ ‖ψ‖²
    rcases le_or_gt x (2 * Real.pi) with hx | hx
    · -- x ≤ 2π → F_N x ≤ F_N 2π = ‖ψ‖²
      have h := hmono hx
      rwa [fejerCDF_two_pi] at h
    · -- 2π < x → F_N x = ‖ψ‖²
      have hxpos : (0 : ℝ) < x := by linarith [Real.pi_pos]
      have hval : fejerCDF U ψ N x = ‖ψ‖ ^ 2 := by
        unfold fejerCDF
        rw [if_neg (not_le.mpr hxpos), if_pos (le_of_lt hx)]
      exact le_of_eq hval

/-- `F_N` is continuous. (Currently unused.) -/
lemma fejerCDF_continuous (ψ : H) (N : ℕ) :
    Continuous (fejerCDF U ψ N) := by
  have hf_cont : Continuous (fun θ => (fejerMeanDensity U ψ N θ).re) :=
    Complex.continuous_re.comp (fejerMeanDensity_continuous U ψ N)
  have hf_ii : ∀ a b : ℝ,
      IntervalIntegrable (fun θ => (fejerMeanDensity U ψ N θ).re) volume a b :=
    fun a b => hf_cont.intervalIntegrable a b
  -- the clamp  x ↦ max 0 (min x 2π)  into [0, 2π]
  have hc_cont : Continuous (fun x : ℝ => max 0 (min x (2 * Real.pi))) :=
    continuous_const.max (continuous_id.min continuous_const)
  -- the candidate continuous function:  (1/2π) · primitive(clamp x)
  have hg_cont : Continuous (fun x : ℝ => (1 / (2 * Real.pi)) *
      ∫ t in (0:ℝ)..(max 0 (min x (2 * Real.pi))), (fejerMeanDensity U ψ N t).re) :=
    continuous_const.mul
      ((intervalIntegral.continuous_primitive hf_ii 0).comp hc_cont)
  have hGset := fejerCDF_hGset U ψ N
  have hR_two_pi := fejerCDF_hR_two_pi U ψ N
  have hpi2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  -- F_N agrees pointwise with the continuous candidate
  have key : ∀ x : ℝ, fejerCDF U ψ N x
      = (1 / (2 * Real.pi)) *
        ∫ t in (0:ℝ)..(max 0 (min x (2 * Real.pi))), (fejerMeanDensity U ψ N t).re := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · -- x ≤ 0 : clamp = 0, primitive = 0
      have hmax : max 0 (min x (2 * Real.pi)) = 0 := by
        rw [min_eq_left (le_trans hx hpi2)]; exact max_eq_left hx
      rw [hmax, intervalIntegral.integral_same, mul_zero]
      unfold fejerCDF; rw [if_pos hx]
    · rcases le_or_gt (2 * Real.pi) x with hx2 | hx2
      · -- 2π ≤ x : clamp = 2π, primitive = ‖ψ‖²
        have hmax : max 0 (min x (2 * Real.pi)) = 2 * Real.pi := by
          rw [min_eq_right hx2]; exact max_eq_right hpi2
        rw [hmax, hGset (2 * Real.pi) hpi2, hR_two_pi]
        unfold fejerCDF; rw [if_neg (not_le.mpr hx), if_pos hx2]
      · -- 0 < x < 2π : clamp = x
        have hmax : max 0 (min x (2 * Real.pi)) = x := by
          rw [min_eq_left (le_of_lt hx2)]; exact max_eq_right (le_of_lt hx)
        rw [hmax, hGset x (le_of_lt hx)]
        unfold fejerCDF; rw [if_neg (not_le.mpr hx), if_neg (not_le.mpr hx2)]
  exact hg_cont.congr (fun x => (key x).symm)

/-- `σ_N((a, b]) = F_N(b) - F_N(a)` for `0 ≤ a ≤ b ≤ 2π`. (Currently unused.) -/
lemma fejerCDF_eq_measure (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * Real.pi) :
    fejerCDF U ψ N b - fejerCDF U ψ N a =
    (fejerMeasure U ψ N (Set.Ioc a b)).toReal := by
  have hpi2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hb0 : 0 ≤ b := le_trans ha hab
  have ha2π : a ≤ 2 * Real.pi := le_trans hab hb
  have hsub : Set.Ioc a b ⊆ Set.Icc 0 (2 * Real.pi) :=
    Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc ha hb)
  have hf_ii : ∀ p q : ℝ,
      IntervalIntegrable (fun θ => (fejerMeanDensity U ψ N θ).re) volume p q :=
    fun p q => (Complex.continuous_re.comp
      (fejerMeanDensity_continuous U ψ N)).intervalIntegrable p q
  have hGset := fejerCDF_hGset U ψ N
  have hR_two_pi := fejerCDF_hR_two_pi U ψ N
  -- F_N on [0,2π] equals the primitive  (1/2π) ∫₀ˣ
  have hcdf_mid : ∀ x : ℝ, 0 ≤ x → x ≤ 2 * Real.pi →
      fejerCDF U ψ N x
        = (1 / (2 * Real.pi)) * ∫ t in (0:ℝ)..x, (fejerMeanDensity U ψ N t).re := by
    intro x hx0 hx2π
    rcases lt_or_eq_of_le hx0 with hx0' | hx0'
    · rcases lt_or_eq_of_le hx2π with hx2' | hx2'
      · -- 0 < x < 2π
        rw [hGset x (le_of_lt hx0')]
        unfold fejerCDF
        rw [if_neg (not_le.mpr hx0'), if_neg (not_le.mpr hx2')]
      · -- x = 2π
        subst hx2'
        rw [hGset (2 * Real.pi) hpi2, hR_two_pi]
        exact fejerCDF_two_pi U ψ N
    · -- 0 = x
      subst hx0'
      rw [intervalIntegral.integral_same, mul_zero]
      exact fejerCDF_zero U ψ N
  -- measure of (a, b]
  have hf_nn : ∀ θ, 0 ≤ (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re :=
    fun θ => mul_nonneg (by positivity) (fejerMeanDensity_nonneg U hU ψ N θ)
  have hf_int_Icc : IntegrableOn
      (fun θ => (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re)
      (Set.Icc 0 (2 * Real.pi)) volume :=
    (continuous_const.mul (Complex.continuous_re.comp
      (fejerMeanDensity_continuous U ψ N))).continuousOn.integrableOn_compact isCompact_Icc
  have hf_int : IntegrableOn
      (fun θ => (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re)
      (Set.Ioc a b) volume := hf_int_Icc.mono_set hsub
  have hmeasure : (fejerMeasure U ψ N (Set.Ioc a b)).toReal
      = (1 / (2 * Real.pi)) * ∫ θ in Set.Ioc a b, (fejerMeanDensity U ψ N θ).re := by
    unfold fejerMeasure
    rw [withDensity_apply (fun θ => ENNReal.ofReal ((1 / (2 * Real.pi)) *
          (fejerMeanDensity U ψ N θ).re)) measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_self_of_subset_left hsub,
        ← ofReal_integral_eq_lintegral_ofReal hf_int (ae_of_all _ hf_nn),
        ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_of_all _ hf_nn)),
        integral_const_mul]
  -- CDF difference  (telescoping ∫₀ᵇ − ∫₀ᵃ = ∫ₐᵇ)
  have hcdf : fejerCDF U ψ N b - fejerCDF U ψ N a
      = (1 / (2 * Real.pi)) * ∫ θ in Set.Ioc a b, (fejerMeanDensity U ψ N θ).re := by
    rw [hcdf_mid b hb0 hb, hcdf_mid a ha ha2π, ← mul_sub]
    congr 1
    rw [← intervalIntegral.integral_of_le hab]
    have hadj := intervalIntegral.integral_add_adjacent_intervals (hf_ii 0 a) (hf_ii a b)
    linarith [hadj]
  rw [hmeasure]; exact hcdf

end Spectra.Herglotz

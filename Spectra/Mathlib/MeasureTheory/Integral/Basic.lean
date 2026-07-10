/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Probability.Distributions.Gaussian.Real
/-!
# Bochner Integration for Exponentially Decaying Functions

This file provides foundational lemmas for Bochner integration of exponentially
decaying functions. These are the analytical tools needed for the resolvent
integral construction in Stone's theorem.

## Main results

* `integral_exp_neg_Ioc`: `∫₀^n e^{-x} dx = 1 - e^{-n}` on the finite interval `[0, n]`
* `integrableOn_exp_neg` / `integrableOn_exp_neg_Ioi`: `e^{-t}` is integrable on `[0, ∞)` / `(0, ∞)`
* `integral_exp_neg_eq_one`: `∫₀^∞ e^{-t} dt = 1`
* `integrable_exp_decay_continuous`: `e^{-t} • f(t)` is integrable if `f` is bounded
* `norm_integral_exp_decay_le`: `‖∫₀^∞ e^{-t} • f(t) dt‖ ≤ C` if `‖f(t)‖ ≤ C`
* `hasDerivAt_integral_of_exp_decay`: differentiation under the integral sign

## Implementation notes

The exponential weight `e^{-t}` ensures integrability. The parameter `λ = 1` is
arbitrary; any `λ > 0` works. This corresponds to evaluating resolvents at `z = ±i`.

## Tags

Bochner integral, exponential decay, improper integral
-/

namespace MeasureTheory.Integral

open Filter Topology

section BasicBochner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The finite-interval antiderivative fact `∫₀^n e^{-x} dx = 1 - e^{-n}`, obtained from
`HasDerivAt (fun t => -e^{-t}) (e^{-x})` via the fundamental theorem of calculus. -/
lemma integral_exp_neg_Ioc (n : ℕ) : ∫ x in (0 : ℝ)..n, Real.exp (-x) = 1 - Real.exp (-n) := by
  by_cases hn : (n : ℝ) ≤ 0
  · have hn' : n = 0 := Nat.cast_eq_zero.mp (le_antisymm hn (Nat.cast_nonneg n))
    simp [hn', intervalIntegral.integral_same]
  · push Not at hn
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) n,
        HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t => -t) (-1) x := hasDerivAt_neg x
      have h2 : HasDerivAt Real.exp (Real.exp (-x)) (-x) := Real.hasDerivAt_exp (-x)
      convert (h2.comp x h1).neg using 1
      ring
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hn)
            ((Real.continuous_exp.comp continuous_neg).continuousOn.neg)
            (fun x hx => hderiv x hx)
            ((Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 n) using 1
    simp [Real.exp_zero]; ring

/-- `e^{-t}` is integrable on `[0, ∞)` (as a function of `t : ℝ`). -/
lemma integrableOn_exp_neg : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_neg_Ioi 0

/-- The total mass of `e^{-t}` on `[0, ∞)` is `1`, i.e. `∫₀^∞ e^{-t} dt = 1`. -/
lemma integral_exp_neg_eq_one : ∫ t in Set.Ici (0 : ℝ), Real.exp (-t) = 1 := by
  rw [integral_Ici_eq_integral_Ioi]
  exact integral_exp_neg_Ioi_zero

/-- `e^{-t}` is integrable on the open ray `(0, ∞)`. -/
lemma integrableOn_exp_neg_Ioi : IntegrableOn (fun t => Real.exp (-t)) (Set.Ioi 0) volume :=
  integrableOn_exp_neg.mono_set Set.Ioi_subset_Ici_self

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A continuous `V`-valued function bounded by `C` on `[0, ∞)` becomes Bochner-integrable
once weighted by `e^{-t}`, by domination against `(max |C| 1) · e^{-t}`. -/
lemma integrable_exp_decay_continuous
    (f : ℝ → V) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) :
    IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume := by
  set M := max |C| 1 with _hM_def
  have _hM_pos : 0 < M := lt_max_of_lt_right one_pos
  have hM_ge : |C| ≤ M := le_max_left _ _
  have h_exp_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume :=
    integrableOn_exp_neg
  have h_bound_int : IntegrableOn (fun t => M * Real.exp (-t)) (Set.Ici 0) volume :=
    h_exp_int.const_mul M
  have h_meas : AEStronglyMeasurable (fun t => Real.exp (-t) • f t)
                                      (volume.restrict (Set.Ici 0)) := by
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable.restrict
    · exact hf_cont.aestronglyMeasurable.restrict
  have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ici 0)),
                  ‖Real.exp (-t) • f t‖ ≤ M * Real.exp (-t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    calc Real.exp (-t) * ‖f t‖
        ≤ Real.exp (-t) * |C| := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            calc ‖f t‖ ≤ C := hC t ht
              _ ≤ |C| := le_abs_self C
      _ ≤ Real.exp (-t) * M := mul_le_mul_of_nonneg_left hM_ge (Real.exp_pos _).le
      _ = M * Real.exp (-t) := mul_comm _ _
  exact Integrable.mono' h_bound_int h_meas h_bound

/-- `‖∫₀^∞ e^{-t} • f(t) dt‖ ≤ C` whenever `f` is continuous and bounded by `C` on `[0, ∞)`.
The hypothesis `0 ≤ C` is not assumed: it is already forced by `hC 0 (le_refl 0)` together with
`‖f 0‖ ≥ 0`. -/
lemma norm_integral_exp_decay_le
    (f : ℝ → V) (hf_cont : Continuous f)
    (C : ℝ) (hC : ∀ t ≥ 0, ‖f t‖ ≤ C) :
    ‖∫ t in Set.Ici 0, Real.exp (-t) • f t‖ ≤ C := by
  have h_integrand_int : IntegrableOn (fun t => Real.exp (-t) • f t) (Set.Ici 0) volume :=
    integrable_exp_decay_continuous f hf_cont C hC
  have h_exp_int : IntegrableOn (fun t => Real.exp (-t)) (Set.Ici 0) volume :=
    integrableOn_exp_neg
  calc ‖∫ t in Set.Ici 0, Real.exp (-t) • f t‖
      ≤ ∫ t in Set.Ici 0, ‖Real.exp (-t) • f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ici 0, C * Real.exp (-t) := by
        apply setIntegral_mono_on h_integrand_int.norm (h_exp_int.const_mul C) measurableSet_Ici
        intro t ht
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
        calc Real.exp (-t) * ‖f t‖
            ≤ Real.exp (-t) * C := mul_le_mul_of_nonneg_left (hC t ht) (Real.exp_pos _).le
          _ = C * Real.exp (-t) := mul_comm _ _
    _ = C * ∫ t in Set.Ici 0, Real.exp (-t) :=
        MeasureTheory.integral_const_mul C fun a => Real.exp (-a)
    _ = C * 1 := by rw [integral_exp_neg_eq_one]
    _ = C := mul_one C

/-- Differentiation under the integral sign for the exponentially-weighted integral: if
`f τ s` is continuous, differentiable in `τ` with derivative continuous in `s`, and both `f`
and its `τ`-derivative are bounded by `C` on `s ≥ 0`, then
`τ ↦ ∫₀^∞ e^{-s} • f τ s` is differentiable at `t` with derivative `∫₀^∞ e^{-s} • ∂_τ f t s`. -/
lemma hasDerivAt_integral_of_exp_decay
    (f : ℝ → ℝ → V)
    (hf_cont : Continuous (Function.uncurry f))
    (hf_deriv : ∀ t s, HasDerivAt (f · s) (deriv (f · s) t) t)
    (hf'_cont : ∀ t, Continuous (fun s => deriv (f · s) t))
    (C : ℝ) (hC : ∀ t s, s ≥ 0 → ‖f t s‖ ≤ C)
    (hC' : ∀ t s, s ≥ 0 → ‖deriv (f · s) t‖ ≤ C)
    (t : ℝ) :
    HasDerivAt (fun τ => ∫ s in Set.Ici 0, Real.exp (-s) • f τ s)
               (∫ s in Set.Ici 0, Real.exp (-s) • deriv (f · s) t)
               t := by
  let μ := volume.restrict (Set.Ici (0 : ℝ))
  let M := max |C| 1
  have _hM_pos : 0 < M := lt_max_of_lt_right one_pos
  have hC_le_M : |C| ≤ M := le_max_left _ _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (x₀ := t)
    (F := fun τ s => Real.exp (-s) • f τ s)
    (F' := fun τ s => Real.exp (-s) • deriv (f · s) τ)
    (bound := fun s => M * Real.exp (-s))
    (Metric.ball_mem_nhds t one_pos)  -- was: (ε := 1) one_pos
    ?hF_meas ?hF_int ?hF'_meas ?hF'_bound ?hbound_int ?hF_deriv
  case hF_meas =>
    filter_upwards with τ
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable.restrict
    · exact (hf_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  case hF_int =>
    have hf_t_cont : Continuous (fun s => f t s) :=
      hf_cont.comp (continuous_const.prodMk continuous_id)
    have hf_t_bound : ∀ s ≥ 0, ‖f t s‖ ≤ |C| := fun s hs => (hC t s hs).trans (le_abs_self C)
    exact integrable_exp_decay_continuous (fun s => f t s) hf_t_cont |C| hf_t_bound
  case hF'_meas =>
    apply AEStronglyMeasurable.smul
    · exact (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable
    · exact (hf'_cont t).aestronglyMeasurable
  case hF'_bound =>
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs τ _
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    calc Real.exp (-s) * ‖deriv (f · s) τ‖
        ≤ Real.exp (-s) * M :=
          mul_le_mul_of_nonneg_left
            ((hC' τ s hs).trans ((le_abs_self C).trans hC_le_M))
            (le_of_lt (Real.exp_pos _))
      _ = M * Real.exp (-s) := mul_comm _ _
  case hbound_int =>
    exact integrableOn_exp_neg.const_mul M
  case hF_deriv =>
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s _ τ _
    exact (hf_deriv τ s).const_smul (Real.exp (-s))
  exact h.2

end BasicBochner

end MeasureTheory.Integral

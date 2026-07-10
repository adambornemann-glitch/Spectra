/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The scalar Klein inequality

The analytic heart of Klein's inequality for the quantum relative entropy is the scalar inequality
`λ − μ ≤ λ · log(λ/μ)` for `0 ≤ λ`, `0 < μ` — equivalently `λ log λ − λ log μ ≥ λ − μ`.  Summed over
the joint eigenvalue distribution of two density operators it yields `D(ρ‖σ) ≥ Tr ρ − Tr σ = 0`.

This file isolates that purely real-analytic fact (a one-line consequence of `x − 1 ≤ x log x`), so
the operator-theoretic relative-entropy development can consume it without carrying real-analysis
lemmas.  It also records the **integral form** of the tangent-line Jensen inequality for `log`,
`∫ log f ≤ log (∫ f)` on a probability measure — the analytic core of the *full* (Umegaki) leg of
Klein's inequality, obtained by integrating the same tangent-line bound `log x ≤ x − 1` rather than
appealing to `ConcaveOn.le_map_integral` (which would require `log` to be continuous on a *closed*
set — impossible near `0`).

## Main results

* `Real.klein_scalar` — `λ − μ ≤ λ · log(λ/μ)`.
* `Real.mul_log_sub_mul_log_ge` — the rearranged form `λ log λ − λ log μ ≥ λ − μ`.
* `Real.integral_log_le_log_of_probability` — `∫ log f ≤ log (∫ f)` for a probability measure with
  `∫ f = s > 0` and `f > 0` a.e., via the tangent line `log(f/s) ≤ f/s − 1`.
-/

open MeasureTheory

namespace Real

/-- **The scalar Klein inequality.** For `0 ≤ λ` and `0 < μ`, `λ − μ ≤ λ · log(λ/μ)`.  This is the
termwise inequality behind Klein's inequality `D(ρ‖σ) ≥ 0` for the quantum relative entropy. -/
lemma klein_scalar {lam mu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 < mu) :
    lam - mu ≤ lam * Real.log (lam / mu) := by
  have hx : 0 ≤ lam / mu := div_nonneg hlam hmu.le
  have h := Real.self_sub_one_le_mul_log hx
  have key : mu * (lam / mu - 1) ≤ mu * (lam / mu * Real.log (lam / mu)) :=
    mul_le_mul_of_nonneg_left h hmu.le
  have e1 : mu * (lam / mu - 1) = lam - mu := by field_simp
  have e2 : mu * (lam / mu * Real.log (lam / mu)) = lam * Real.log (lam / mu) := by
    field_simp
  rwa [e1, e2] at key

/-- **Klein's inequality, rearranged.** For `0 < λ` and `0 < μ`,
`λ log λ − λ log μ ≥ λ − μ`.  (The `log(λ/μ) = log λ − log μ` split needs `λ > 0`.) -/
lemma mul_log_sub_mul_log_ge {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) :
    lam - mu ≤ lam * Real.log lam - lam * Real.log mu := by
  have h := klein_scalar hlam.le hmu
  rwa [Real.log_div hlam.ne' hmu.ne', mul_sub] at h

/-- **Integral form of the tangent-line Jensen inequality for `log`.**  For a probability measure
`μ`, a function `f` that is `> 0` `μ`-a.e., integrable, with `log ∘ f` integrable and mean
`∫ f = s > 0`, one has `∫ log f ≤ log s`.  This is Jensen's inequality for the concave `log`,
proved *without* `ConcaveOn.le_map_integral` (which needs a closed domain of continuity — `log`
has none containing `0`): integrate the pointwise tangent line `log(f x / s) ≤ f x / s − 1`
(`Real.log_le_sub_one_of_pos`), i.e. `log (f x) ≤ log s + (f x − s)/s`, whose integral is exactly
`log s` because `∫ (f − s) = s − s = 0`. -/
lemma integral_log_le_log_of_probability {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {s : ℝ} (hs : 0 < s)
    (hf_pos : ∀ᵐ x ∂μ, 0 < f x) (hf_int : Integrable f μ)
    (hlog_int : Integrable (fun x => Real.log (f x)) μ) (hmean : ∫ x, f x ∂μ = s) :
    ∫ x, Real.log (f x) ∂μ ≤ Real.log s := by
  -- the pointwise tangent-line bound, `μ`-a.e.
  have hkey : ∀ᵐ x ∂μ, Real.log (f x) ≤ Real.log s + (f x - s) / s := by
    filter_upwards [hf_pos] with x hx
    have h := Real.log_le_sub_one_of_pos (div_pos hx hs)
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hs)] at h
    have hrw : f x / s - 1 = (f x - s) / s := by field_simp
    rw [hrw] at h; linarith
  -- the affine minorant `x ↦ log s + (f x − s)/s` is integrable
  have hg_int : Integrable (fun x => (f x - s) / s) μ := by
    have hrw : (fun x => (f x - s) / s) = (fun x => (1 / s) * (f x - s)) := by
      funext x; rw [div_eq_inv_mul, one_div]
    rw [hrw]; exact (hf_int.sub (integrable_const s)).const_mul (1 / s)
  have hmin_int : Integrable (fun x => Real.log s + (f x - s) / s) μ :=
    (integrable_const _).add hg_int
  -- its mean is `log s`, since `∫ (f − s) = 0`
  have hint2 : ∫ x, (f x - s) / s ∂μ = 0 := by
    have hrw : (fun x => (f x - s) / s) = (fun x => (1 / s) * (f x - s)) := by
      funext x; rw [div_eq_inv_mul, one_div]
    rw [hrw, integral_const_mul, integral_sub hf_int (integrable_const s), integral_const, hmean]
    simp
  calc ∫ x, Real.log (f x) ∂μ
      ≤ ∫ x, (Real.log s + (f x - s) / s) ∂μ := integral_mono_ae hlog_int hmin_int hkey
    _ = (∫ _x, Real.log s ∂μ) + ∫ x, (f x - s) / s ∂μ := integral_add (integrable_const _) hg_int
    _ = Real.log s := by rw [hint2, integral_const]; simp

end Real

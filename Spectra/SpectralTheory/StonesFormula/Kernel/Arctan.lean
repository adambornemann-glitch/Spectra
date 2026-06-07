/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: StonesFormula/Kernel/Arctan.lean
-/
import Spectra.SpectralTheory.StonesFormula.Kernel.Defs
import Spectra.SpectralTheory.FourierTransform

/-!
# Resolvent Kernel Analysis

This file develops the analytical properties of the resolvent kernel `(s - z)⁻¹`
and the associated Lorentzian approximation to the delta function.

### Arctan integration
* `lorentzian_arctan_integral`: `∫_a^b ε/((s-t)² + ε²) dt = arctan(...) - arctan(...)`
* `arctan_indicator_limit`: The arctan kernel converges to the indicator function
* `arctan_kernel_bound`: The arctan kernel is uniformly bounded by 1

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VII
* Stone, "Linear Transformations in Hilbert Space" (1932)

## Tags

resolvent, Lorentzian, approximate identity, Poisson kernel
-/
namespace QuantumMechanics.SpectralTheory

open FourierUniqueness
open Complex MeasureTheory Filter Topology TopologicalSpace
open scoped NNReal ENNReal InnerProductSpace

/-- Arctan antiderivative for the Lorentzian kernel.
`∫_a^b ε/((s-t)² + ε²) dt = arctan((b-s)/ε) - arctan((a-s)/ε)`
This is obtained by the substitution `u = (t-s)/ε`. -/
lemma lorentzian_arctan_integral (s a b ε : ℝ) (hε : ε > 0) :
    ∫ t in a..b, ε / ((s - t)^2 + ε^2) =
      Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε) := by
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  let F : ℝ → ℝ := fun t => Real.arctan ((t - s) / ε)
  suffices h : ∫ t in a..b, ε / ((s - t)^2 + ε^2) = F b - F a by
    simp only [F] at h; exact h
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  -- HasDerivAt on uIcc
  · intro t _
    have hg : HasDerivAt (fun t => (t - s) / ε) (1 / ε) t := by
      simpa using ((hasDerivAt_id t).sub (hasDerivAt_const t s)).div_const ε
    have hchain := (Real.hasDerivAt_arctan ((t - s) / ε)).comp t hg
    convert hchain using 1
    have : (s - t) ^ 2 + ε ^ 2 > 0 := by positivity
    have : 1 + ((t - s) / ε) ^ 2 > 0 := by positivity
    field_simp
    ring
  -- IntervalIntegrable
  · apply Continuous.intervalIntegrable
    apply continuous_const.div
    · exact ((continuous_const.sub continuous_id).pow 2).add continuous_const
    · intro t; positivity

/-- The arctan kernel converges to the indicator function away from endpoints.
For `s ∉ {a, b}`, `(1/π)[arctan((b-s)/ε) - arctan((a-s)/ε)] → 𝟙_{(a,b]}(s)` as
`ε → 0+` At the endpoints `s = a` and `s = b` the limit is `1/2`, not `0` or
`1`, which is the source of the averaged endpoint terms in Stone's formula.
This is because `arctan(x) → π/2` as `x → +∞` and `arctan(x) → -π/2` as `x → -∞`.-/
lemma arctan_indicator_limit (a b s : ℝ) (hab : a < b)
    (hs_a : s ≠ a) (hs_b : s ≠ b) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)))
      (𝓝[>] 0)
      (𝓝 (Set.indicator (Set.Ioc a b) 1 s)) := by
  have hπ_pos := Real.pi_pos
  -- Step 1: c/ε → +∞ as ε → 0+ when c > 0
  have div_atTop : ∀ c : ℝ, 0 < c →
      Tendsto (fun ε : ℝ => c / ε) (𝓝[>] 0) atTop := by
    intro c hc
    simp_rw [div_eq_mul_inv, mul_comm c]
    exact tendsto_inv_nhdsGT_zero.atTop_mul_const hc
  -- Step 2: c/ε → -∞ when c < 0
  have div_atBot : ∀ c : ℝ, c < 0 →
      Tendsto (fun ε : ℝ => c / ε) (𝓝[>] 0) atBot := by
    intro c hc
    have key : (fun ε : ℝ => c / ε) = (fun ε => -((-c) / ε)) := by ext; simp [neg_div]
    rw [key]
    exact tendsto_neg_atTop_atBot.comp (div_atTop (-c) (neg_pos.mpr hc))
  -- Step 3: arctan limit compositions
  have lim_pos : ∀ c : ℝ, 0 < c →
      Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (Real.pi / 2)) :=
    fun c hc => (Real.tendsto_arctan_atTop.comp (div_atTop c hc)).mono_right nhdsWithin_le_nhds
  have lim_neg : ∀ c : ℝ, c < 0 →
      Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (-(Real.pi / 2))) :=
    fun c hc => (Real.tendsto_arctan_atBot.comp (div_atBot c hc)).mono_right nhdsWithin_le_nhds
  -- Step 4: case analysis on s
  rcases lt_or_gt_of_ne hs_a with hsa | hsa
  · -- s < a: both (b-s), (a-s) > 0 → both arctans → π/2 → difference → 0
    have hmem : s ∉ Set.Ioc a b := fun h => absurd h.1 (not_lt.mpr (le_of_lt hsa))
    simp only [Set.indicator_apply, if_neg hmem, Pi.one_apply]
    have h1 := (lim_pos _ (by aesop)).sub (lim_pos _ (by aesop))
    simp only [sub_self] at h1
    have h2 := (tendsto_const_nhds (x := 1 / Real.pi)).mul h1
    exact FourierUniqueness.arctanRecovery_tendsto_zero_of_lt' hsa hab
  · rcases lt_or_gt_of_ne hs_b with hsb | hsb
    · -- a < s < b: (b-s) > 0 → π/2, (a-s) < 0 → -π/2, difference → π
      have hmem : s ∈ Set.Ioc a b := ⟨hsa, le_of_lt hsb⟩
      simp only [Set.indicator_of_mem hmem, Pi.one_apply]
      have hbs : 0 < b - s := by linarith
      have has : a - s < 0 := by linarith
      have h1 := (lim_pos _ hbs).sub (lim_neg _ has)
      simp only [sub_neg_eq_add, add_halves] at h1
      have h2 := (tendsto_const_nhds (x := 1 / Real.pi)).mul h1
      simpa [div_mul_cancel₀] using h2
    · -- s > b: both (b-s), (a-s) < 0 → both arctans → -π/2 → difference → 0
      have hmem : s ∉ Set.Ioc a b := fun h => absurd h.2 (not_le.mpr hsb)
      simp only [Set.indicator_apply, if_neg hmem, Pi.one_apply]
      have hbs : b - s < 0 := by linarith
      have has : a - s < 0 := by linarith [hab]
      have h1 := (lim_neg _ hbs).sub (lim_neg _ has)
      simp only [sub_self] at h1
      have h2 := (tendsto_const_nhds (x := 1 / Real.pi)).mul h1
      simpa [mul_zero] using h2

/-- The arctan kernel is uniformly bounded by 1.
Since `|arctan(x)| ≤ π/2` for all `x`, the difference is at most `π`. -/
lemma arctan_kernel_bound (a b s ε : ℝ) (_hε : ε > 0) :
    |(1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))| ≤ 1 := by
  have hπ_pos := Real.pi_pos
  have h_diff : |Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)| ≤ Real.pi := by
    rw [abs_le]
    constructor <;>
      linarith [Real.neg_pi_div_two_lt_arctan ((b - s) / ε),
        Real.arctan_lt_pi_div_two ((b - s) / ε),
        Real.neg_pi_div_two_lt_arctan ((a - s) / ε),
        Real.arctan_lt_pi_div_two ((a - s) / ε)]
  rw [abs_mul, abs_of_pos (by positivity)]
  calc (1 / Real.pi) * |Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)|
      ≤ (1 / Real.pi) * Real.pi := by apply mul_le_mul_of_nonneg_left h_diff; positivity
    _ = 1 := by field_simp

end QuantumMechanics.SpectralTheory

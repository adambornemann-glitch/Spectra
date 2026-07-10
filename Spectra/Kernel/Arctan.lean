/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Kernel.Defs
import Spectra.Fourier.IsUnique
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
open Filter Topology
open Spectra.Fourier
namespace Spectra.Kernels

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

/-- The "arctan recovery function": for fixed ε > 0, the function
    `ω ↦ (1/π)[arctan((b-ω)/ε) - arctan((a-ω)/ε)]`
    is bounded between 0 and 1 and converges to `1_{(a,b]}(ω)` as ε → 0⁺. -/
noncomputable def arctanRecovery (ε : ℝ) (a b : ℝ) (ω : ℝ) : ℝ :=
  (1 / Real.pi) * (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))

/-! ### Helpers: division by ε → 0⁺ sends constants to ±∞ -/

/-- If `c > 0`, then `c / ε → +∞` as `ε → 0⁺`. -/
lemma tendsto_pos_div_zero_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε => c / ε) (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (·⁻¹ : ℝ → ℝ) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  rw [Filter.tendsto_atTop] at hinv ⊢
  intro M
  filter_upwards [hinv (M / c)] with ε hε
  calc M = c * (M / c) := by field_simp
    _ ≤ c * ε⁻¹ := by apply mul_le_mul_of_nonneg_left hε hc.le
    _ = c / ε := by rw [div_eq_mul_inv]

/-- If `c < 0`, then `c / ε → -∞` as `ε → 0⁺`. -/
lemma tendsto_neg_div_zero_atBot {c : ℝ} (hc : c < 0) :
    Tendsto (fun ε => c / ε) (𝓝[>] (0 : ℝ)) atBot := by
  have key : Tendsto (fun ε => (-c) / ε) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_pos_div_zero_atTop (neg_pos.mpr hc)
  have : Tendsto (fun ε => -((-c) / ε)) (𝓝[>] (0 : ℝ)) atBot :=
    Filter.tendsto_neg_atTop_atBot.comp key
  convert this using 1; ext ε; simp [neg_div]

/-- For `ω < a` (strictly to the left), `arctanRecovery ε a b ω → 0` as `ε → 0⁺`. -/
lemma arctanRecovery_tendsto_zero_of_lt {a b ω : ℝ} (hω : ω < a)
    {b' : ℝ} (hab : a ≤ b') (hbb : b' = b) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0) := by
  unfold arctanRecovery
  -- Both (b-ω)/ε and (a-ω)/ε → +∞ since b-ω > a-ω > 0
  have h1 : Tendsto (fun ε => Real.arctan ((b - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp
      (tendsto_pos_div_zero_atTop (by linarith [hab, hbb]))).mono_right
      nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε => Real.arctan ((a - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp
      (tendsto_pos_div_zero_atTop (by linarith))).mono_right nhdsWithin_le_nhds
  have h_diff : Tendsto (fun ε => Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2 - Real.pi / 2)) :=
    h1.sub h2
  rw [sub_self] at h_diff
  have h_mul : Tendsto (fun ε => (1 / Real.pi) *
      (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / Real.pi) * 0)) :=
    tendsto_const_nhds.mul h_diff
  rwa [mul_zero] at h_mul

/-- For `ω < a` (original signature without extra params). -/
lemma arctanRecovery_tendsto_zero_of_lt' {a b ω : ℝ} (hω : ω < a) (hab : a < b) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0) :=
  arctanRecovery_tendsto_zero_of_lt hω (le_of_lt hab) rfl

/-- The arctan kernel converges to the indicator function away from endpoints.
For `s ∉ {a, b}`, `(1/π)[arctan((b-s)/ε) - arctan((a-s)/ε)] → 𝟙_{(a,b]}(s)` as
`ε → 0+` At the endpoints `s = a` and `s = b` the limit is `1/2`, not `0` or
`1`, which is the source of the averaged endpoint terms in Stone's formula.
This is because `arctan(x) → π/2` as `x → +∞` and `arctan(x) → -π/2` as `x → -∞`. -/
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
    have _h2 := (tendsto_const_nhds (x := 1 / Real.pi)).mul h1
    exact arctanRecovery_tendsto_zero_of_lt' hsa hab
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
  have _hπ_pos := Real.pi_pos
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

end Spectra.Kernels

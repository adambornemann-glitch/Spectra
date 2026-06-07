/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: FourierTransform/ArctanLim.lean
-/
import Spectra.SpectralTheory.FourierTransform.Bridge

namespace QuantumMechanics.FourierUniqueness

open Complex MeasureTheory Filter Topology Set


/-! ## §4: Arctan limits — recovering the indicator function

As `ε → 0⁺`, the arctan recovery function converges to `1_{(a,b]}` pointwise
(except possibly at the endpoints `a` and `b`). -/

/-- For `ω ∈ (a, b)` (strictly interior), `arctanRecovery ε a b ω → 1` as `ε → 0⁺`. -/
lemma arctanRecovery_tendsto_one {a b ω : ℝ} (ha : a < ω) (hb : ω < b) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 1) := by
  unfold arctanRecovery
  -- As ε → 0⁺: (b-ω)/ε → +∞ so arctan → π/2; (a-ω)/ε → -∞ so arctan → -π/2
  have h_top : Tendsto (fun ε => Real.arctan ((b - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp (tendsto_pos_div_zero_atTop (by linarith))).mono_right nhdsWithin_le_nhds

  have h_bot : Tendsto (fun ε => Real.arctan ((a - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp (tendsto_neg_div_zero_atBot (by linarith))).mono_right nhdsWithin_le_nhds

  have h_diff : Tendsto (fun ε => Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi / 2 - -(Real.pi / 2))) :=
    h_top.sub h_bot
  rw [show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring] at h_diff
  have h_mul : Tendsto (fun ε => (1 / Real.pi) *
      (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / Real.pi) * Real.pi)) :=
    tendsto_const_nhds.mul h_diff
  rwa [one_div_mul_cancel (ne_of_gt Real.pi_pos)] at h_mul

/-- For `ω < a` (strictly to the left), `arctanRecovery ε a b ω → 0` as `ε → 0⁺`. -/
lemma arctanRecovery_tendsto_zero_of_lt {a b ω : ℝ} (hω : ω < a)
    {b' : ℝ} (hab : a ≤ b') (hbb : b' = b) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0) := by
  unfold arctanRecovery
  -- Both (b-ω)/ε and (a-ω)/ε → +∞ since b-ω > a-ω > 0
  have h1 : Tendsto (fun ε => Real.arctan ((b - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp (tendsto_pos_div_zero_atTop (by linarith [hab, hbb]))).mono_right
      nhdsWithin_le_nhds

  have h2 : Tendsto (fun ε => Real.arctan ((a - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.comp (tendsto_pos_div_zero_atTop (by linarith))).mono_right nhdsWithin_le_nhds

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

/-- For `ω > b` (strictly to the right), `arctanRecovery ε a b ω → 0` as `ε → 0⁺`. -/
lemma arctanRecovery_tendsto_zero_of_gt {a b ω : ℝ} (hab : a < b) (hω : b < ω) :
    Tendsto (fun ε => arctanRecovery ε a b ω) (𝓝[>] 0) (𝓝 0) := by
  unfold arctanRecovery
  -- Both (b-ω)/ε and (a-ω)/ε → -∞ since both numerators are negative
  have h1 : Tendsto (fun ε => Real.arctan ((b - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp (tendsto_neg_div_zero_atBot (by linarith))).mono_right nhdsWithin_le_nhds

  have h2 : Tendsto (fun ε => Real.arctan ((a - ω) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp (tendsto_neg_div_zero_atBot (by linarith))).mono_right nhdsWithin_le_nhds

  have h_diff : Tendsto (fun ε => Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (-(Real.pi / 2) - -(Real.pi / 2))) :=
    h1.sub h2
  rw [sub_self] at h_diff
  have h_mul : Tendsto (fun ε => (1 / Real.pi) *
      (Real.arctan ((b - ω) / ε) - Real.arctan ((a - ω) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / Real.pi) * 0)) :=
    tendsto_const_nhds.mul h_diff
  rwa [mul_zero] at h_mul

/-- At the right endpoint `b`, the arctan recovery converges to `1/2`. -/
lemma arctanRecovery_tendsto_half_at_right {a b : ℝ} (hab : a < b) :
    Tendsto (fun ε => arctanRecovery ε a b b) (𝓝[>] 0) (𝓝 (1/2)) := by
  unfold arctanRecovery
  -- (b-b)/ε = 0 → arctan(0) = 0; (a-b)/ε → -∞ → arctan → -π/2
  simp only [sub_self, zero_div, Real.arctan_zero]
  have h_bot : Tendsto (fun ε => Real.arctan ((a - b) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.comp (tendsto_neg_div_zero_atBot (by linarith))).mono_right nhdsWithin_le_nhds

  have h_diff : Tendsto (fun ε => 0 - Real.arctan ((a - b) / ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 - -(Real.pi / 2))) :=
    tendsto_const_nhds.sub h_bot
  -- Replace the simp + h_mul block with:
  have h_mul : Tendsto (fun ε => (1 / Real.pi) * (0 - Real.arctan ((a - b) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 / Real.pi) * (0 - -(Real.pi / 2)))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub h_bot)
  simp only [zero_sub, neg_neg, one_div] at h_mul
  convert h_mul using 1
  simp only [one_div, zero_sub, mul_neg]
  field_simp

end QuantumMechanics.FourierUniqueness

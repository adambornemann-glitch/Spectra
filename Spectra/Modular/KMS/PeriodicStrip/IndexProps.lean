/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.PeriodicStrip.Defs

/-!
# The strip index and the fundamental-strip reduction

This file develops the basic properties of `stripIndex` and `toFundamentalStrip`: the
floor-based integer `stripIndex β z` picking out which horizontal copy `[n·β, (n+1)·β)` of the
strip `z.im` falls into (`stripIndex_spec`), and the reduction map `toFundamentalStrip β z` that
shifts `z` down into the fundamental strip `{0 ≤ Im z < β}` (`toFundamentalStrip_im`,
`toFundamentalStrip_mem_closedStrip`, `toFundamentalStrip_of_mem_strip`).

It then proves the key seam-continuity lemma `periodicExtension_continuous_at_boundary`: at a
boundary point `Im z = n·β`, the periodic extension is continuous, because the periodicity
hypothesis `F(t) = F(t + iβ)` glues the value approached from below to the value approached from
above. Finally, `interior_closedStrip` identifies the interior of the closed strip with the open
strip.

## Main results

* `stripIndex_spec`, `toFundamentalStrip_im`, `toFundamentalStrip_mem_closedStrip`
* `periodicExtension_continuous_at_boundary`
* `interior_closedStrip`
-/

open Complex Set Filter Topology Int MeasureTheory
namespace Spectra.PeriodicHolomorphic

variable {β : ℝ}

/-! ## Basic Properties of the Strip Index -/

/-- `stripIndex β z` is the unique integer `n` with `n * β ≤ z.im < (n + 1) * β`. -/
lemma stripIndex_spec (hβ : 0 < β) (z : ℂ) :
    (stripIndex β z : ℝ) * β ≤ z.im ∧ z.im < (stripIndex β z + 1 : ℤ) * β := by
  constructor
  · have h := Int.floor_le (z.im / β)
    calc (stripIndex β z : ℝ) * β = ⌊z.im / β⌋ * β := rfl
      _ ≤ (z.im / β) * β := by exact mul_le_mul_of_nonneg_right h (le_of_lt hβ)
      _ = z.im := by field_simp
  · have h := Int.lt_floor_add_one (z.im / β)
    calc z.im = (z.im / β) * β := by field_simp
      _ < (⌊z.im / β⌋ + 1) * β := by exact mul_lt_mul_of_pos_right h hβ
      _ = (stripIndex β z + 1 : ℤ) * β := by push_cast; rfl

/-- The imaginary part of `toFundamentalStrip β z` lies in `[0, β)`. -/
lemma toFundamentalStrip_im (hβ : 0 < β) (z : ℂ) :
    0 ≤ (toFundamentalStrip β z).im ∧ (toFundamentalStrip β z).im < β := by
  simp only [toFundamentalStrip, sub_im, mul_im, ofReal_im, mul_zero,
     ofReal_re, I_im, mul_one, I_re]
  obtain ⟨h1, h2⟩ := stripIndex_spec hβ z
  constructor
  · simp only [mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero, add_zero];
    linarith
  · simp only [Int.cast_add, Int.cast_one, add_mul, one_mul] at h2
    simp only [mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero, add_zero]
    linarith


/-- `toFundamentalStrip β z` always lands in the closed strip `ClosedStrip β`. -/
lemma toFundamentalStrip_mem_closedStrip (hβ : 0 < β) (z : ℂ) :
    toFundamentalStrip β z ∈ ClosedStrip β := by
  simp only [ClosedStrip, mem_setOf_eq]
  obtain ⟨h1, h2⟩ := toFundamentalStrip_im hβ z
  exact ⟨h1, le_of_lt h2⟩

/-- On the fundamental strip, toFundamentalStrip is the identity -/
lemma toFundamentalStrip_of_mem_strip (hβ : 0 < β) {z : ℂ}
    (hz : 0 ≤ z.im ∧ z.im < β) : toFundamentalStrip β z = z := by
  simp only [toFundamentalStrip]
  have hn : stripIndex β z = 0 := by
    simp only [stripIndex]
    rw [Int.floor_eq_zero_iff]
    constructor
    · exact div_nonneg hz.1 (le_of_lt hβ)
    · rw [propext (div_lt_one hβ)];
      rw [@RCLike.lt_iff_re_im]
      exact And.symm (And.imp_left (fun _a => rfl) hz)
  simp [hn]

/-! ## Continuity of the Periodic Extension -/

/-- Key lemma: the boundary condition ensures continuity at the seams.

If F(t) = F(t + iβ) for all t ∈ ℝ, then the periodic extension is continuous
at points where Im(z) = n*β.
-/
lemma periodicExtension_continuous_at_boundary
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hcont : ContinuousOn F (ClosedStrip β))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    (z : ℂ) (n : ℤ) (hz : z.im = n * β) :
    ContinuousAt (periodicExtension F β) z := by
  -- First, establish what stripIndex gives at z
  have hstrip_z : stripIndex β z = n := by
    simp only [stripIndex, hz]
    rw [mul_div_assoc, div_self (ne_of_gt hβ)]
    simp only [mul_one, floor_intCast]
  -- The fundamental strip image of z is on the lower boundary
  have hz_fund : toFundamentalStrip β z = realToLower z.re := by
    simp only [toFundamentalStrip, realToLower, hstrip_z]
    rw [Complex.ext_iff]
    constructor
    · simp
    · simp [hz]
  -- So the value at z is F(realToLower z.re)
  have hz_val : periodicExtension F β z = F (realToLower z.re) := by
    simp only [periodicExtension, hz_fund]
  -- Key points in the fundamental strip
  have hmem_lower : realToLower z.re ∈ ClosedStrip β := by
    simp only [ClosedStrip, realToLower, Set.mem_setOf_eq, ofReal_im]
    exact ⟨le_refl 0, le_of_lt hβ⟩
  have hmem_upper : realToUpper β z.re ∈ ClosedStrip β := by
    simp only [ClosedStrip, realToUpper, Set.mem_setOf_eq, add_im, ofReal_im,
               mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero]
    simp only [add_zero, zero_add, le_refl, and_true]
    exact le_of_lt hβ
  -- Use metric characterization of continuity
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Get δ's from continuity of F at both boundary points
  rw [Metric.continuousOn_iff] at hcont
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hcont (realToLower z.re) hmem_lower ε hε
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := hcont (realToUpper β z.re) hmem_upper ε hε
  -- Choose δ to also be at most β, so stripIndex doesn't jump more than 1
  use min (min δ₁ δ₂) β
  refine ⟨lt_min (lt_min hδ₁_pos hδ₂_pos) hβ, ?_⟩
  intro w hw
  -- Key fact: |w.im - z.im| < β, so stripIndex w ∈ {n-1, n}
  have him_dist : |w.im - z.im| < β := by
    calc |w.im - z.im| = |w.im - z.im| := rfl
      _ = |(w - z).im| := by simp [Complex.sub_im]
      _ ≤ ‖(w - z)‖ := by exact abs_im_le_norm (w - z)
      _ = dist w z := by rw [dist_eq_norm];
      _ < min (min δ₁ δ₂) β := hw
      _ ≤ β := min_le_right _ _
  have him_upper : w.im < (n + 1) * β := by
    have : w.im - z.im < β := (abs_lt.mp him_dist).2
    linarith [hz.symm ▸ this]
  have him_lower : (n - 1) * β < w.im := by
    have : -(β) < w.im - z.im := (abs_lt.mp him_dist).1
    calc (n - 1) * β = n * β - β := by ring
      _ < w.im := by linarith [hz.symm ▸ this]
  rw [hz_val]
  by_cases hwn : n * β ≤ w.im
  · -- Case 1: w.im ≥ n*β (at or above the boundary)
    -- stripIndex β w = n
    have hw_strip : stripIndex β w = n := by
      simp only [stripIndex]
      rw [Int.floor_eq_iff]
      constructor
      · exact (le_div_iff₀ hβ).mpr hwn
      · exact (div_lt_iff₀ hβ).mpr him_upper
    simp only [periodicExtension, toFundamentalStrip, hw_strip]
    -- Need to show: dist (F (w - n*β*I)) (F (realToLower z.re)) < ε
    apply hδ₁
    · -- w - n*β*I ∈ ClosedStrip β
      simp only [ClosedStrip, Set.mem_setOf_eq, sub_im, mul_im,
                 ofReal_im, mul_zero, ofReal_re, I_im, mul_one,
                 I_re,mul_re, intCast_re, ofReal_re, intCast_im,
                 ofReal_im, mul_zero, sub_zero, add_zero,
                 tsub_le_iff_right]
      constructor
      · linarith
      · linarith
    · -- dist (w - n*β*I) (realToLower z.re) < δ₁
      simp only [realToLower, dist_eq_norm]
      have heq : w - (n : ℂ) * β * I - z.re = w - z := by
        rw [Complex.ext_iff]
        constructor
        · simp [Complex.sub_re, Complex.mul_re]
        · simp only [Complex.sub_im, Complex.mul_im,
                     Complex.ofReal_im, mul_zero,
                     Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
                     sub_zero]
          rw [hz]
          simp only [mul_re, intCast_re, ofReal_re, intCast_im, ofReal_im, mul_zero, sub_zero,
            add_zero]
      rw [heq, ← dist_eq_norm]
      calc dist w z < min (min δ₁ δ₂) β := hw
        _ ≤ min δ₁ δ₂ := min_le_left _ _
        _ ≤ δ₁ := min_le_left _ _
  · -- Case 2: w.im < n*β (below the boundary)
    push Not at hwn
    -- stripIndex β w = n - 1
    have hw_strip : stripIndex β w = n - 1 := by
      simp only [stripIndex]
      rw [Int.floor_eq_iff]
      have _hβ_ne : β ≠ 0 := ne_of_gt hβ
      constructor
      · -- Need: ((n - 1 : ℤ) : ℝ) ≤ w.im / β
        rw [Int.cast_sub, Int.cast_one]
        have h1 : (n - 1 : ℝ) * β < w.im := him_lower
        have h2 : (n - 1 : ℝ) * β ≤ w.im := le_of_lt h1
        -- Divide both sides by β (β > 0)
        have h3 : (n - 1 : ℝ) ≤ w.im / β := by
          exact (le_div_iff₀ hβ).mpr h2
        exact h3
      · -- Need: w.im / β < n
        rw [div_lt_iff₀ hβ]
        simp only [cast_sub, cast_one, sub_add_cancel]
        exact hwn
    simp only [periodicExtension, toFundamentalStrip, hw_strip]
    -- The shifted point is w - (n-1)*β*I
    -- This is close to z - (n-1)*β*I = z.re + (n*β - (n-1)*β)*I = z.re + β*I = realToUpper β z.re
    -- By periodicity, F(realToUpper β z.re) = F(realToLower z.re)
    rw [hperiod z.re]
    apply hδ₂
    · -- w - (n-1)*β*I ∈ ClosedStrip β
      simp only [ClosedStrip, Set.mem_setOf_eq, sub_im, mul_im,
                 ofReal_im, mul_zero, ofReal_re, I_im, mul_one,
                 I_re, Int.cast_sub, Int.cast_one, mul_re, sub_re,
                 intCast_re, one_re, ofReal_re, sub_im, intCast_im,
                 one_im, sub_self, ofReal_im, mul_zero, sub_zero,
                 add_zero, tsub_le_iff_right]
      constructor
      · -- 0 ≤ w.im - (n-1)*β
        have : (n - 1) * β < w.im := him_lower
        linarith
      · -- w.im - (n-1)*β ≤ β, i.e., w.im ≤ n*β
        linarith
    · -- dist (w - (n-1)*β*I) (realToUpper β z.re) < δ₂
      simp only [realToUpper, dist_eq_norm]
      have heq : w - ((n : ℤ) - 1 : ℤ) * β * I - (z.re + β * I) = w - z := by
        rw [Complex.ext_iff]
        constructor
        · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
        · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, mul_zero,
                     Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
                     Complex.add_im, Int.cast_sub, Int.cast_one]
          rw [hz]
          simp only [mul_re, sub_re, intCast_re, one_re, ofReal_re, sub_im, intCast_im, one_im,
            sub_self, ofReal_im, mul_zero, sub_zero, add_zero, zero_add]
          ring
      rw [heq, ← dist_eq_norm]
      calc dist w z < min (min δ₁ δ₂) β := hw
        _ ≤ min δ₁ δ₂ := min_le_left _ _
        _ ≤ δ₂ := min_le_right _ _


/-- The interior of the closed strip `ClosedStrip β` is the open strip `Strip β`. -/
lemma interior_closedStrip (_hβ : 0 < β) : interior (ClosedStrip β) = Strip β := by
  ext z
  simp only [Strip, ClosedStrip, mem_interior_iff_mem_nhds, mem_setOf_eq]
  constructor
  · intro h
    -- If z is in interior, there's an ε-ball around z in ClosedStrip
    rw [Metric.mem_nhds_iff] at h
    obtain ⟨ε, hε_pos, hball⟩ := h
    constructor
    · -- 0 < z.im
      by_contra hle
      push Not at hle
      -- Consider z - (ε/2)*I, which is in the ball but has im < 0
      have hmem_ball : z - (ε/2) * I ∈ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        simp only [sub_sub_cancel_left, norm_neg, norm_mul, norm_I, mul_one]
        have h1 : ‖(ε : ℂ) / 2‖ = ε / 2 := by
          rw [norm_div, Complex.norm_real]
          simp only [Real.norm_eq_abs, norm_ofNat]
          rw [abs_of_pos hε_pos]
        rw [h1]
        linarith
      have hmem := hball hmem_ball
      simp only [mem_setOf_eq, sub_im, mul_im, div_ofNat_re, ofReal_re, I_im, mul_one, div_ofNat_im,
        ofReal_im, zero_div, I_re, mul_zero, add_zero, tsub_le_iff_right] at hmem
      linarith
    · -- z.im < β
      by_contra hge
      push Not at hge
      have hmem_ball : z + (ε/2) * I ∈ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : z + ε / 2 * I - z = (ε / 2 : ℝ) * I := by simp only [add_sub_cancel_left,
          ofReal_div, ofReal_ofNat]
        rw [hsub, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
        rw [Real.norm_eq_abs, abs_of_pos (half_pos hε_pos)]
        linarith
      have hmem := hball hmem_ball
      simp only [mem_setOf_eq, add_im, mul_im, div_ofNat_re, ofReal_re, I_im, mul_one, div_ofNat_im,
        ofReal_im, zero_div, I_re, mul_zero, add_zero] at hmem
      linarith
  · intro ⟨h1, h2⟩
    -- z is in open strip, show it's in interior of closed strip
    rw [Metric.mem_nhds_iff]
    use min z.im (β - z.im)
    refine ⟨lt_min h1 (by linarith), ?_⟩
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    simp only [mem_setOf_eq]
    have him : |w.im - z.im| < min z.im (β - z.im) := by
      calc |w.im - z.im| = |(w - z).im| := by simp only [sub_im]
        _ ≤ ‖w - z‖ := abs_im_le_norm (w - z)
        _ < min z.im (β - z.im) := hw
    constructor
    · have := (abs_lt.mp him).1
      linarith [min_le_left z.im (β - z.im)]
    · have := (abs_lt.mp him).2
      linarith [min_le_right z.im (β - z.im)]

end Spectra.PeriodicHolomorphic

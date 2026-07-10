/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.PeriodicStrip.IndexProps

/-!
# Continuity, holomorphicity, and boundedness of the periodic extension

This file establishes the analytic properties of `periodicExtension F β` (the ℤ-periodic-in-`iβ`
extension of a strip function `F`, defined via `toFundamentalStrip`) that feed into the entirety
theorem of `PeriodicStrip/Basic.lean`:

* `periodicExtension_continuous`: continuity everywhere, including at the boundary seams
  `Im z = n·β`, where the periodicity hypothesis `F(t) = F(t + iβ)` glues the two sides together.
* `periodicExtension_differentiableAt_off_boundaries`: holomorphicity at every point off the
  boundary lattice, by local agreement with `F` composed with a translation.
* `periodicExtension_bounded`, `periodicExtension_eq_on_strip`: boundedness of the extension, and
  agreement with `F` on the closed fundamental strip.

Two topological facts about the off-boundary set (`isOpen_off_boundaryLines`,
`dense_off_boundaryLines`) are recorded but currently unused.

## Main results

* `periodicExtension_continuous`
* `periodicExtension_differentiableAt_off_boundaries`
* `periodicExtension_bounded`
* `periodicExtension_eq_on_strip`
-/

open Complex Set Filter Topology Int MeasureTheory
namespace Spectra.PeriodicHolomorphic

variable {β : ℝ}

/-- The periodic extension is continuous everywhere -/
lemma periodicExtension_continuous
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hcont : ContinuousOn F (ClosedStrip β))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t)) :
    Continuous (periodicExtension F β) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases h : z.im ∈ Set.range (fun n : ℤ => (n : ℝ) * β)
  · -- z is on a boundary line
    obtain ⟨n, hn⟩ := h
    exact periodicExtension_continuous_at_boundary F hβ hcont hperiod z n (id (Eq.symm hn))
  · -- z is in the interior of some strip, continuity follows from composition.
    -- Since z is NOT on a boundary, toFundamentalStrip β z is in the OPEN strip.
    have him_pos : 0 < (toFundamentalStrip β z).im := by
      obtain ⟨h1, _⟩ := toFundamentalStrip_im hβ z
      rcases h1.lt_or_eq with hlt | heq
      · exact hlt
      · -- heq : (toFundamentalStrip β z).im = 0 means z.im = n*β
        exfalso
        apply h
        refine ⟨stripIndex β z, ?_⟩
        simp only [toFundamentalStrip, sub_im, mul_im, mul_re, intCast_im, ofReal_im, mul_zero,
                  intCast_re, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, sub_zero] at heq
        linarith
    have him_lt : (toFundamentalStrip β z).im < β := (toFundamentalStrip_im hβ z).2
    -- toFundamentalStrip β z is in the open strip = interior of closed strip
    have h_in_interior : toFundamentalStrip β z ∈ interior (ClosedStrip β) := by
      rw [interior_closedStrip hβ]
      exact ⟨him_pos, him_lt⟩
    -- F is continuous at points in the interior
    have hF_cont : ContinuousAt F (toFundamentalStrip β z) :=
      hcont.continuousAt (mem_interior_iff_mem_nhds.mp h_in_interior)
    -- stripIndex is locally constant at z (since z is not on a boundary)
    -- Therefore toFundamentalStrip is continuous at z
    let n := stripIndex β z
    have hz_strict : (n : ℝ) * β < z.im ∧ z.im < (n + 1 : ℤ) * β := by
      obtain ⟨h1, h2⟩ := stripIndex_spec hβ z
      refine ⟨?_, h2⟩
      rcases h1.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; exact h ⟨n, heq⟩
    have hfund_cont : ContinuousAt (toFundamentalStrip β) z := by
      -- In a small neighborhood, stripIndex is constant
      let ε := min (z.im - n * β) ((↑(n + 1 : ℤ) : ℝ) * β - z.im)
      have hε_pos : 0 < ε := lt_min (by linarith) (by push_cast; grind only)
      rw [Metric.continuousAt_iff]
      intro δ hδ
      use min ε δ
      refine ⟨lt_min hε_pos hδ, ?_⟩
      intro w hw
      -- ⊢ dist (toFundamentalStrip β w) (toFundamentalStrip β z) < δ
      have him_dist : |w.im - z.im| < ε := calc
        |w.im - z.im| = |(w - z).im| := by simp only [sub_im]
        _ ≤ ‖w - z‖ := abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ < min ε δ := hw
        _ ≤ ε := min_le_left _ _
      -- stripIndex w = n
      have hw_strip : stripIndex β w = n := by
        simp only [stripIndex, Int.floor_eq_iff]
        have him_lower : w.im > z.im - ε := sub_lt_of_abs_sub_lt_left him_dist
        have him_upper : w.im < z.im + ε := by linarith [(abs_lt.mp him_dist).2]
        have hε_left : ε ≤ z.im - n * β := min_le_left _ _
        have hε_right : ε ≤ (n + 1 : ℤ) * β - z.im := min_le_right _ _
        -- Simplify the cast in hε_right
        simp only [Int.cast_add, Int.cast_one] at hε_right
        -- Now hε_right : ε ≤ (↑n + 1) * β - z.im
        constructor
        · rw [le_div_iff₀ hβ]
          -- Need: ↑n * β ≤ w.im
          linarith
        · rw [div_lt_iff₀ hβ]
          -- Need: w.im < (↑n + 1) * β
          linarith
      -- Now compute distance
      simp only [toFundamentalStrip, hw_strip, dist_eq_norm]
      -- Both use the same n, so the I terms cancel
      have : w - ↑n * ↑β * I - (z - ↑n * ↑β * I) = w - z := by ring
      rw [this, ← dist_eq_norm]
      calc dist w z < min ε δ := hw
        _ ≤ δ := min_le_right _ _
    exact hF_cont.comp hfund_cont

/-! ## Holomorphicity Away from Boundaries -/

/-- The periodic extension is holomorphic at points not on boundary lines -/
lemma periodicExtension_differentiableAt_off_boundaries
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (z : ℂ) (hz : z.im ∉ Set.range (fun n : ℤ => (n : ℝ) * β)) :
    DifferentiableAt ℂ (periodicExtension F β) z := by
  -- Same setup: toFundamentalStrip β z is in the OPEN strip
  have him_pos : 0 < (toFundamentalStrip β z).im := by
    obtain ⟨h1, _⟩ := toFundamentalStrip_im hβ z
    rcases h1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hz
      refine ⟨stripIndex β z, ?_⟩
      change ↑(stripIndex β z) * β = z.im
      simp only [toFundamentalStrip, sub_im, mul_im, mul_re, intCast_im, ofReal_im, mul_zero,
                intCast_re, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, sub_zero] at heq
      linarith
  have him_lt : (toFundamentalStrip β z).im < β := (toFundamentalStrip_im hβ z).2
  -- toFundamentalStrip β z ∈ Strip β
  have _h_in_strip : toFundamentalStrip β z ∈ Strip β := ⟨him_pos, him_lt⟩
  -- F is differentiable at points in the open strip
  have hF_diff : DifferentiableAt ℂ F (toFundamentalStrip β z) := by
    apply hholo.differentiableAt
    -- Need: Strip β ∈ 𝓝 (toFundamentalStrip β z)
    -- Strip β is open, so it suffices to show toFundamentalStrip β z ∈ Strip β
    rw [Metric.mem_nhds_iff]
    use min (toFundamentalStrip β z).im (β - (toFundamentalStrip β z).im)
    refine ⟨lt_min him_pos (by linarith), ?_⟩
    intro w hw
    rw [Metric.mem_ball] at hw
    simp only [Strip, mem_setOf_eq]
    have him_w : |w.im - (toFundamentalStrip β z).im|
        < min (toFundamentalStrip β z).im (β - (toFundamentalStrip β z).im) := by
      calc |w.im - (toFundamentalStrip β z).im|
          = |(w - toFundamentalStrip β z).im| := by simp only [sub_im]
        _ ≤ ‖w - toFundamentalStrip β z‖ := abs_im_le_norm _
        _ = dist w (toFundamentalStrip β z) := (dist_eq_norm _ _).symm
        _ < _ := hw
    constructor
    · have := (abs_lt.mp him_w).1
      linarith [min_le_left (toFundamentalStrip β z).im (β - (toFundamentalStrip β z).im)]
    · have := (abs_lt.mp him_w).2
      linarith [min_le_right (toFundamentalStrip β z).im (β - (toFundamentalStrip β z).im)]
  -- In a neighborhood of z, periodicExtension F β = F ∘ (· - n*β*I)
  -- where n = stripIndex β z
  let n := stripIndex β z
  -- stripIndex is constant near z
  have hz_strict : (n : ℝ) * β < z.im ∧ z.im < (n + 1 : ℤ) * β := by
    obtain ⟨h1, h2⟩ := stripIndex_spec hβ z
    refine ⟨?_, h2⟩
    rcases h1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; exact hz ⟨n, heq⟩
  let ε := min (z.im - n * β) ((↑(n + 1 : ℤ) : ℝ) * β - z.im)
  have hε_pos : 0 < ε := lt_min (by linarith) (by push_cast; grind only)
  -- On ball z ε, periodicExtension = F ∘ (· - n*β*I)
  have heq_on : ∀ w ∈ Metric.ball z ε, periodicExtension F β w = F (w - n * β * I) := by
    intro w hw
    simp only [periodicExtension, toFundamentalStrip]
    congr 1
    -- Show stripIndex β w = n
    rw [Metric.mem_ball] at hw
    have him_dist : |w.im - z.im| < ε := calc
      |w.im - z.im| = |(w - z).im| := by simp only [sub_im]
      _ ≤ ‖w - z‖ := abs_im_le_norm _
      _ = dist w z := (dist_eq_norm _ _).symm
      _ < ε := hw
    have hw_strip : stripIndex β w = n := by
      simp only [stripIndex, Int.floor_eq_iff]
      constructor
      · apply (le_div_iff₀ hβ).mpr
        have hε_left : ε ≤ z.im - n * β := min_le_left _ _
        linarith [(abs_lt.mp him_dist).1, hε_left]
      · apply (div_lt_iff₀ hβ).mpr
        have hε_right : ε ≤ (↑(n + 1 : ℤ) : ℝ) * β - z.im := min_le_right _ _
        simp only [Int.cast_add, Int.cast_one] at hε_right
        linarith [(abs_lt.mp him_dist).2, hε_right]
    simp [hw_strip]
  -- Translation w ↦ w - n*β*I is differentiable
  have htrans_diff : DifferentiableAt ℂ (fun w => w - n * β * I) z :=
    differentiableAt_id.sub (differentiableAt_const _)
  -- Use chain rule via the local equality
  have heq_eventually : periodicExtension F β =ᶠ[𝓝 z] fun w => F (w - n * β * I) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Metric.ball z ε, Metric.ball_mem_nhds z hε_pos, heq_on⟩
  -- F ∘ (translation) is differentiable at z
  have hdiff_comp : DifferentiableAt ℂ (fun w => F (w - n * β * I)) z :=
    DifferentiableAt.fun_comp' z hF_diff htrans_diff
  -- Transfer differentiability via local equality
  exact hdiff_comp.congr_of_eventuallyEq heq_eventually



/-! ## The Morera-Type Theorem

This is the key technical result: a continuous function that is holomorphic
except on a discrete set of horizontal lines is holomorphic everywhere.

The proof uses Morera's theorem: if ∫_γ f = 0 for all triangles γ, then f
is holomorphic. For a triangle crossing a boundary line, we approximate
by triangles that don't cross (using continuity) and use that holomorphic
functions have zero integral over closed curves.
-/

/-- The set of points NOT on any boundary line is open (Currently unused.) -/
lemma isOpen_off_boundaryLines (β : ℝ) (hβ : 0 < β) :
    IsOpen {z : ℂ | ∀ n : ℤ, z.im ≠ n * β} := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  -- z.im is not equal to any n * β
  -- Find the nearest boundary lines above and below z
  let n := ⌊z.im / β⌋
  have hn_below : (n : ℝ) * β < z.im := by
    have hne : z.im ≠ n * β := hz n
    have hle : (n : ℝ) * β ≤ z.im := by
      have := Int.floor_le (z.im / β)
      calc (n : ℝ) * β = ⌊z.im / β⌋ * β := rfl
        _ ≤ (z.im / β) * β := mul_le_mul_of_nonneg_right this (le_of_lt hβ)
        _ = z.im := by field_simp
    exact lt_of_le_of_ne hle (Ne.symm hne)
  have hn_above : z.im < (n + 1 : ℤ) * β := by
    have := Int.lt_floor_add_one (z.im / β)
    calc z.im = (z.im / β) * β := by field_simp
      _ < (⌊z.im / β⌋ + 1) * β := mul_lt_mul_of_pos_right this hβ
      _ = (n + 1 : ℤ) * β := by push_cast; rfl
  -- The distance to the nearest boundary
  let ε := min (z.im - n * β) ((↑(n + 1 : ℤ) : ℝ) * β - z.im)
  have hε_pos : 0 < ε := lt_min (by linarith) (by push_cast; grind only)
  refine ⟨Metric.ball z ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε_pos⟩
  intro w hw
  rw [Metric.mem_ball] at hw
  intro m
  have him : |w.im - z.im| < ε := calc
    |w.im - z.im| = |(w - z).im| := by simp only [sub_im]
    _ ≤ ‖w - z‖ := abs_im_le_norm _
    _ = dist w z := (dist_eq_norm _ _).symm
    _ < ε := hw
  -- w.im is strictly between n*β and (n+1)*β, so can't equal m*β for any m
  have hw_lower : (n : ℝ) * β < w.im := by
    have := (abs_lt.mp him).1
    have hε_left : ε ≤ z.im - n * β := min_le_left _ _
    linarith
  have hw_upper : w.im < (n + 1 : ℤ) * β := by
    have := (abs_lt.mp him).2
    have hε_right : ε ≤ (↑(n + 1 : ℤ) : ℝ) * β - z.im := min_le_right _ _
    simp only [Int.cast_add, Int.cast_one] at hε_right ⊢
    linarith
  -- So w.im ∈ (n*β, (n+1)*β), which means w.im ≠ m*β for any integer m
  intro heq
  -- From hw_lower: n * β < w.im = m * β, so n < m (since β > 0)
  have hn_lt_m : n < m := by
    have _h : (n : ℝ) * β < (m : ℝ) * β := by rw [← heq]; exact hw_lower
    exact_mod_cast show (n : ℝ) < (m : ℝ) by nlinarith
  -- From hw_upper: w.im = m * β < (n + 1) * β, so m < n + 1
  have hm_lt : m < n + 1 := by
    have _h1 : (m : ℝ) * β < (↑(n + 1 : ℤ) : ℝ) * β := by rw [heq.symm]; exact hw_upper
    exact_mod_cast show (m : ℝ) < (↑(n + 1 : ℤ) : ℝ) by nlinarith
  -- n < m and m < n + 1 is impossible for integers
  linarith


/-- The set of points NOT on any boundary line is dense (Currently unused.) -/
lemma dense_off_boundaryLines (β : ℝ) (hβ : 0 < β) :
    Dense {z : ℂ | ∀ n : ℤ, z.im ≠ n * β} := by
  rw [dense_iff_inter_open]
  intro U hU ⟨z₀, hz₀⟩
  -- U is open, so there's a ball around z₀
  rw [Metric.isOpen_iff] at hU
  obtain ⟨r, hr_pos, hball⟩ := hU z₀ hz₀
  -- We'll find a point in U that's not on any boundary line
  by_cases h : ∀ n : ℤ, z₀.im ≠ n * β
  · exact ⟨z₀, hz₀, h⟩
  · -- z₀ is on some line, so perturb it
    push Not at h
    obtain ⟨n, hn⟩ := h
    -- Consider z₀ + δ*I where δ is small and irrational multiple of β
    -- Simpler: just pick δ = min(r/2, β/2)
    let δ := min (r / 2) (β / 2)
    have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδ_lt_r : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ_lt_β : δ < β := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    let w := z₀ + δ * I
    refine ⟨w, hball ?_, ?_⟩
    · -- w ∈ ball z₀ r
      change dist (z₀ + δ * I) z₀ < r
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      exact hδ_lt_r
    · -- w is not on any boundary line
      intro m
      change (z₀ + δ * I).im ≠ ↑m * β
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      rw [hn]
      -- Need: n * β + δ ≠ (m : ℝ) * β, i.e., δ ≠ (m - n) * β
      intro heq
      have hδ_eq : δ = (m - n) * β := by linarith
      -- δ > 0 and δ < β, so 0 < (m - n) * β < β
      -- This means 0 < m - n < 1 (after dividing by β > 0)
      -- But m - n is an integer, so no such integer exists
      have h1 : 0 < (m - n : ℤ) := by
        have : 0 < (m - n : ℝ) * β := by rw [← hδ_eq]; exact hδ_pos
        have := (mul_pos_iff_of_pos_right hβ).mp this
        simp only [sub_pos, cast_lt] at this
        simp only [Int.sub_pos, gt_iff_lt]
        exact this
      have h2 : (m - n : ℤ) < 1 := by
        have hkey : (↑(m - n) : ℝ) * β < β := by
          simp only [cast_sub]
          rw [← hδ_eq]; exact hδ_lt_β
        have hkey2 : (↑(m - n) : ℝ) < 1 := by
          have := (mul_lt_iff_lt_one_left hβ).mp hkey
          exact this
        exact_mod_cast hkey2
      linarith

/- **Morera's Theorem for functions holomorphic off horizontal lines**

If f : ℂ → ℂ is continuous and holomorphic except on horizontal lines at heights n*β,
then f is entire (holomorphic everywhere).

Proof: At any point z₀ (even on a boundary line), define the Cauchy integral
  g(z) = (2πi)⁻¹ ∮_{|ζ-z₀|=r} f(ζ)/(ζ-z) dζ
on a small disk. Then:
1. g is holomorphic on the disk (standard)
2. g = f on the open dense set where f is holomorphic (Cauchy formula)
3. Both are continuous, so g = f everywhere on the disk
4. Therefore f is holomorphic at z₀
-/

/-! ## The Main Extension Theorem

The entirety of the periodic extension (`periodicExtension_entire`) is proved in
`PeriodicStrip/Basic.lean`, where the local Painlevé line-removal theorem from
`PeriodicStrip/LineRemove.lean` is available to combine with the continuity and
off-boundary holomorphicity established here.
-/

/-- The periodic extension is bounded -/
lemma periodicExtension_bounded
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β))) :
    Bornology.IsBounded (Set.range (periodicExtension F β)) := by
  -- Get the bound M
  obtain ⟨M, hM⟩ := hbdd
  -- Show the range is contained in the closed ball of radius M centered at 0
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨M, ?_⟩
  -- Take any w in the range
  intro w hw
  simp only [Metric.mem_closedBall]
  -- w = periodicExtension F β z for some z
  obtain ⟨z, rfl⟩ := hw
  simp only [periodicExtension]
  -- Need: ‖F (toFundamentalStrip β z)‖ ≤ M
  -- This follows because toFundamentalStrip β z ∈ ClosedStrip β
  apply hM
  -- Show ‖F (toFundamentalStrip β z)‖ ∈ norm '' (F '' ClosedStrip β)
  simp only [Set.mem_image]
  -- ⊢ ∃ x, (∃ x_1 ∈ ClosedStrip β, F x_1 = x) ∧ ‖x‖ = dist (F (toFundamentalStrip β z)) 0
  exact ⟨F (toFundamentalStrip β z),
         ⟨toFundamentalStrip β z, toFundamentalStrip_mem_closedStrip hβ z, rfl⟩,
         (dist_zero_right _).symm⟩

/-- The periodic extension agrees with F on the closed strip -/
lemma periodicExtension_eq_on_strip
    (F : ℂ → ℂ) (hβ : 0 < β)
    (_hcont : ContinuousOn F (ClosedStrip β))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t))
    {z : ℂ} (hz : z ∈ ClosedStrip β) :
    periodicExtension F β z = F z := by
  simp only [periodicExtension]
  simp only [ClosedStrip, mem_setOf_eq] at hz
  by_cases h : z.im < β
  · -- z is in [0, β), so stripIndex is 0
    have : toFundamentalStrip β z = z :=
      toFundamentalStrip_of_mem_strip hβ ⟨hz.1, h⟩
    rw [this]
  · -- z.im = β (on the upper boundary)
    push Not at h
    have hzβ : z.im = β := le_antisymm hz.2 h
    -- At the upper boundary, we need to use the periodic condition
    -- stripIndex will be 1, so we shift down by β
    have hstrip : stripIndex β z = 1 := by
      simp only [stripIndex]
      rw [Int.floor_eq_iff]
      constructor
      · simp only [Int.cast_one]; exact (one_le_div₀ hβ).mpr h
      · have : z.im / β = 1 := by rw [hzβ]; exact div_self (ne_of_gt hβ)
        simp only [this, Int.cast_one]
        norm_num
    simp only [toFundamentalStrip, hstrip]
    simp only [Int.cast_one]
    -- Now toFundamentalStrip β z = z - 1 * β * I (with 1 : ℂ); this point sits on
    -- the lower boundary, and periodicity carries F across.
    have hz_shifted : z - (1 : ℂ) * β * I = realToLower z.re := by
      simp only [realToLower]
      rw [Complex.ext_iff]
      constructor
      · simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re]
      · simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, hzβ]
    rw [hz_shifted]
    -- And z = realToUpper β z.re
    have hz_upper : z = realToUpper β z.re := by
      rw [Complex.ext_iff]
      constructor
      · simp [realToUpper]
      · simp [realToUpper, hzβ]
    rw [hz_upper]
    -- Simplify: (realToUpper β z.re).re = z.re
    have h_re : (realToUpper β z.re).re = z.re := by
      simp [realToUpper]
    simp only [h_re]
    -- Now goal is: F (realToLower z.re) = F (realToUpper β z.re)
    exact (hperiod z.re)

end Spectra.PeriodicHolomorphic

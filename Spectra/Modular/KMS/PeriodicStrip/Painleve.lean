/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Spectra.Modular.KMS.PeriodicStrip.Defs

/-!
# Cauchy–Goursat with one horizontal line excluded

This file supplies the geometric and integral-theoretic groundwork for the local Painlevé
line-removal theorem completed in `PeriodicStrip/LineRemove.lean`.

* `integral_boundary_rect_eq_zero_off_horizLine`: Cauchy–Goursat for a rectangle that may straddle
  one horizontal singular line `{Im = a}` — proved by splitting the rectangle at height `a` and
  gluing two applications of Mathlib's standard Cauchy–Goursat theorem.
* `rect_in_ball_of_corners_in_ball`, `horiz_seg_in_ball`, `vert_seg_in_ball`: elementary geometric
  facts placing rectangles and axis-aligned segments inside a ball from their corner/endpoint
  memberships.
* `F_eq_F₁`, `F_diff_eq_Lpath`: path-independence of the "L-shaped" primitive candidate built from
  the rectangle identity above, expressing a difference `F(z + h) - F(z)` as a single L-path
  integral.

Together with the vanishing rectangle integrals, `F_diff_eq_Lpath` is exactly what
`LineRemove.lean`'s `exists_primitive_of_continuousOn_of_rect_integral_zero` needs to construct a
primitive `F` with `F' = g` on the ball, which that file then upgrades to the full local Painlevé
theorem (`differentiableOn_of_continuousOn_of_differentiableOn_off_horizLine`).

## Main results

* `integral_boundary_rect_eq_zero_off_horizLine`
* `F_diff_eq_Lpath`
-/

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Topology

namespace Spectra.PeriodicHolomorphic

/-- **Cauchy–Goursat across a horizontal line.**

If `f` is continuous on a closed rectangle and complex-differentiable on the open
rectangle minus a single horizontal line `{ζ | ζ.im = a}`, then the integral of
`f` along the boundary of the rectangle vanishes. The line is allowed to cross
the open rectangle; the proof splits at height `a` and applies Mathlib's standard
Cauchy–Goursat to the two sub-rectangles. -/
lemma integral_boundary_rect_eq_zero_off_horizLine
    {a : ℝ} (f : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : DifferentiableOn ℂ f
            ((Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
              Set.Ioo (min z.im w.im) (max z.im w.im)) \ {ζ | ζ.im = a})) :
    (((∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * I)) -
       ∫ (x : ℝ) in z.re..w.re, f (↑x + ↑w.im * I)) +
     I • ∫ (y : ℝ) in z.im..w.im, f (↑w.re + ↑y * I)) -
     I • ∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * I) = 0 := by
  by_cases ha : a ∈ Set.Ioo (min z.im w.im) (max z.im w.im)
  · -- Hard case: line crosses the open rectangle.  Split at height `a`.
    -- Closed/open im-interval inclusions induced by `a` lying inside `(min, max)`.
    have ha_uIcc : a ∈ Set.uIcc z.im w.im := Set.Ioo_subset_Icc_self ha
    have low_uIcc : Set.uIcc z.im a ⊆ Set.uIcc z.im w.im :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc ha_uIcc
    have up_uIcc : Set.uIcc a w.im ⊆ Set.uIcc z.im w.im :=
      Set.uIcc_subset_uIcc ha_uIcc Set.right_mem_uIcc
    have low_Ioo : Set.Ioo (min z.im a) (max z.im a) ⊆
                   Set.Ioo (min z.im w.im) (max z.im w.im) :=
      Set.Ioo_subset_Ioo
        (le_min (min_le_left _ _) ha.1.le)
        (max_le (le_max_left _ _) ha.2.le)
    have up_Ioo : Set.Ioo (min a w.im) (max a w.im) ⊆
                  Set.Ioo (min z.im w.im) (max z.im w.im) :=
      Set.Ioo_subset_Ioo
        (le_min ha.1.le (min_le_right _ _))
        (max_le ha.2.le (le_max_right _ _))
    -- The line `Im = a` sits on the boundary of each open sub-rectangle, not inside.
    have a_not_low : a ∉ Set.Ioo (min z.im a) (max z.im a) := by
      intro h
      rcases le_or_gt z.im a with hza | hza
      · exact absurd h.2 (by rw [max_eq_right hza]; exact lt_irrefl _)
      · exact absurd h.1 (by rw [min_eq_right hza.le]; exact lt_irrefl _)
    have a_not_up : a ∉ Set.Ioo (min a w.im) (max a w.im) := by
      intro h
      rcases le_or_gt a w.im with haw | haw
      · exact absurd h.1 (by rw [min_eq_left haw]; exact lt_irrefl _)
      · exact absurd h.2 (by rw [max_eq_left haw.le]; exact lt_irrefl _)
    -- The two new corners, with their real/imaginary parts. Named via `set` — each corner
    -- literal recurs 4 times below (both `ContinuousOn`/`DifferentiableOn` hypotheses and the
    -- Cauchy–Goursat application); writing it out repeatedly forced Lean to re-unfold
    -- `Complex.re`/`.im` on the same constructed complex number from scratch each time
    -- (measured ~2s per occurrence-cluster; see the compile-time case study).
    set cornerW : ℂ := (↑w.re + ↑a * I : ℂ) with hcornerW
    set cornerZ : ℂ := (↑z.re + ↑a * I : ℂ) with hcornerZ
    have hcre : cornerW.re = w.re := by rw [hcornerW]; simp
    have hcim : cornerW.im = a := by rw [hcornerW]; simp
    have hdre : cornerZ.re = z.re := by rw [hcornerZ]; simp
    have hdim : cornerZ.im = a := by rw [hcornerZ]; simp
    -- Continuity of `f` on each closed sub-rectangle, inherited from `Hc`.
    have Hc_low : ContinuousOn f
        (Set.uIcc z.re cornerW.re ×ℂ Set.uIcc z.im cornerW.im) := by
      rw [hcre, hcim]
      refine Hc.mono fun ζ hζ => ⟨hζ.1, low_uIcc hζ.2⟩
    have Hc_up : ContinuousOn f
        (Set.uIcc cornerZ.re w.re ×ℂ Set.uIcc cornerZ.im w.im) := by
      rw [hdre, hdim]
      refine Hc.mono fun ζ hζ => ⟨hζ.1, up_uIcc hζ.2⟩
    -- Differentiability of `f` on each open sub-rectangle.  The open sub-rectangle
    -- is a subset of the open big rectangle and avoids the line.
    have Hd_low : DifferentiableOn ℂ f
        (Set.Ioo (min z.re cornerW.re) (max z.re cornerW.re) ×ℂ
         Set.Ioo (min z.im cornerW.im) (max z.im cornerW.im)) := by
      rw [hcre, hcim]
      refine Hd.mono fun ζ hζ => ⟨⟨hζ.1, low_Ioo hζ.2⟩, ?_⟩
      intro hζa
      simp only [Set.mem_setOf_eq] at hζa
      exact a_not_low (hζa ▸ hζ.2)
    have Hd_up : DifferentiableOn ℂ f
        (Set.Ioo (min cornerZ.re w.re) (max cornerZ.re w.re) ×ℂ
         Set.Ioo (min cornerZ.im w.im) (max cornerZ.im w.im)) := by
      rw [hdre, hdim]
      refine Hd.mono fun ζ hζ => ⟨⟨hζ.1, up_Ioo hζ.2⟩, ?_⟩
      intro hζa
      simp only [Set.mem_setOf_eq] at hζa
      exact a_not_up (hζa ▸ hζ.2)
    -- Apply Mathlib's Cauchy–Goursat on each sub-rectangle.
    have low_zero :=
      Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        f z cornerW Hc_low Hd_low
    have up_zero :=
      Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
        f cornerZ w Hc_up Hd_up
    -- Substitute the corner coordinates.
    simp only [hcre, hcim, hdre, hdim] at low_zero up_zero
    -- Continuity of the horizontal-edge integrands along the closed im-interval.
    have cont_w : ContinuousOn (fun y : ℝ => f (↑w.re + ↑y * I)) (Set.uIcc z.im w.im) := by
      refine Hc.comp (by fun_prop) (fun y hy => ⟨?_, ?_⟩)
      · simp only [mem_preimage, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, right_mem_uIcc]
      · simpa using hy
    have cont_z : ContinuousOn (fun y : ℝ => f (↑z.re + ↑y * I)) (Set.uIcc z.im w.im) := by
      refine Hc.comp (by fun_prop) (fun y hy => ⟨?_, ?_⟩)
      · simp only [mem_preimage, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, left_mem_uIcc]
      · simpa using hy
    -- Glue the lower and upper horizontal integrals.
    have hint_w :
        (∫ y in z.im..a, f (↑w.re + ↑y * I)) + (∫ y in a..w.im, f (↑w.re + ↑y * I)) =
        (∫ y in z.im..w.im, f (↑w.re + ↑y * I)) :=
      intervalIntegral.integral_add_adjacent_intervals
        (cont_w.mono low_uIcc).intervalIntegrable
        (cont_w.mono up_uIcc).intervalIntegrable
    have hint_z :
        (∫ y in z.im..a, f (↑z.re + ↑y * I)) + (∫ y in a..w.im, f (↑z.re + ↑y * I)) =
        (∫ y in z.im..w.im, f (↑z.re + ↑y * I)) :=
      intervalIntegral.integral_add_adjacent_intervals
        (cont_z.mono low_uIcc).intervalIntegrable
        (cont_z.mono up_uIcc).intervalIntegrable
    -- After rewriting `B_low + B_up` for both sides, the sum of `low_zero` and
    -- `up_zero` is exactly the desired boundary integral (the middle `Am` terms cancel).
    rw [← hint_w, ← hint_z]
    have hsm : ∀ x : ℂ, (I : ℂ) • x = I * x := fun _ => rfl
    simp_rw [smul_add, hsm] at low_zero up_zero ⊢
    grind => ring
  · -- Easy case: the line does not meet the open rectangle.  Apply Mathlib directly.
    apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w Hc
    refine Hd.mono fun ζ hζ => ⟨hζ, ?_⟩
    intro hζa
    simp only [Set.mem_setOf_eq] at hζa
    exact ha (hζa ▸ hζ.2)


/-- A real number in `Set.uIcc a b` has squared deviation from any `k` bounded by
the maximum of `(a - k)^2` and `(b - k)^2`. Convexity of `x ↦ (x - k)^2` packaged
as a bound at the endpoints of the interval. -/
private lemma sq_sub_le_max_sq_of_mem_uIcc {a b k x : ℝ} (hx : x ∈ Set.uIcc a b) :
    (x - k)^2 ≤ max ((a - k)^2) ((b - k)^2) := by
  obtain ⟨h_lo, h_hi⟩ := hx
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab] at h_lo
    rw [max_eq_right hab] at h_hi
    rcases le_total k a with hka | hka
    · exact ((by nlinarith : (x - k)^2 ≤ (b - k)^2)).trans (le_max_right _ _)
    · rcases le_total k b with hkb | hkb
      · rcases le_total x k with hxk | hxk
        · exact ((by nlinarith : (x - k)^2 ≤ (a - k)^2)).trans (le_max_left _ _)
        · exact ((by nlinarith : (x - k)^2 ≤ (b - k)^2)).trans (le_max_right _ _)
      · exact ((by nlinarith : (x - k)^2 ≤ (a - k)^2)).trans (le_max_left _ _)
  · rw [min_eq_right hab] at h_lo
    rw [max_eq_left hab] at h_hi
    rcases le_total k b with hkb | hkb
    · exact ((by nlinarith : (x - k)^2 ≤ (a - k)^2)).trans (le_max_left _ _)
    · rcases le_total k a with hka | hka
      · rcases le_total x k with hxk | hxk
        · exact ((by nlinarith : (x - k)^2 ≤ (b - k)^2)).trans (le_max_right _ _)
        · exact ((by nlinarith : (x - k)^2 ≤ (a - k)^2)).trans (le_max_left _ _)
      · exact ((by nlinarith : (x - k)^2 ≤ (b - k)^2)).trans (le_max_right _ _)

/-- A closed axis-aligned rectangle whose four corners lie in an open ball is
contained in the ball. (Stated for the two-diagonal-corner presentation that the
Painlevé proof actually consumes — the two off-diagonal corners are passed
explicitly so we avoid an ad-hoc convex-hull argument.) -/
lemma rect_in_ball_of_corners_in_ball {c : ℂ} {R : ℝ} {z w : ℂ} (hR : 0 < R)
    (hz : z ∈ Metric.ball c R)
    (hw : w ∈ Metric.ball c R)
    (hzw : (↑z.re + ↑w.im * I : ℂ) ∈ Metric.ball c R)
    (hwz : (↑w.re + ↑z.im * I : ℂ) ∈ Metric.ball c R) :
    Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ Metric.ball c R := by
  -- Squared norm in coordinates.
  have norm_sq_eq : ∀ q : ℂ, ‖q - c‖^2 = (q.re - c.re)^2 + (q.im - c.im)^2 := fun q => by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  -- Reduce ball membership to a squared inequality.
  have to_sq : ∀ q : ℂ, q ∈ Metric.ball c R → ‖q - c‖^2 < R^2 := fun q hq => by
    rw [Metric.mem_ball, dist_eq_norm] at hq
    exact sq_lt_sq' (by linarith [norm_nonneg (q - c)]) hq
  -- Squared inequalities at each of the four corners.
  have hz'  : (z.re - c.re)^2 + (z.im - c.im)^2 < R^2 := by
    have := to_sq z hz; rwa [norm_sq_eq] at this
  have hw'  : (w.re - c.re)^2 + (w.im - c.im)^2 < R^2 := by
    have := to_sq w hw; rwa [norm_sq_eq] at this
  have hzw' : (z.re - c.re)^2 + (w.im - c.im)^2 < R^2 := by
    have h := to_sq _ hzw
    rw [norm_sq_eq] at h
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
               Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
               mul_zero, mul_one, sub_zero, add_zero, zero_add] at h
    exact h
  have hwz' : (w.re - c.re)^2 + (z.im - c.im)^2 < R^2 := by
    have h := to_sq _ hwz
    rw [norm_sq_eq] at h
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
               Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
               mul_zero, mul_one, sub_zero, add_zero, zero_add] at h
    exact h
  -- Main argument.
  intro p ⟨hp_re, hp_im⟩
  have bound_re := sq_sub_le_max_sq_of_mem_uIcc (k := c.re) hp_re
  have bound_im := sq_sub_le_max_sq_of_mem_uIcc (k := c.im) hp_im
  rw [Metric.mem_ball, dist_eq_norm]
  suffices h : (p.re - c.re)^2 + (p.im - c.im)^2 < R^2 by
    have h1 : ‖p - c‖^2 < R^2 := by rw [norm_sq_eq]; exact h
    exact lt_of_pow_lt_pow_left₀ 2 hR.le h1
  -- Case-split on which corner provides each coordinate's max.
  rcases le_total ((z.re - c.re)^2) ((w.re - c.re)^2) with hre | hre <;>
    rcases le_total ((z.im - c.im)^2) ((w.im - c.im)^2) with him | him
  · rw [max_eq_right hre] at bound_re
    rw [max_eq_right him] at bound_im
    linarith
  · rw [max_eq_right hre] at bound_re
    rw [max_eq_left  him] at bound_im
    linarith
  · rw [max_eq_left  hre] at bound_re
    rw [max_eq_right him] at bound_im
    linarith
  · rw [max_eq_left  hre] at bound_re
    rw [max_eq_left  him] at bound_im
    linarith


/-- **Path independence at one point.** The vertical-first L-path primitive
agrees with the horizontal-first L-path primitive on the ball — both compute
the same value because the rectangle bounded by `c` and the point lies in the
ball, where the boundary integral vanishes. -/
lemma F_eq_F₁ {c : ℂ} {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ)
    (hg_rect : ∀ z w : ℂ,
        Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ Metric.ball c R →
        (((∫ x in z.re..w.re, g (↑x + ↑z.im * I)) -
           ∫ x in z.re..w.re, g (↑x + ↑w.im * I)) +
         I • ∫ y in z.im..w.im, g (↑w.re + ↑y * I)) -
         I • ∫ y in z.im..w.im, g (↑z.re + ↑y * I) = 0) :
    ∀ w ∈ Metric.ball c R,
      I • (∫ s in c.im..w.im, g (↑c.re + ↑s * I)) +
            ∫ t in c.re..w.re, g (↑t + ↑w.im * I)
      = (∫ t in c.re..w.re, g (↑t + ↑c.im * I)) +
            I • ∫ s in c.im..w.im, g (↑w.re + ↑s * I) := by
  intro w hw
  -- Distance and coordinate bounds.
  have h_w_norm : ‖w - c‖ < R := by rwa [← dist_eq_norm, ← Metric.mem_ball]
  have h_im_bd : |w.im - c.im| < R := by
    have h := Complex.abs_im_le_norm (w - c)
    rw [Complex.sub_im] at h
    linarith
  have h_re_bd : |w.re - c.re| < R := by
    have h := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re] at h
    linarith
  -- The two off-diagonal corners lie in the ball.
  have h_cw : (↑c.re + ↑w.im * I : ℂ) ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (↑c.re + ↑w.im * I : ℂ) - c = ((w.im - c.im : ℝ) : ℂ) * I := by
      rw [show c = (↑c.re : ℂ) + ↑c.im * I from (Complex.re_add_im c).symm]
      push_cast; ring_nf; simp only [re_add_im]; grind only
    rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact h_im_bd
  have h_wc : (↑w.re + ↑c.im * I : ℂ) ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (↑w.re + ↑c.im * I : ℂ) - c = ((w.re - c.re : ℝ) : ℂ) := by
      rw [show c = (↑c.re : ℂ) + ↑c.im * I from (Complex.re_add_im c).symm]
      push_cast; ring_nf; simp only [re_add_im]; grind only
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact h_re_bd
  -- The closed rectangle from c to w is in the ball — apply rect_in_ball.
  have h_rect := rect_in_ball_of_corners_in_ball hR
                    (Metric.mem_ball_self hR) hw h_cw h_wc
  -- Invoke the rectangle hypothesis on (c, w) and rearrange.
  have h_eq := hg_rect c w h_rect
  have hsm : ∀ x : ℂ, (I : ℂ) • x = I * x := fun _ => rfl
  simp_rw [hsm] at h_eq ⊢
  grind => ring


/-- A horizontal segment whose endpoints lie in an open ball stays in the ball.
Degenerate rectangle special case of `rect_in_ball_of_corners_in_ball`. -/
lemma horiz_seg_in_ball {c : ℂ} {R : ℝ} (hR : 0 < R) {x₁ x₂ y : ℝ}
    (h₁ : (↑x₁ + ↑y * I : ℂ) ∈ Metric.ball c R)
    (h₂ : (↑x₂ + ↑y * I : ℂ) ∈ Metric.ball c R) :
    ∀ t ∈ Set.uIcc x₁ x₂, (↑t + ↑y * I : ℂ) ∈ Metric.ball c R := by
  intro t ht
  have h_off : ∀ a b : ℝ, (↑a + ↑y * I : ℂ) ∈ Metric.ball c R →
      (↑(↑a + ↑y * I : ℂ).re + ↑(↑b + ↑y * I : ℂ).im * I : ℂ) ∈ Metric.ball c R := by
    intro a b ha
    have : (↑(↑a + ↑y * I : ℂ).re + ↑(↑b + ↑y * I : ℂ).im * I : ℂ) = ↑a + ↑y * I := by
      simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [this]; exact ha
  have h_rect := rect_in_ball_of_corners_in_ball hR h₁ h₂ (h_off x₁ x₂ h₁) (h_off x₂ x₁ h₂)
  apply h_rect
  refine ⟨?_, ?_⟩
  · change (↑t + ↑y * I : ℂ).re ∈ Set.uIcc (↑x₁ + ↑y * I : ℂ).re (↑x₂ + ↑y * I : ℂ).re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
               Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact ht
  · change (↑t + ↑y * I : ℂ).im ∈ Set.uIcc (↑x₁ + ↑y * I : ℂ).im (↑x₂ + ↑y * I : ℂ).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
               Complex.ofReal_re, mul_one, zero_mul, add_zero, zero_add]
    exact Set.left_mem_uIcc

/-- A vertical segment whose endpoints lie in an open ball stays in the ball. -/
lemma vert_seg_in_ball {c : ℂ} {R : ℝ} (hR : 0 < R) {x y₁ y₂ : ℝ}
    (h₁ : (↑x + ↑y₁ * I : ℂ) ∈ Metric.ball c R)
    (h₂ : (↑x + ↑y₂ * I : ℂ) ∈ Metric.ball c R) :
    ∀ s ∈ Set.uIcc y₁ y₂, (↑x + ↑s * I : ℂ) ∈ Metric.ball c R := by
  intro s hs
  -- z := ↑x + ↑y₁ * I, w := ↑x + ↑y₂ * I.
  -- z.re = x = w.re, so off-diagonals are ↑x + ↑y₂*I = w and ↑x + ↑y₁*I = z.
  have h_off1 : (↑(↑x + ↑y₁ * I : ℂ).re + ↑(↑x + ↑y₂ * I : ℂ).im * I : ℂ) ∈ Metric.ball c R := by
    have : (↑(↑x + ↑y₁ * I : ℂ).re + ↑(↑x + ↑y₂ * I : ℂ).im * I : ℂ) = ↑x + ↑y₂ * I := by
      simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [this]; exact h₂
  have h_off2 : (↑(↑x + ↑y₂ * I : ℂ).re + ↑(↑x + ↑y₁ * I : ℂ).im * I : ℂ) ∈ Metric.ball c R := by
    have : (↑(↑x + ↑y₂ * I : ℂ).re + ↑(↑x + ↑y₁ * I : ℂ).im * I : ℂ) = ↑x + ↑y₁ * I := by
      simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [this]; exact h₁
  have h_rect := rect_in_ball_of_corners_in_ball hR h₁ h₂ h_off1 h_off2
  apply h_rect
  refine ⟨?_, ?_⟩
  · change (↑x + ↑s * I : ℂ).re ∈ Set.uIcc (↑x + ↑y₁ * I : ℂ).re (↑x + ↑y₂ * I : ℂ).re
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
               Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact Set.left_mem_uIcc
  · change (↑x + ↑s * I : ℂ).im ∈ Set.uIcc (↑x + ↑y₁ * I : ℂ).im (↑x + ↑y₂ * I : ℂ).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
               Complex.ofReal_re, mul_one, zero_mul, add_zero, zero_add]
    exact hs

/-- **Local difference identity.** For `z, z + h.re, z + h` all in the ball, the
difference `F(z + h) − F(z)` (with `F` the vertical-first L-path primitive `F₂`)
equals the L-path integral from `z` to `z + h` taken horizontal at `z.im` then
vertical at `z.re + h.re`. -/
lemma F_diff_eq_Lpath {c : ℂ} {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ)
    (hg_cont : ContinuousOn g (Metric.ball c R))
    (hg_rect : ∀ z w : ℂ,
        Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ Metric.ball c R →
        (((∫ x in z.re..w.re, g (↑x + ↑z.im * I)) -
           ∫ x in z.re..w.re, g (↑x + ↑w.im * I)) +
         I • ∫ y in z.im..w.im, g (↑w.re + ↑y * I)) -
         I • ∫ y in z.im..w.im, g (↑z.re + ↑y * I) = 0)
    {z h : ℂ}
    (hz : z ∈ Metric.ball c R)
    (hzhr : z + ↑h.re ∈ Metric.ball c R)
    (hzh : z + h ∈ Metric.ball c R) :
    (I • (∫ s in c.im..(z.im + h.im), g (↑c.re + ↑s * I)) +
        ∫ t in c.re..(z.re + h.re), g (↑t + ↑(z.im + h.im) * I))
    - (I • (∫ s in c.im..z.im, g (↑c.re + ↑s * I)) +
        ∫ t in c.re..z.re, g (↑t + ↑z.im * I))
    = (∫ t in z.re..(z.re + h.re), g (↑t + ↑z.im * I)) +
      I • ∫ s in z.im..(z.im + h.im), g (↑(z.re + h.re) + ↑s * I) := by
  -- Norm bounds.
  have h_z_norm  : ‖z - c‖     < R := by rwa [← dist_eq_norm, ← Metric.mem_ball]
  have h_zh_norm : ‖z + h - c‖ < R := by rwa [← dist_eq_norm, ← Metric.mem_ball]
  -- Two off-diagonal corners we'll need for the segment helpers.
  have h_corn_a : (↑c.re + ↑z.im * I : ℂ) ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (↑c.re + ↑z.im * I : ℂ) - c = ((z.im - c.im : ℝ) : ℂ) * I := by
      rw [show c = (↑c.re : ℂ) + ↑c.im * I from (Complex.re_add_im c).symm]
      push_cast; ring_nf; simp only [re_add_im]; grind only
    rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hh := Complex.abs_im_le_norm (z - c)
    rw [Complex.sub_im] at hh
    linarith
  have h_corn_b : (↑(z.re + h.re) + ↑c.im * I : ℂ) ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (↑(z.re + h.re) + ↑c.im * I : ℂ) - c = ((z.re + h.re - c.re : ℝ) : ℂ) := by
      rw [show c = (↑c.re : ℂ) + ↑c.im * I from (Complex.re_add_im c).symm]
      push_cast; ring_nf; simp only [re_add_im]; grind only
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    have hh := Complex.abs_re_le_norm (z + h - c)
    rw [Complex.sub_re, Complex.add_re] at hh
    linarith
  -- Lift the three given ball memberships to the (↑·.re + ↑·.im * I) form
  -- that the segment helpers consume.
  have hz_lifted : (↑z.re + ↑z.im * I : ℂ) ∈ Metric.ball c R := by
    rw [Complex.re_add_im]; exact hz
  have hzhr_lifted : (↑(z.re + h.re) + ↑z.im * I : ℂ) ∈ Metric.ball c R := by
    have heq : (↑(z.re + h.re) + ↑z.im * I : ℂ) = z + ↑h.re := by
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [heq]; exact hzhr
  have hzh_lifted : (↑(z.re + h.re) + ↑(z.im + h.im) * I : ℂ) ∈ Metric.ball c R := by
    have heq : (↑(z.re + h.re) + ↑(z.im + h.im) * I : ℂ) = z + h := by
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [heq]; exact hzh
  -- Apply F_eq_F₁ at z + h and z + ↑h.re, then normalize `.re`/`.im` projections.
  have h_F1_zh  := F_eq_F₁ hR g hg_rect (z + h)    hzh
  have h_F1_zhr := F_eq_F₁ hR g hg_rect (z + ↑h.re) hzhr
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
    at h_F1_zh h_F1_zhr
  -- Continuity of the horizontal and vertical line parameterizations.
  have h_horiz_cont : Continuous (fun t : ℝ => (↑t + ↑z.im * I : ℂ)) :=
    Complex.continuous_ofReal.add continuous_const
  have h_vert_cont : Continuous (fun s : ℝ => (↑(z.re + h.re) + ↑s * I : ℂ)) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  -- Integrability on the four relevant sub-intervals.
  have h_int1 : IntervalIntegrable (fun t : ℝ => g (↑t + ↑z.im * I))
                  MeasureTheory.volume c.re z.re :=
    (hg_cont.comp h_horiz_cont.continuousOn
      (fun t ht => horiz_seg_in_ball hR h_corn_a hz_lifted t ht)).intervalIntegrable
  have h_int2 : IntervalIntegrable (fun t : ℝ => g (↑t + ↑z.im * I))
                  MeasureTheory.volume z.re (z.re + h.re) :=
    (hg_cont.comp h_horiz_cont.continuousOn
      (fun t ht => horiz_seg_in_ball hR hz_lifted hzhr_lifted t ht)).intervalIntegrable
  have h_int3 : IntervalIntegrable (fun s : ℝ => g (↑(z.re + h.re) + ↑s * I))
                  MeasureTheory.volume c.im z.im :=
    (hg_cont.comp h_vert_cont.continuousOn
      (fun s hs => vert_seg_in_ball hR h_corn_b hzhr_lifted s hs)).intervalIntegrable
  have h_int4 : IntervalIntegrable (fun s : ℝ => g (↑(z.re + h.re) + ↑s * I))
                  MeasureTheory.volume z.im (z.im + h.im) :=
    (hg_cont.comp h_vert_cont.continuousOn
      (fun s hs => vert_seg_in_ball hR hzhr_lifted hzh_lifted s hs)).intervalIntegrable
  -- Adjacent-interval additivity for the two relevant horizontal/vertical lines.
  have h_add_t :
      (∫ t in c.re..z.re, g (↑t + ↑z.im * I)) +
      (∫ t in z.re..(z.re + h.re), g (↑t + ↑z.im * I)) =
      ∫ t in c.re..(z.re + h.re), g (↑t + ↑z.im * I) :=
    intervalIntegral.integral_add_adjacent_intervals h_int1 h_int2
  have h_add_s :
      (∫ s in c.im..z.im, g (↑(z.re + h.re) + ↑s * I)) +
      (∫ s in z.im..(z.im + h.im), g (↑(z.re + h.re) + ↑s * I)) =
      ∫ s in c.im..(z.im + h.im), g (↑(z.re + h.re) + ↑s * I) :=
    intervalIntegral.integral_add_adjacent_intervals h_int3 h_int4
  -- Linear combination over ℂ.
  have hsm : ∀ x : ℂ, (I : ℂ) • x = I * x := fun _ => rfl
  simp_rw [hsm] at h_F1_zh h_F1_zhr ⊢
  linear_combination h_F1_zh - h_F1_zhr - h_add_t - I * h_add_s




end Spectra.PeriodicHolomorphic

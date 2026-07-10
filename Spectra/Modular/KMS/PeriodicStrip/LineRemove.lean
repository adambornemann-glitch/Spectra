/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.PeriodicStrip.Painleve

/-!
# The local Painlevé theorem: removing a horizontal line

This file completes the local Painlevé argument begun in `PeriodicStrip/Painleve.lean`: a function
continuous on an open ball and complex-differentiable everywhere on it except possibly on a single
horizontal line is in fact complex-differentiable on the whole ball — the line is removable.

The chain is: the vanishing rectangle-boundary integrals from `Painleve.lean`
(`integral_boundary_rect_eq_zero_off_horizLine`) produce a primitive `F` with `F' = g`
(`exists_primitive_of_continuousOn_of_rect_integral_zero`); since a primitive of a continuous
function is itself holomorphic, its derivative `deriv F` is holomorphic, and `g = deriv F` on the
ball transfers this back to `g`
(`differentiableOn_of_continuousOn_of_differentiableOn_off_horizLine`). This is the analytic
content used in `PeriodicStrip/Basic.lean` to upgrade the periodic extension from "holomorphic off
the boundary lattice" to "entire". An elementary integer-squeeze fact
(`intMul_eq_of_dist_lt`) closes the argument that a ball of radius `< β` meets at most one
boundary line `Im = n·β`.

## Main results

* `exists_primitive_of_continuousOn_of_rect_integral_zero` : existence of a primitive from
  vanishing rectangle-boundary integrals.
* `differentiableOn_of_continuousOn_of_differentiableOn_off_horizLine` : the local Painlevé
  line-removal theorem.
* `intMul_eq_of_dist_lt` : two integer multiples of `β` within distance `< β` coincide.
-/

open Complex Set Filter MeasureTheory intervalIntegral
open scoped Topology
namespace Spectra.PeriodicHolomorphic

/-- **Goursat's primitive on a ball.**

If `g : ℂ → ℂ` is continuous on the open ball `Metric.ball c R`, and the boundary
integral of `g` vanishes over every closed rectangle contained in the ball, then
`g` admits a primitive there: some `F : ℂ → ℂ` with `HasDerivAt F (g z) z` for
every `z ∈ Metric.ball c R`.

This is Lemma 2 of the local Painlevé argument. -/
lemma exists_primitive_of_continuousOn_of_rect_integral_zero
    {c : ℂ} {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ)
    (hg_cont : ContinuousOn g (Metric.ball c R))
    (hg_rect : ∀ z w : ℂ,
        Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ Metric.ball c R →
        (((∫ x in z.re..w.re, g (↑x + ↑z.im * I)) -
           ∫ x in z.re..w.re, g (↑x + ↑w.im * I)) +
         I • ∫ y in z.im..w.im, g (↑w.re + ↑y * I)) -
         I • ∫ y in z.im..w.im, g (↑z.re + ↑y * I) = 0) :
    ∃ F : ℂ → ℂ, ∀ z ∈ Metric.ball c R, HasDerivAt F (g z) z := by
  refine ⟨fun w =>
    I • (∫ s in c.im..w.im, g (↑c.re + ↑s * I)) +
        ∫ t in c.re..w.re, g (↑t + ↑w.im * I), ?_⟩
  intro z hz
  -- A. Inner ball, continuity at z, IsLittleO unfolding.
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball z hz
  have hg_at_z : ContinuousAt g z := hg_cont.continuousAt (Metric.isOpen_ball.mem_nhds hz)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.continuousAt_iff.mp hg_at_z (ε / 2) (by positivity)
  rw [Metric.eventually_nhds_iff]
  refine ⟨min r (δ₀ / 2), lt_min hr_pos (by positivity), fun w hwz => ?_⟩
  -- B. Norm bounds.
  have h_norm_lt : ‖w - z‖ < min r (δ₀ / 2) := by rwa [← dist_eq_norm]
  have h_lt_r : ‖w - z‖ < r := h_norm_lt.trans_le (min_le_left _ _)
  have h_lt_δ_half : ‖w - z‖ < δ₀ / 2 := h_norm_lt.trans_le (min_le_right _ _)
  have h_re_le : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
  have h_im_le : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  -- C. Ball memberships of the three corners.
  have hw_in : w ∈ Metric.ball c R := hr_sub <| by
    rw [Metric.mem_ball, dist_eq_norm]; exact h_lt_r
  have hzhr_in : z + ↑(w - z).re ∈ Metric.ball c R := hr_sub <| by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
        Complex.norm_real, Real.norm_eq_abs]
    exact h_re_le.trans_lt h_lt_r
  have hzh_in : z + (w - z) ∈ Metric.ball c R := by
    rw [show z + (w - z) = w from by ring]; exact hw_in
  -- D. Apply F_diff_eq_Lpath and rewrite into w-form.
  have h_lpath := F_diff_eq_Lpath hR g hg_cont hg_rect hz hzhr_in hzh_in
  simp only [Complex.sub_re, Complex.sub_im] at h_lpath
  have h_re_eq : z.re + (w.re - z.re) = w.re := by linarith
  have h_im_eq : z.im + (w.im - z.im) = w.im := by linarith
  rw [h_re_eq, h_im_eq] at h_lpath
  -- E. Lifted endpoints needed for segment helpers.
  have hz_lifted : (↑z.re + ↑z.im * I : ℂ) ∈ Metric.ball c R := by
    rw [Complex.re_add_im]; exact hz
  have hw_re_lifted : (↑w.re + ↑z.im * I : ℂ) ∈ Metric.ball c R := by
    have heq : (↑w.re + ↑z.im * I : ℂ) = z + ↑(w - z).re := by
      apply Complex.ext <;>
        simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.sub_re, Complex.sub_im]
    rw [heq]; exact hzhr_in
  have hw_im_lifted : (↑w.re + ↑w.im * I : ℂ) ∈ Metric.ball c R := by
    rw [Complex.re_add_im]; exact hw_in
  -- F. Integrability along the two segments.
  have h_int_horiz : IntervalIntegrable (fun t : ℝ => g (↑t + ↑z.im * I))
      MeasureTheory.volume z.re w.re := by
    apply ContinuousOn.intervalIntegrable
    apply hg_cont.comp ((Complex.continuous_ofReal.add continuous_const).continuousOn)
    intro t ht
    exact horiz_seg_in_ball hR hz_lifted hw_re_lifted t ht
  have h_int_vert : IntervalIntegrable (fun s : ℝ => g (↑w.re + ↑s * I))
      MeasureTheory.volume z.im w.im := by
    apply ContinuousOn.intervalIntegrable
    apply hg_cont.comp
      ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn)
    intro s hs
    exact vert_seg_in_ball hR hw_re_lifted hw_im_lifted s hs
  -- G. Integrand norm bounds (ε/2) via continuity at z.
  have h_horiz_bd : ∀ t ∈ Set.uIcc z.re w.re, ‖g (↑t + ↑z.im * I) - g z‖ ≤ ε / 2 := by
    intro t ht
    apply le_of_lt
    have h_dist : dist (↑t + ↑z.im * I : ℂ) z < δ₀ := by
      have heq : (↑t + ↑z.im * I : ℂ) - z = ↑(t - z.re) := by
        rw [show z = (↑z.re : ℂ) + ↑z.im * I from (Complex.re_add_im z).symm]
        push_cast; ring_nf; simp only [re_add_im]; grind only
      rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs]
      have h_t_bd : |t - z.re| ≤ |w.re - z.re| := by
        rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      calc |t - z.re| ≤ |w.re - z.re| := h_t_bd
        _ = |(w - z).re| := by rw [Complex.sub_re]
        _ ≤ ‖w - z‖ := h_re_le
        _ < δ₀ / 2 := h_lt_δ_half
        _ < δ₀ := by linarith
    have := hδ₀ h_dist
    rwa [dist_eq_norm] at this
  have h_vert_bd : ∀ s ∈ Set.uIcc z.im w.im, ‖g (↑w.re + ↑s * I) - g z‖ ≤ ε / 2 := by
    intro s hs
    apply le_of_lt
    have h_dist : dist (↑w.re + ↑s * I : ℂ) z < δ₀ := by
      have heq : (↑w.re + ↑s * I : ℂ) - z = ↑(w.re - z.re) + ↑(s - z.im) * I := by
        rw [show z = (↑z.re : ℂ) + ↑z.im * I from (Complex.re_add_im z).symm]
        push_cast; ring_nf
        simp only [add_im, mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re,
          one_mul, zero_add, add_zero, add_re, mul_re, zero_mul, sub_self]
      rw [dist_eq_norm, heq]
      have h_s_bd : |s - z.im| ≤ |w.im - z.im| := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      calc ‖((↑(w.re - z.re) : ℂ) + ↑(s - z.im) * I)‖
          ≤ ‖((↑(w.re - z.re) : ℂ))‖ + ‖((↑(s - z.im) : ℂ) * I)‖ := norm_add_le _ _
        _ = |w.re - z.re| + |s - z.im| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
                Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |(w - z).re| + |(w - z).im| := by
            rw [Complex.sub_re, Complex.sub_im]; linarith
        _ ≤ ‖w - z‖ + ‖w - z‖ := by linarith [h_re_le, h_im_le]
        _ = 2 * ‖w - z‖ := by ring
        _ < δ₀ := by linarith
    have := hδ₀ h_dist
    rwa [dist_eq_norm] at this
  -- H. Decompose (w - z) • g z as two constant integrals.
  have h_smul_split : (w - z) • g z
                    = (∫ _ in z.re..w.re, g z) + I • ∫ _ in z.im..w.im, g z := by
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const]
    -- ℝ-smul on ℂ is defeq to ofReal-then-mul; ℂ-smul on ℂ is defeq to mul.
    change (w - z) * g z = (↑(w.re - z.re) : ℂ) * g z + I * ((↑(w.im - z.im) : ℂ) * g z)
    have hwz_decomp : w - z = (↑(w.re - z.re) : ℂ) + ↑(w.im - z.im) * I := by
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
              Complex.I_re, Complex.I_im]
    rw [hwz_decomp]
    ring
  -- I. Final bound: rewrite, regroup, fold, triangle, bound.
  rw [h_lpath, h_smul_split]
  have h_combine :
      ((∫ t in z.re..w.re, g (↑t + ↑z.im * I)) + I • ∫ s in z.im..w.im, g (↑w.re + ↑s * I))
      - ((∫ _ in z.re..w.re, g z) + I • ∫ _ in z.im..w.im, g z)
      = ((∫ t in z.re..w.re, g (↑t + ↑z.im * I)) - ∫ _ in z.re..w.re, g z)
        + I • ((∫ s in z.im..w.im, g (↑w.re + ↑s * I)) - ∫ _ in z.im..w.im, g z) := by
    have hI : ∀ x : ℂ, (I : ℂ) • x = I * x := fun _ => rfl
    simp_rw [hI]; ring
  rw [h_combine]
  rw [← intervalIntegral.integral_sub h_int_horiz intervalIntegrable_const,
      ← intervalIntegral.integral_sub h_int_vert intervalIntegrable_const]
  calc ‖(∫ t in z.re..w.re, g (↑t + ↑z.im * I) - g z)
        + I • ∫ s in z.im..w.im, g (↑w.re + ↑s * I) - g z‖
      ≤ ‖∫ t in z.re..w.re, g (↑t + ↑z.im * I) - g z‖
        + ‖I • ∫ s in z.im..w.im, g (↑w.re + ↑s * I) - g z‖ := norm_add_le _ _
    _ = ‖∫ t in z.re..w.re, g (↑t + ↑z.im * I) - g z‖
        + ‖∫ s in z.im..w.im, g (↑w.re + ↑s * I) - g z‖ := by
          rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ (ε/2) * |w.re - z.re| + (ε/2) * |w.im - z.im| := by
        apply add_le_add
        · exact intervalIntegral.norm_integral_le_of_norm_le_const
            (fun t ht => h_horiz_bd t (Set.uIoc_subset_uIcc ht))
        · exact intervalIntegral.norm_integral_le_of_norm_le_const
            (fun s hs => h_vert_bd s (Set.uIoc_subset_uIcc hs))
    _ ≤ ε * ‖w - z‖ := by
        have h1 : |w.re - z.re| ≤ ‖w - z‖ := by
          rw [show |w.re - z.re| = |(w - z).re| from by rw [Complex.sub_re]]
          exact h_re_le
        have h2 : |w.im - z.im| ≤ ‖w - z‖ := by
          rw [show |w.im - z.im| = |(w - z).im| from by rw [Complex.sub_im]]
          exact h_im_le
        nlinarith [hε, abs_nonneg (w.re - z.re), abs_nonneg (w.im - z.im)]


/-- **Local Painlevé: removing a horizontal line as a singular set.**

If `g : ℂ → ℂ` is continuous on an open ball and complex-differentiable everywhere
on that ball except possibly on a single horizontal line `{ζ | ζ.im = a}`, then
`g` is complex-differentiable on the whole ball — the line is removable.

The argument composes the three preceding results: Cauchy–Goursat across the
line gives vanishing boundary integrals for every rectangle in the ball
(`integral_boundary_rect_eq_zero_off_horizLine`); these in turn yield a primitive
`F` with `F' = g` on the ball (`exists_primitive_of_continuousOn_of_rect_integral_zero`);
and a primitive of a continuous function, being itself holomorphic, has a
holomorphic derivative (`DifferentiableOn.deriv`), which transfers back to `g`.

This is the local form of the Painlevé / Schwarz-reflection style "remove a
line" theorem. It is the analytic content needed to upgrade the periodic
extension of a holomorphic strip function from "holomorphic off the boundary
lattice" to "entire". -/
lemma differentiableOn_of_continuousOn_of_differentiableOn_off_horizLine
    {c : ℂ} {R a : ℝ} (hR : 0 < R) (g : ℂ → ℂ)
    (hg_cont : ContinuousOn g (Metric.ball c R))
    (hg_diff : DifferentiableOn ℂ g (Metric.ball c R \ {z | z.im = a})) :
    DifferentiableOn ℂ g (Metric.ball c R) := by
  -- Step 1: rectangle hypothesis for every closed rectangle in the ball
  have hg_rect : ∀ z w : ℂ,
      Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ Metric.ball c R →
      (((∫ x in z.re..w.re, g (↑x + ↑z.im * I)) -
         ∫ x in z.re..w.re, g (↑x + ↑w.im * I)) +
       I • ∫ y in z.im..w.im, g (↑w.re + ↑y * I)) -
       I • ∫ y in z.im..w.im, g (↑z.re + ↑y * I) = 0 := by
    intro z w h_sub
    apply integral_boundary_rect_eq_zero_off_horizLine (a := a) g z w
    · exact hg_cont.mono h_sub
    · apply hg_diff.mono
      intro ζ ⟨hζ_open, hζ_line⟩
      refine ⟨h_sub ?_, hζ_line⟩
      exact ⟨Set.Ioo_subset_Icc_self hζ_open.1, Set.Ioo_subset_Icc_self hζ_open.2⟩
  -- Step 2: primitive
  obtain ⟨F, hF⟩ := exists_primitive_of_continuousOn_of_rect_integral_zero
                      hR g hg_cont hg_rect
  -- Step 3: F is DifferentiableOn (ball)
  have hF_diff : DifferentiableOn ℂ F (Metric.ball c R) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  -- Step 4: deriv F is DifferentiableOn (ball)  -- single-step!
  have h_deriv : DifferentiableOn ℂ (_root_.deriv F) (Metric.ball c R) :=
    hF_diff.deriv Metric.isOpen_ball
  -- Step 5: g = deriv F on the ball
  have h_eq : ∀ z ∈ Metric.ball c R, g z = _root_.deriv F z := fun z hz =>
    ((hF z hz).deriv).symm
  -- Step 6: transfer DifferentiableOn from deriv F to g
  intro z hz
  exact (h_deriv z hz).congr (fun w hw => (h_eq w hw)) (h_eq z hz)


/-- **Integer squeeze for boundary lines.**

Two integer multiples of a positive real `β` lying within distance `< β` of each
other must coincide. The arithmetic core of the assertion "a ball of radius `< β`
centered on a boundary line `Im = n·β` meets no other boundary line `Im = m·β`". -/
lemma intMul_eq_of_dist_lt {β : ℝ} (hβ : 0 < β) {m n : ℤ}
    (h : |(m : ℝ) * β - (n : ℝ) * β| < β) : m = n := by
  -- Factor: |↑m·β - ↑n·β| = |↑(m - n)| · β  (using β > 0).
  have heq : |(m : ℝ) * β - (n : ℝ) * β| = |((m - n : ℤ) : ℝ)| * β := by
    rw [show (m : ℝ) * β - (n : ℝ) * β = ((m - n : ℤ) : ℝ) * β from by push_cast; ring,
        abs_mul, abs_of_pos hβ]
  rw [heq] at h
  -- Divide by β > 0: |↑(m - n)| < 1.
  have h_lt_one : |((m - n : ℤ) : ℝ)| < 1 := (mul_lt_iff_lt_one_left hβ).mp h
  -- A nonzero integer has |·| ≥ 1 in ℝ; contradiction forces m - n = 0.
  have h_zero : (m - n : ℤ) = 0 := by
    by_contra hne
    have h1 : 1 ≤ |(m - n : ℤ)| := Int.one_le_abs hne
    have h2 : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast h1
    linarith
  omega


end Spectra.PeriodicHolomorphic

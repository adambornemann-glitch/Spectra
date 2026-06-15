/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: PeriodicStrip/Basic.lean
-/
import Spectra.KMS.PeriodicStrip.Defs
import Spectra.KMS.PeriodicStrip.IndexProps
import Spectra.KMS.PeriodicStrip.ExtensionProps
import Spectra.KMS.PeriodicStrip.Hadamard
import Spectra.KMS.PeriodicStrip.LineRemove

open Complex Set Metric

namespace Spectra.PeriodicHolomorphic

/-! ## Entirety of the Periodic Extension -/

variable {β:ℝ}

/-- **The periodic extension is entire.**

If `F` is holomorphic on the open strip, continuous on the closed strip, and has
matching boundary values `F(t) = F(t + iβ)`, then its periodic extension is
differentiable on all of `ℂ`.

This discharges the Morera/entire hypothesis that downstream results previously
*assumed*. The two ingredients are already available:
`periodicExtension_continuous` (continuity everywhere) and
`periodicExtension_differentiableAt_off_boundaries` (holomorphicity off the
boundary lattice `{Im = n·β}`). Around any point `z` we work in the ball of radius
`β/2`, which meets **at most one** lattice line — the nearest one, at height
`a = round(Im z / β)·β`. The local Painlevé theorem
`differentiableOn_of_continuousOn_of_differentiableOn_off_horizLine` removes that
single line, yielding differentiability on the whole ball, hence at `z`. -/
lemma periodicExtension_entire
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t)) :
    Differentiable ℂ (periodicExtension F β) := by
  have hcontG : Continuous (periodicExtension F β) :=
    periodicExtension_continuous F hβ hcont hperiod
  intro z
  have hR : (0 : ℝ) < β / 2 := by positivity
  -- The nearest lattice line to `z` sits at height `a = n₀ · β`.
  set n₀ : ℤ := round (z.im / β) with hn₀
  set a : ℝ := (n₀ : ℝ) * β with ha
  -- `z.im` is within `β/2` of that line.
  have hza : |z.im - a| ≤ β / 2 := by
    have hkey : z.im - a = (z.im / β - n₀) * β := by
      rw [ha, sub_mul, div_mul_cancel₀ _ (ne_of_gt hβ)]
    have hround : |z.im / β - (n₀ : ℝ)| ≤ 1 / 2 := by
      rw [hn₀]; exact abs_sub_round (z.im / β)
    rw [hkey, abs_mul, abs_of_pos hβ]
    calc |z.im / β - (n₀ : ℝ)| * β ≤ (1 / 2) * β :=
          mul_le_mul_of_nonneg_right hround hβ.le
      _ = β / 2 := by ring
  -- Continuity on the ball is immediate from global continuity.
  have hcontball : ContinuousOn (periodicExtension F β) (Metric.ball z (β / 2)) :=
    hcontG.continuousOn
  -- Holomorphicity on the ball minus the single line `{Im = a}`.
  have hdiffball : DifferentiableOn ℂ (periodicExtension F β)
      (Metric.ball z (β / 2) \ {w : ℂ | w.im = a}) := by
    intro w hw
    obtain ⟨hw_ball, hw_line⟩ := hw
    have hw_ne : w.im ≠ a := by simpa using hw_line
    -- `w` avoids the entire lattice, so it is a point of differentiability.
    have hw_off : w.im ∉ Set.range (fun n : ℤ => (n : ℝ) * β) := by
      rintro ⟨m, hm⟩
      have hmβ : (m : ℝ) * β = w.im := hm
      have hnorm : ‖w - z‖ < β / 2 := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw_ball
      have hdist : |w.im - z.im| < β / 2 := by
        have hle : |w.im - z.im| ≤ ‖w - z‖ := by
          rw [show w.im - z.im = (w - z).im from (Complex.sub_im w z).symm]
          exact Complex.abs_im_le_norm _
        linarith
      have hclash : |(m : ℝ) * β - a| < β :=
        calc |(m : ℝ) * β - a| = |w.im - a| := by rw [hmβ]
          _ ≤ |w.im - z.im| + |z.im - a| := abs_sub_le _ _ _
          _ < β / 2 + β / 2 := add_lt_add_of_lt_of_le hdist hza
          _ = β := by ring
      have hmn : m = n₀ := by
        apply intMul_eq_of_dist_lt hβ
        rwa [ha] at hclash
      exact hw_ne (by rw [← hmβ, hmn, ← ha])
    exact (periodicExtension_differentiableAt_off_boundaries F hβ hholo w
      hw_off).differentiableWithinAt
  -- Assemble via local Painlevé, then read off `DifferentiableAt` at the centre.
  have hmain : DifferentiableOn ℂ (periodicExtension F β) (Metric.ball z (β / 2)) :=
    differentiableOn_of_continuousOn_of_differentiableOn_off_horizLine hR
      (periodicExtension F β) hcontball hdiffball
  exact (hmain z (Metric.mem_ball_self hR)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))

/-! ## The Main Theorem -/

/-- **Periodic Strip Extension Theorem**
If F is holomorphic on the open strip, continuous on the closed strip,
bounded, and satisfies F(t) = F(t + iβ) for all real t, then F extends
to a bounded entire function that agrees with F on the strip.
Combined with Liouville's theorem, this implies F is constant.
-/
lemma periodic_strip_extension
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β))
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β)))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t)) :
    ∃ G : ℂ → ℂ,
      Differentiable ℂ G ∧
      Bornology.IsBounded (Set.range G) ∧
      (∀ z ∈ ClosedStrip β, G z = F z) :=
  ⟨periodicExtension F β,
   periodicExtension_entire F hβ hholo hcont hperiod,
   periodicExtension_bounded F hβ hbdd,
   fun _z hz => periodicExtension_eq_on_strip F hβ hcont hperiod hz⟩

/-! ## Application: Periodic Functions on Strips are Constant -/

/-- A holomorphic function on a strip with matching boundary values is constant.
This is the key result used in proving KMS states are time-invariant.-/
lemma periodic_strip_is_constant
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β))
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β)))
    (hperiod : ∀ t : ℝ, F (realToLower t) = F (realToUpper β t)) :
    ∃ c : ℂ, ∀ z ∈ ClosedStrip β, F z = c := by
  -- Get the bounded entire extension
  obtain ⟨G, G_entire, G_bdd, G_extends⟩ :=
    periodic_strip_extension F hβ hholo hcont hbdd hperiod
  -- By Liouville, G is constant
  have G_const : ∀ z w : ℂ, G z = G w :=
    fun z w => G_entire.apply_eq_apply_of_bounded G_bdd z w
  -- F agrees with G on the strip, so F is also constant there
  use G 0
  intro z hz
  rw [(G_extends z hz).symm, G_const z 0]

/-! ## Uniqueness on the Strip (Hadamard Three-Lines)

A bounded holomorphic function on the strip is determined by its two boundary
values: if it vanishes on both edges it vanishes throughout. This is the
maximum-modulus / Phragmén–Lindelöf content of the Hadamard three-lines theorem
(`Spectra.ThreeLines.hadamard_three_lines_horizontal`): the interpolation bound
collapses to `0` once both edge suprema are `0`.
-/

/-- A function holomorphic on the open strip, continuous and bounded on the closed
strip, vanishing on both boundary lines, is identically zero on the closed strip. -/
lemma eqZero_of_strip_boundary_zero
    (H : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ H (Strip β))
    (hcont : ContinuousOn H (ClosedStrip β))
    (hbdd : BddAbove (norm '' (H '' ClosedStrip β)))
    (hlow : ∀ t : ℝ, H (realToLower t) = 0)
    (hup : ∀ t : ℝ, H (realToUpper β t) = 0) :
    ∀ z ∈ ClosedStrip β, H z = 0 := by
  -- The supremum of ‖H‖ along each boundary line is 0.
  have hsup0 : sSup ((norm ∘ H) '' (Complex.im ⁻¹' {(0 : ℝ)})) = 0 := by
    have hset : (norm ∘ H) '' (Complex.im ⁻¹' {(0 : ℝ)}) = {0} := by
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨⟨0, ?_, ?_⟩, ?_⟩
      · simp [Set.mem_preimage]
      · show ‖H 0‖ = 0
        rw [show (0 : ℂ) = realToLower 0 from by simp [realToLower], hlow 0, norm_zero]
      · rintro y ⟨w, hw, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
        show ‖H w‖ = 0
        rw [show w = realToLower w.re from by apply Complex.ext <;> simp [realToLower, hw],
          hlow, norm_zero]
    rw [hset, csSup_singleton]
  have hsupβ : sSup ((norm ∘ H) '' (Complex.im ⁻¹' {β})) = 0 := by
    have hset : (norm ∘ H) '' (Complex.im ⁻¹' {β}) = {0} := by
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨⟨realToUpper β 0, ?_, ?_⟩, ?_⟩
      · simp [Set.mem_preimage, realToUpper]
      · show ‖H (realToUpper β 0)‖ = 0
        rw [hup, norm_zero]
      · rintro y ⟨w, hw, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
        show ‖H w‖ = 0
        rw [show w = realToUpper β w.re from by apply Complex.ext <;> simp [realToUpper, hw],
          hup, norm_zero]
    rw [hset, csSup_singleton]
  -- The Hadamard interpolation bound then forces ‖H z‖ ≤ 0.
  intro z hz
  have hbound :=
    Spectra.ThreeLines.hadamard_three_lines_horizontal H hβ hholo hcont hbdd z hz
  rw [hsup0, hsupβ] at hbound
  have hrhs : (0 : ℝ) ^ ((β - z.im) / β) * (0 : ℝ) ^ (z.im / β) = 0 := by
    rcases eq_or_ne (z.im / β) 0 with hq | hq
    · have hz0 : z.im = 0 := (div_eq_zero_iff.mp hq).resolve_right (ne_of_gt hβ)
      have hp : (β - z.im) / β ≠ 0 := by
        rw [hz0, sub_zero, div_self (ne_of_gt hβ)]; exact one_ne_zero
      rw [Real.zero_rpow hp, zero_mul]
    · rw [Real.zero_rpow hq, mul_zero]
  rw [hrhs] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

/-- **Uniqueness on the strip.** Two functions holomorphic on the open strip,
continuous and bounded on the closed strip, that agree on both boundary lines,
agree on the entire closed strip. -/
lemma eqOn_closedStrip_of_boundary_eq
    (F G : ℂ → ℂ) (hβ : 0 < β)
    (hFholo : DifferentiableOn ℂ F (Strip β)) (hGholo : DifferentiableOn ℂ G (Strip β))
    (hFcont : ContinuousOn F (ClosedStrip β)) (hGcont : ContinuousOn G (ClosedStrip β))
    (hFbdd : BddAbove (norm '' (F '' ClosedStrip β)))
    (hGbdd : BddAbove (norm '' (G '' ClosedStrip β)))
    (hlow : ∀ t : ℝ, F (realToLower t) = G (realToLower t))
    (hup : ∀ t : ℝ, F (realToUpper β t) = G (realToUpper β t)) :
    Set.EqOn F G (ClosedStrip β) := by
  intro z hz
  have hHbdd : BddAbove (norm '' ((fun w => F w - G w) '' ClosedStrip β)) := by
    obtain ⟨MF, hMF⟩ := hFbdd
    obtain ⟨MG, hMG⟩ := hGbdd
    refine ⟨MF + MG, ?_⟩
    rintro y ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    calc ‖F w - G w‖ ≤ ‖F w‖ + ‖G w‖ := norm_sub_le _ _
      _ ≤ MF + MG :=
          add_le_add (hMF ⟨F w, ⟨w, hw, rfl⟩, rfl⟩) (hMG ⟨G w, ⟨w, hw, rfl⟩, rfl⟩)
  have key := eqZero_of_strip_boundary_zero (fun w => F w - G w) hβ
    (hFholo.sub hGholo) (hFcont.sub hGcont) hHbdd
    (fun t => by simp [hlow t]) (fun t => by simp [hup t]) z hz
  exact sub_eq_zero.mp key

end Spectra.PeriodicHolomorphic

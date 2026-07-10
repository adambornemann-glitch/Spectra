/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.PeriodicStrip.Defs
import Mathlib.Analysis.Complex.Hadamard

/-!
# Hadamard's three-lines theorem for a horizontal strip

Mathlib's Hadamard three-lines theorem is stated for a *vertical* strip. This file transports it
to the *horizontal* strip `{0 ≤ Im z ≤ β}` used throughout `PeriodicStrip/`, via the rotation
`tildeF F z := F (I * z)`, which sends the vertical strip `{0 ≤ Re z ≤ β}` to the horizontal one
since `(I * z).im = z.re`. Differentiability, continuity, boundedness, and the boundary suprema of
`tildeF F` are transported across this rotation, and Mathlib's theorem is then translated back to
give `hadamard_three_lines_horizontal`.

## Main results

* `hadamard_three_lines_horizontal` : for `F` holomorphic on the open horizontal strip, continuous
  and bounded on its closure, `‖F w‖` is bounded by the log-convex interpolation of the boundary
  suprema of `‖F‖` along `{Im = 0}` and `{Im = β}`.
-/

open Complex Set Filter Topology Int MeasureTheory Complex.HadamardThreeLines
open Spectra.PeriodicHolomorphic
namespace Spectra.ThreeLines

variable {β : ℝ}

/-- The horizontal-to-vertical rotation: `tildeF F z = F (i z)`.
    Designed so `(I * z).im = z.re`, mapping the vertical strip to the horizontal one. -/
def tildeF (F : ℂ → ℂ) : ℂ → ℂ := fun z => F (I * z)

/-- `tildeF F` is `DiffContOnCl` on the vertical strip when `F` is holomorphic and continuous
    on the horizontal strip. -/
lemma tildeF_diffContOnCl
    (F : ℂ → ℂ) (_hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β)) :
    DiffContOnCl ℂ (tildeF F) (verticalStrip 0 β) := by
  have h_im_eq : ∀ z : ℂ, (I * z).im = z.re := fun z => by simp
  have hrot_diff : Differentiable ℂ (fun z : ℂ => I * z) := by fun_prop
  refine ⟨?_, ?_⟩
  · -- Differentiability on the open vertical strip
    have hmaps : Set.MapsTo (fun z : ℂ => I * z) (verticalStrip 0 β) (Strip β) := by
      intro z hz
      refine ⟨?_, ?_⟩
      · rw [h_im_eq]; exact hz.1
      · rw [h_im_eq]; exact hz.2
    exact hholo.comp hrot_diff.differentiableOn hmaps
  · -- Continuity on the closure
    have hcl_sub : closure (verticalStrip 0 β) ⊆ verticalClosedStrip 0 β := by
      refine closure_minimal ?_ (isClosed_Icc.preimage Complex.continuous_re)
      intro z hz
      exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    apply ContinuousOn.mono _ hcl_sub
    have hmaps : Set.MapsTo (fun z : ℂ => I * z) (verticalClosedStrip 0 β) (ClosedStrip β) := by
      intro z hz
      refine ⟨?_, ?_⟩
      · rw [h_im_eq]; exact hz.1
      · rw [h_im_eq]; exact hz.2
    exact hcont.comp hrot_diff.continuous.continuousOn hmaps

/-- The norms of `tildeF F` on the vertical closed strip are bounded above whenever the norms of
    `F` on the horizontal closed strip are. -/
lemma tildeF_bddAbove
    (F : ℂ → ℂ) (_hβ : 0 < β)
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β))) :
    BddAbove (norm '' (tildeF F '' verticalClosedStrip 0 β)) := by
  have h_im_eq : ∀ z : ℂ, (I * z).im = z.re := fun z => by simp
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨M, ?_⟩
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  -- After destructure: x = ‖tildeF F z‖ = ‖F (I * z)‖, goal: ‖F (I * z)‖ ≤ M
  apply hM
  -- Goal: ‖F (I * z)‖ ∈ norm '' (F '' ClosedStrip β)
  exact ⟨F (I * z), ⟨I * z,
    ⟨by rw [h_im_eq]; exact hz.1, by rw [h_im_eq]; exact hz.2⟩, rfl⟩, rfl⟩

/-- The rotation `z ↦ I * z` sends the vertical line `{Re = x}` bijectively
    to the horizontal line `{Im = x}`. -/
lemma image_I_mul_re (x : ℝ) :
    (fun z : ℂ => I * z) '' (Complex.re ⁻¹' {x}) = Complex.im ⁻¹' {x} := by
  ext w
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [show (I * z).im = z.re from by simp]
    exact hz
  · intro hw
    refine ⟨-I * w, ?_, ?_⟩
    · rw [show (-I * w).re = w.im from by simp]
      exact hw
    · -- I * (-I * w) = w via I * I = -1
      have h : I * (-I * w) = -(I * I) * w := by ring
      rw [h, Complex.I_mul_I]
      ring

/-- The `sSupNormIm` of `tildeF F` at level `x` equals the supremum of `‖F‖`
    along the horizontal line `{Im = x}`. -/
lemma sSupNormIm_tildeF (F : ℂ → ℂ) (x : ℝ) :
    sSupNormIm (tildeF F) x = sSup ((norm ∘ F) '' (Complex.im ⁻¹' {x})) := by
  unfold sSupNormIm
  apply congrArg sSup
  rw [show ((norm ∘ tildeF F) : ℂ → ℝ) = (norm ∘ F) ∘ (fun z : ℂ => I * z) from rfl,
      Set.image_comp, image_I_mul_re]

/-- Hadamard's three-lines theorem for a horizontal strip: `‖F w‖` is bounded by the log-convex
    interpolation of the boundary suprema of `‖F‖` along `{Im = 0}` and `{Im = β}`. -/
lemma hadamard_three_lines_horizontal
    (F : ℂ → ℂ) (hβ : 0 < β)
    (hholo : DifferentiableOn ℂ F (Strip β))
    (hcont : ContinuousOn F (ClosedStrip β))
    (hbdd : BddAbove (norm '' (F '' ClosedStrip β)))
    (w : ℂ) (hw : w ∈ ClosedStrip β) :
    ‖F w‖ ≤ sSup ((norm ∘ F) '' (Complex.im ⁻¹' {0})) ^ ((β - w.im) / β) *
            sSup ((norm ∘ F) '' (Complex.im ⁻¹' {β})) ^ (w.im / β) := by
  -- Rotation: -I * w is the vertical-strip counterpart of w
  have hre_eq : (-I * w).re = w.im := by simp
  have hz_mem : -I * w ∈ verticalClosedStrip 0 β := by
    refine ⟨?_, ?_⟩
    · rw [hre_eq]; exact hw.1
    · rw [hre_eq]; exact hw.2
  have hF_eq : tildeF F (-I * w) = F w := by
    change F (I * (-I * w)) = F w
    congr 1
    have h : I * (-I * w) = -(I * I) * w := by ring
    rw [h, Complex.I_mul_I]; ring
  -- Reformat hypotheses to match Mathlib's input shape
  have hbdd' : BddAbove ((norm ∘ tildeF F) '' verticalClosedStrip 0 β) := by
    rw [Set.image_comp]
    exact tildeF_bddAbove F hβ hbdd
  have hd : DiffContOnCl ℂ (tildeF F) (verticalStrip 0 β) :=
    tildeF_diffContOnCl F hβ hholo hcont
  -- Apply Mathlib's three-lines, then translate everything back
  have key := norm_le_interp_of_mem_verticalClosedStrip'
                (a := sSupNormIm (tildeF F) 0)
                (b := sSupNormIm (tildeF F) β)
                hβ hz_mem hd hbdd'
  rw [sSupNormIm_tildeF, sSupNormIm_tildeF, hF_eq, hre_eq] at key
  -- Boundary sup sets are bounded above (subsets of F '' ClosedStrip β)
  have h_bdd_lower : BddAbove ((fun a => ‖F a‖) '' (Complex.im ⁻¹' {0})) := by
    obtain ⟨M, hM⟩ := hbdd
    refine ⟨M, ?_⟩
    rintro x ⟨z, hz, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    refine hM ⟨F z, ⟨z, ?_, rfl⟩, rfl⟩
    change 0 ≤ z.im ∧ z.im ≤ β
    rw [hz]; exact ⟨le_refl 0, le_of_lt hβ⟩
  have h_bdd_upper : BddAbove ((fun a => ‖F a‖) '' (Complex.im ⁻¹' {β})) := by
    obtain ⟨M, hM⟩ := hbdd
    refine ⟨M, ?_⟩
    rintro x ⟨z, hz, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
    refine hM ⟨F z, ⟨z, ?_, rfl⟩, rfl⟩
    change 0 ≤ z.im ∧ z.im ≤ β
    rw [hz]; exact ⟨le_of_lt hβ, le_refl _⟩
  -- The edge bounds Mathlib requires
  have ha : ∀ z : ℂ, z.re = 0 →
      ‖tildeF F z‖ ≤ sSup ((fun a => ‖F a‖) '' (Complex.im ⁻¹' {0})) := by
    intro z hz
    apply le_csSup h_bdd_lower
    refine ⟨I * z, ?_, rfl⟩
    change (I * z).im = 0
    rw [show (I * z).im = z.re from by simp]; exact hz
  have hb : ∀ z : ℂ, z.re = β →
      ‖tildeF F z‖ ≤ sSup ((fun a => ‖F a‖) '' (Complex.im ⁻¹' {β})) := by
    intro z hz
    apply le_csSup h_bdd_upper
    refine ⟨I * z, ?_, rfl⟩
    change (I * z).im = β
    rw [show (I * z).im = z.re from by simp]; exact hz
  -- Bridge the exponent: (β - w.im)/β = 1 - w.im/β
  have hβ_ne : β ≠ 0 := ne_of_gt hβ
  rw [show (β - w.im) / β = 1 - w.im / β from by field_simp]
  have final := key ha hb
  simp only [sub_zero] at final
  exact final

end Spectra.ThreeLines

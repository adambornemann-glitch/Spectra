/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.AnalyticElements
import Spectra.Modular.KMS.PeriodicStrip.Basic
/-!
# The Imaginary-Time KMS Condition

For a KMS state `ω` at inverse temperature `β` and an **analytic element** `b` (A1), the strip
boundary condition becomes the algebraic imaginary-time identity

`ω (a · σ_{iβ}(b)) = ω (b · a)`,

where `σ_{iβ}` is the complexified flow at imaginary time `iβ` (`Dynamics.sigma`, A1). This is the
modern operator-algebraic form of the KMS condition (Bratteli–Robinson, *OAQSM 1*, Prop. 5.3.7).

## Proof

The boundary correlation `t ↦ ω (a · α_t b)` continues to the entire function
`G z := ω (a · σ_z(b))`, which is bounded on the closed strip because `α_t` is isometric (A1) so
`‖σ_z b‖ = ‖σ_{i·Im z} b‖` depends only on `Im z ∈ [0, β]`. The KMS function `F` for `(a, b)` and
`G` agree on the lower boundary `ℝ` (both equal `ω(a·α_t b)`), so by **one-boundary strip
uniqueness** (`eqOn_closedStrip_of_lower_boundary_eq`) they agree on the whole closed strip.
Evaluating at `iβ`: `G(iβ) = ω(a·σ_{iβ} b)` and `F(iβ) = ω(b·a)` (upper boundary at `t = 0`).

## Main result

* `Spectra.KMS.IsKMSState.imaginaryTime`.
-/

open Complex Set Filter Topology
open Spectra.PeriodicHolomorphic

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

/-- The correlation continuation `z ↦ ω (a · σ_z b)` of an analytic element `b` is **entire**. This
uses no KMS hypothesis — only that `ω` is a state and `b` is analytic. -/
lemma sigmaCorr_differentiable {ω : State A} {α : Dynamics A} {b : A}
    (hb : α.IsAnalyticElement b) (a : A) :
    Differentiable ℂ (fun z => ω (a * α.sigma hb z)) := by
  set ωL : A →L[ℂ] ℂ := ⟨ω.toFun, ω.continuous⟩
  have hσdiff : Differentiable ℂ (fun z => α.sigma hb z) := by
    simp only [Dynamics.sigma]; exact α.analyticExtend_differentiable hb
  exact ωL.differentiable.comp (hσdiff.const_mul a)

/-- The correlation continuation `z ↦ ω (a · σ_z b)` is **bounded on the closed strip**: since `α_t`
is isometric, `‖σ_z b‖ = ‖σ_{i·Im z} b‖` depends only on `Im z ∈ [0,β]`, a compact set. No KMS
hypothesis is used. -/
lemma sigmaCorr_bddAbove_closedStrip {ω : State A} {α : Dynamics A} {β : ℝ} {b : A}
    (hb : α.IsAnalyticElement b) (a : A) :
    BddAbove (norm '' ((fun z => ω (a * α.sigma hb z)) '' ClosedStrip β)) := by
  set ωL : A →L[ℂ] ℂ := ⟨ω.toFun, ω.continuous⟩
  have hcont_norm : Continuous (fun s : ℝ => ‖α.analyticExtend hb ((s : ℂ) * I)‖) :=
    ((α.analyticExtend_differentiable hb).continuous.comp (by fun_prop)).norm
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.image_of_continuousOn (hcont_norm.continuousOn)).bddAbove
  refine ⟨‖ωL‖ * (‖a‖ * M), ?_⟩
  rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
  have hredz : ‖α.analyticExtend hb z‖ = ‖α.analyticExtend hb ((z.im : ℂ) * I)‖ := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [α.ext_add_real hb z.re ((z.im : ℂ) * I), α.norm_evolve]
  have hzim : ‖α.analyticExtend hb ((z.im : ℂ) * I)‖ ≤ M := hM ⟨z.im, ⟨hz.1, hz.2⟩, rfl⟩
  change ‖ω (a * α.sigma hb z)‖ ≤ ‖ωL‖ * (‖a‖ * M)
  simp only [Dynamics.sigma]
  calc ‖ω (a * α.analyticExtend hb z)‖
      ≤ ‖ωL‖ * ‖a * α.analyticExtend hb z‖ := ωL.le_opNorm _
    _ ≤ ‖ωL‖ * (‖a‖ * ‖α.analyticExtend hb z‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖ωL‖ * (‖a‖ * M) := by
        rw [hredz]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hzim (norm_nonneg _)) (norm_nonneg _)

/-- **The imaginary-time KMS condition.** For a KMS state `ω` at inverse temperature `β` and an
analytic element `b`, `ω (a · σ_{iβ}(b)) = ω (b · a)`. -/
theorem IsKMSState.imaginaryTime {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    (hkms : IsKMSState ω α β) {b : A} (hb : α.IsAnalyticElement b) (a : A) :
    ω (a * α.sigma hb ((β : ℂ) * I)) = ω (b * a) := by
  obtain ⟨F⟩ := hkms a b
  -- The analytic continuation `G z = ω (a · σ_z b)` — entire and bounded on the closed strip,
  -- independent of the KMS hypothesis.
  set G : ℂ → ℂ := fun z => ω (a * α.sigma hb z) with hG_def
  have hGdiff : Differentiable ℂ G := sigmaCorr_differentiable hb a
  have hGbdd : BddAbove (norm '' (G '' ClosedStrip β)) := sigmaCorr_bddAbove_closedStrip hb a
  -- `F` and `G` agree on the lower boundary line.
  have hlowEq : ∀ t : ℝ, F.toFun (realToLower t) = G (realToLower t) := by
    intro t
    have hGt : G (realToLower t) = ω (a * α.evolve t b) := by
      change ω (a * α.sigma hb (realToLower t)) = ω (a * α.evolve t b)
      rw [show α.sigma hb (realToLower t) = α.evolve t b from α.sigma_ofReal hb t]
    rw [F.lower_boundary t, hGt]
  -- One-boundary uniqueness ⇒ they agree on the whole closed strip.
  have hFG : Set.EqOn F.toFun G (ClosedStrip β) :=
    eqOn_closedStrip_of_lower_boundary_eq F.toFun G hβ
      F.holomorphic hGdiff.differentiableOn
      F.continuousOn hGdiff.continuous.continuousOn
      F.bounded hGbdd hlowEq
  -- Evaluate at `iβ = realToUpper β 0`.
  have hβI_eq : (β : ℂ) * I = realToUpper β 0 := by simp [realToUpper]
  have hiβ_im : ((β : ℂ) * I).im = β := by simp
  have hiβ_mem : (β : ℂ) * I ∈ ClosedStrip β := by
    refine ⟨?_, le_of_eq hiβ_im⟩
    rw [hiβ_im]; exact hβ.le
  calc ω (a * α.sigma hb ((β : ℂ) * I))
      = G ((β : ℂ) * I) := by simp only [hG_def]
    _ = F.toFun ((β : ℂ) * I) := (hFG hiβ_mem).symm
    _ = F.toFun (realToUpper β 0) := by rw [hβI_eq]
    _ = ω (α.evolve 0 b * a) := F.upper_boundary 0
    _ = ω (b * a) := by rw [α.evolve_zero]

end Spectra.KMS

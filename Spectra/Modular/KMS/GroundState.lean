/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.Condition
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Piecewise
/-!
# Ground States are Invariant

A ground state (the `β = +∞` case of KMS) is invariant under its dynamics.

The proof is the two-half-plane gluing argument. For the pair `(1, a)` the correlation
`t ↦ ω (α_t a)` extends to a bounded function `F` holomorphic on the upper half-plane. By
hermiticity of `ω` (`State.star_apply`) and the fact that `α` is a `*`-automorphism, the
*conjugate-reflected* extension `G z = conj (F'(conj z))` built from the pair `(1, star a)`
is holomorphic on the lower half-plane, bounded, and agrees with `F` on `ℝ`. Gluing `F` and
`G` across the real axis (local Painlevé line-removal) produces a bounded entire function; by
Liouville it is constant, so `ω (α_t a) = ω (α_0 a) = ω a`.

A bounded holomorphic function on the closed upper half-plane is **not** forced constant by its
real boundary values alone (e.g. `e^{iz}`); the constancy here genuinely uses the second,
reflected analytic continuation — i.e. the spectrum/positivity content packaged into
`IsGroundState`.

## Main statements

* `Spectra.KMS.const_of_glue` — the analytic core: a function bounded-holomorphic on the closed
  upper half-plane glued to one on the closed lower half-plane, agreeing on `ℝ`, has constant
  boundary values.
* `Spectra.KMS.IsGroundState.isInvariant` — ground states are invariant.
-/

open Complex Set Filter Topology
open ComplexConjugate
open Spectra.PeriodicHolomorphic

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

/-- **Two-half-plane gluing.** If `F` is holomorphic on the open upper half-plane, continuous and
bounded on its closure, and `G` likewise on the lower half-plane, and they agree on the real
axis, then the common boundary values are constant: `F s = F t` for all real `s, t`. -/
lemma const_of_glue (F G : ℂ → ℂ)
    (hFd : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hGd : DifferentiableOn ℂ G {z : ℂ | z.im < 0})
    (hFc : ContinuousOn F {z : ℂ | 0 ≤ z.im})
    (hGc : ContinuousOn G {z : ℂ | z.im ≤ 0})
    (hFb : BddAbove (norm '' (F '' {z : ℂ | 0 ≤ z.im})))
    (hGb : BddAbove (norm '' (G '' {z : ℂ | z.im ≤ 0})))
    (hagree : ∀ t : ℝ, F t = G t) :
    ∀ s t : ℝ, F s = F t := by
  classical
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hLopen : IsOpen {z : ℂ | z.im < 0} := isOpen_lt continuous_im continuous_const
  -- The glued function.
  set H : ℂ → ℂ := fun z => if 0 ≤ z.im then F z else G z with _hHdef
  -- Off the real axis, `H` is locally `F` (above) or `G` (below), hence differentiable.
  have hHoff : ∀ w : ℂ, w.im ≠ 0 → DifferentiableAt ℂ H w := by
    intro w hwne
    rcases lt_or_gt_of_ne hwne with hlt | hgt
    · have hmem : w ∈ {z : ℂ | z.im < 0} := hlt
      have hHG : H =ᶠ[𝓝 w] G :=
        eventuallyEq_of_mem (hLopen.mem_nhds hmem) fun u hu => if_neg (not_le.mpr hu)
      exact (hGd.differentiableAt (hLopen.mem_nhds hmem)).congr_of_eventuallyEq hHG
    · have hmem : w ∈ {z : ℂ | 0 < z.im} := hgt
      have hHF : H =ᶠ[𝓝 w] F :=
        eventuallyEq_of_mem (hUopen.mem_nhds hmem) fun u hu => if_pos (le_of_lt hu)
      exact (hFd.differentiableAt (hUopen.mem_nhds hmem)).congr_of_eventuallyEq hHF
  -- `H` is continuous (pasting across the real axis, where `F = G`).
  have hHcont : Continuous H := by
    rw [← continuousOn_univ]
    apply ContinuousOn.if (p := fun z : ℂ => 0 ≤ z.im)
    · intro z hz
      have hz0 : z.im = 0 := by
        have h := hz.2
        rwa [frontier_setOf_le_im] at h
      have : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz0]
      rw [this]; exact hagree z.re
    · have hcl : closure {z : ℂ | 0 ≤ z.im} = {z : ℂ | 0 ≤ z.im} :=
        (isClosed_Ici.preimage continuous_im).closure_eq
      rw [univ_inter, hcl]; exact hFc
    · have hcl : closure {z : ℂ | ¬ 0 ≤ z.im} = {z : ℂ | z.im ≤ 0} := by
        simp only [not_le]; exact closure_setOf_im_lt 0
      rw [univ_inter, hcl]; exact hGc
  -- `H` is entire: differentiable off `ℝ`, and the real axis is removable (local Painlevé).
  have hHdiff : Differentiable ℂ H := by
    intro z
    by_cases hz : z.im = 0
    · have hdiffball : DifferentiableOn ℂ H (Metric.ball z 1 \ {w : ℂ | w.im = 0}) :=
        fun w hw => (hHoff w (by simpa using hw.2)).differentiableWithinAt
      have hmain := differentiableOn_of_continuousOn_of_differentiableOn_off_horizLine
        (c := z) (a := 0) one_pos H hHcont.continuousOn hdiffball
      exact (hmain z (Metric.mem_ball_self one_pos)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
    · exact hHoff z hz
  -- `H` is bounded.
  have hHbdd : Bornology.IsBounded (Set.range H) := by
    obtain ⟨MF, hMF⟩ := hFb
    obtain ⟨MG, hMG⟩ := hGb
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max MF MG, ?_⟩
    rintro w ⟨z, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_cases hz : 0 ≤ z.im
    · have hHz : H z = F z := if_pos hz
      rw [hHz]
      exact (hMF ⟨F z, ⟨z, hz, rfl⟩, rfl⟩).trans (le_max_left _ _)
    · have hHz : H z = G z := if_neg hz
      rw [hHz]
      exact (hMG ⟨G z, ⟨z, le_of_lt (not_le.mp hz), rfl⟩, rfl⟩).trans (le_max_right _ _)
  -- Liouville: `H` is constant; read off the boundary values.
  have hHconst : ∀ u v : ℂ, H u = H v := fun u v =>
    hHdiff.apply_eq_apply_of_bounded hHbdd u v
  intro s t
  have hs : H (s : ℂ) = F s := if_pos (by simp)
  have ht : H (t : ℂ) = F t := if_pos (by simp)
  rw [← hs, ← ht]; exact hHconst _ _

/-- **Ground states are invariant.** If `ω` is a ground state for the dynamics `α`, then
`ω (α_t a) = ω a` for all `t` and `a`. -/
lemma IsGroundState.isInvariant {ω : State A} {α : Dynamics A}
    (h : IsGroundState ω α) : IsInvariant ω α := by
  intro t a
  obtain ⟨F, hFd, hFc, hFb, hFbound⟩ := h 1 a
  obtain ⟨F', hF'd, hF'c, hF'b, hF'bound⟩ := h 1 (star a)
  have hUopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  -- The conjugate-reflected lower-half-plane extension.
  set G : ℂ → ℂ := fun z => conj (F' (conj z)) with hGdef
  have hconj_im : ∀ z : ℂ, (conj z).im = -z.im := fun z => Complex.conj_im z
  -- `G` is holomorphic on the open lower half-plane (Schwarz reflection of `F'`).
  have hGd : DifferentiableOn ℂ G {z : ℂ | z.im < 0} := by
    intro z hz
    have hz' : z.im < 0 := hz
    have hcz : conj z ∈ {z : ℂ | 0 < z.im} := by
      simp only [Set.mem_setOf_eq, hconj_im]; linarith
    have hdF' : DifferentiableAt ℂ F' (conj z) := hF'd.differentiableAt (hUopen.mem_nhds hcz)
    have hd := hdF'.conj_conj
    rw [Complex.conj_conj] at hd
    exact hd.differentiableWithinAt
  -- `G` is continuous and bounded on the closed lower half-plane.
  have hmaps : Set.MapsTo conj {z : ℂ | z.im ≤ 0} {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    have hz' : z.im ≤ 0 := hz
    simp only [Set.mem_setOf_eq, hconj_im]; linarith
  have hGc : ContinuousOn G {z : ℂ | z.im ≤ 0} :=
    Complex.continuous_conj.comp_continuousOn (hF'c.comp Complex.continuous_conj.continuousOn hmaps)
  have hGb : BddAbove (norm '' (G '' {z : ℂ | z.im ≤ 0})) := by
    obtain ⟨M, hM⟩ := hF'b
    refine ⟨M, ?_⟩
    rintro x ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    have hval : ‖G z‖ = ‖F' (conj z)‖ := by rw [hGdef]; simp
    rw [hval]
    exact hM ⟨F' (conj z), ⟨conj z, hmaps hz, rfl⟩, rfl⟩
  -- `F` and `G` agree on the real axis (hermiticity of `ω`).
  have hagree : ∀ s : ℝ, F s = G s := by
    intro s
    have hFs : F (s : ℂ) = ω (α.evolve s a) := by rw [hFbound s, one_mul]
    have hGs : G (s : ℂ) = star (ω (α.evolve s (star a))) := by
      change conj (F' (conj (s : ℂ))) = star (ω (α.evolve s (star a)))
      rw [Complex.conj_ofReal, hF'bound s, one_mul, starRingEnd_apply]
    rw [hFs, hGs, ← ω.star_apply, ← α.map_star, star_star]
  -- Glue and conclude.
  have hconst := const_of_glue F G hFd hGd hFc hGc hFb hGb hagree
  have e1 : ω (α.evolve t a) = F (t : ℂ) := by rw [hFbound t, one_mul]
  have e0 : ω (α.evolve (0 : ℝ) a) = F ((0 : ℝ) : ℂ) := by rw [hFbound 0, one_mul]
  rw [e1, hconst t 0, ← e0, α.evolve_zero]

end Spectra.KMS

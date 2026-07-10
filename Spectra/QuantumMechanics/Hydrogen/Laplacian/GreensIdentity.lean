/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Green's identity for radial functions with a Kato cusp

Infrastructure for the **reverse direction** of `hydrogen_discrete_spectrum` (`ℓ = 0`, `Z = 1`).

The transported `s`-state eigenfunction is the purely radial `f(x) = c·R_{n0}(‖x‖)`: continuous
everywhere, `C^∞` away from the origin, but with the **Kato cusp** at `x = 0` (`∇f` is bounded
but discontinuous there).  To establish `MemSobolevH2 f` and compute its weak Laplacian we use
the Fourier characterisation `memSobolevH2_of_fourier_decay`, which requires
`(1 + ‖ξ‖²)·𝓕f ∈ L²`.  That reduces to the distributional **Green's identity**

  `∫ f·(Δφ) = ∫ (Δf)·φ`   for all test functions `φ`,

with no Dirac delta at the origin (the gradient is bounded, so the single point carries no `H¹`
capacity).  The identity is proved by a smooth cutoff: multiply by `χ_ε` vanishing near the
origin, apply the classical integration by parts, and let `ε → 0`; the cutoff shell terms vanish
because `f` and `∇f` are bounded near `0`, against the `O(1/ε)`-and-`O(1/ε²)` cutoff derivatives
on a shell of volume `O(ε³)`.

## This file (so far)

The **1-D cutoff profile** `cutoffP` (`0` on `(-∞,1]`, `1` on `[2,∞)`, `C^∞`, valued in `[0,1]`)
with globally bounded first and second derivatives (compactly supported in `[1,2]`).  The radial
cutoff is `χ_ε(x) = cutoffP(‖x‖/ε)`, whose gradient and Laplacian are then `O(1/ε)` and `O(1/ε²)`.

## Main definitions

* `cutoffP` — the 1-D cutoff profile, built from `Real.smoothTransition`.

## Main statements

* `cutoffP_contDiff` — `cutoffP` is `C^∞`.
* `cutoffP_eq_zero`, `cutoffP_eq_one`, `cutoffP_nonneg`, `cutoffP_le_one` — the defining shape of
  the profile: `0` on `(-∞,1]`, `1` on `[2,∞)`, valued in `[0,1]` throughout.
* `deriv_cutoffP_bounded`, `deriv2_cutoffP_bounded` — the first and second derivatives are globally
  bounded, via `hasCompactSupport_deriv_cutoffP`/`hasCompactSupport_deriv2_cutoffP` (both supported
  in `[1,2]`, `deriv_cutoffP_support`/`deriv2_cutoffP_support`).

## Implementation notes

`cutoffP` is reused from Mathlib's `Real.smoothTransition` rather than built as a bespoke bump
function, since `smoothTransition` already provides exactly the `0`-to-`1` transition shape (with
`C^∞` smoothness for every order, not just up to some fixed `n`) that this file's compact-support
and boundedness arguments need. The support/boundedness lemmas for the first and second derivative
share two private helpers (`bounded_of_continuous_hasCompactSupport`,
`derivCutoffP_eventuallyEq_zero_of_lt`/`_of_gt`, built on `cutoffP_eventuallyEq_zero_of_lt`/
`_one_of_gt`) rather than duplicating the "continuous + compactly supported ⟹ bounded" and
"eventually constant near `t` ⟹ derivative vanishes at `t`" arguments once per derivative order.

## References

* [Evans, *Partial Differential Equations*][evans2010], Section 5.3 (mollifiers/cutoffs)
-/

noncomputable section

namespace Spectra.QuantumMechanics.Hydrogen

open scoped ContDiff

/-! ## The 1-D cutoff profile -/

/-- The 1-D cutoff **p**rofile (hence the `P` suffix): `0` on `(-∞,1]`, `1` on `[2,∞)`, `C^∞`,
    valued in `[0,1]`. -/
def cutoffP : ℝ → ℝ := fun t => Real.smoothTransition (t - 1)

/-- `cutoffP` is `C^∞`. -/
lemma cutoffP_contDiff : ContDiff ℝ ∞ cutoffP := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => t - 1) := by fun_prop
  exact Real.smoothTransition.contDiff.comp h1

/-- `cutoffP` vanishes on `(-∞, 1]`. -/
lemma cutoffP_eq_zero {t : ℝ} (ht : t ≤ 1) : cutoffP t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- `cutoffP` equals `1` on `[2, ∞)`. -/
lemma cutoffP_eq_one {t : ℝ} (ht : 2 ≤ t) : cutoffP t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- `cutoffP` is nonnegative. -/
lemma cutoffP_nonneg (t : ℝ) : 0 ≤ cutoffP t := Real.smoothTransition.nonneg _

/-- `cutoffP` is bounded above by `1`. -/
lemma cutoffP_le_one (t : ℝ) : cutoffP t ≤ 1 := Real.smoothTransition.le_one _

/-- The derivative of `cutoffP` is continuous. -/
lemma deriv_cutoffP_continuous : Continuous (deriv cutoffP) :=
  cutoffP_contDiff.continuous_deriv (by norm_num)

/-- `cutoffP` is eventually `0` in a neighborhood of any `t < 1`. -/
private lemma cutoffP_eventuallyEq_zero_of_lt {t : ℝ} (ht : t < 1) :
    cutoffP =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact cutoffP_eq_zero hs.le

/-- `cutoffP` is eventually `1` in a neighborhood of any `2 < t`. -/
private lemma cutoffP_eventuallyEq_one_of_gt {t : ℝ} (ht : 2 < t) :
    cutoffP =ᶠ[nhds t] (fun _ => (1 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact cutoffP_eq_one hs.le

/-- `deriv cutoffP` is eventually `0` in a neighborhood of any `t < 1`: shrink to where
    `cutoffP` itself is eventually `0` (`cutoffP_eventuallyEq_zero_of_lt`), then differentiate. -/
private lemma derivCutoffP_eventuallyEq_zero_of_lt {t : ℝ} (ht : t < 1) :
    deriv cutoffP =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  rw [(cutoffP_eventuallyEq_zero_of_lt hs).deriv_eq, deriv_const']

/-- `deriv cutoffP` is eventually `0` in a neighborhood of any `2 < t`: shrink to where
    `cutoffP` itself is eventually `1` (`cutoffP_eventuallyEq_one_of_gt`), then differentiate. -/
private lemma derivCutoffP_eventuallyEq_zero_of_gt {t : ℝ} (ht : 2 < t) :
    deriv cutoffP =ᶠ[nhds t] (fun _ => (0 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [(cutoffP_eventuallyEq_one_of_gt hs).deriv_eq, deriv_const']

/-- The derivative of the profile is supported in `[1,2]`. -/
lemma deriv_cutoffP_support : Function.support (deriv cutoffP) ⊆ Set.Icc 1 2 := by
  intro t ht
  by_contra hmem
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  apply ht
  rcases hmem with h | h
  · rw [(cutoffP_eventuallyEq_zero_of_lt h).deriv_eq, deriv_const']
  · rw [(cutoffP_eventuallyEq_one_of_gt h).deriv_eq, deriv_const']

/-- The derivative of `cutoffP` has compact support. -/
lemma hasCompactSupport_deriv_cutoffP : HasCompactSupport (deriv cutoffP) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1:ℝ)) (b := 2))
    deriv_cutoffP_support

/-- A continuous, compactly supported function on `ℝ` is globally bounded. -/
private lemma bounded_of_continuous_hasCompactSupport {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_supp : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |f t| ≤ M := by
  obtain ⟨M, hM⟩ := hf_cont.bounded_above_of_compact_support hf_supp
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  have := hM t
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- The profile derivative is globally bounded. -/
lemma deriv_cutoffP_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv cutoffP t| ≤ M :=
  bounded_of_continuous_hasCompactSupport deriv_cutoffP_continuous hasCompactSupport_deriv_cutoffP

/-- The second derivative of `cutoffP` is continuous. -/
lemma deriv2_cutoffP_continuous : Continuous (deriv (deriv cutoffP)) :=
  ((cutoffP_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).deriv' (n := 2)).continuous_deriv
    (by norm_num)

/-- The second derivative of the profile is supported in `[1,2]`. -/
lemma deriv2_cutoffP_support : Function.support (deriv (deriv cutoffP)) ⊆ Set.Icc 1 2 := by
  intro t ht
  by_contra hmem
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
  apply ht
  rcases hmem with h | h
  · rw [(derivCutoffP_eventuallyEq_zero_of_lt h).deriv_eq, deriv_const']
  · rw [(derivCutoffP_eventuallyEq_zero_of_gt h).deriv_eq, deriv_const']

/-- The second derivative of `cutoffP` has compact support. -/
lemma hasCompactSupport_deriv2_cutoffP : HasCompactSupport (deriv (deriv cutoffP)) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1:ℝ)) (b := 2))
    deriv2_cutoffP_support

/-- The profile second derivative is globally bounded. -/
lemma deriv2_cutoffP_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv (deriv cutoffP) t| ≤ M :=
  bounded_of_continuous_hasCompactSupport deriv2_cutoffP_continuous hasCompactSupport_deriv2_cutoffP

end Spectra.QuantumMechanics.Hydrogen

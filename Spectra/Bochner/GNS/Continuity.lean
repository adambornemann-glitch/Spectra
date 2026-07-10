/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.PositiveDefinite.Basic

/-!
# Continuity Propagation for Positive-Definite Functions

Bochner's theorem needs a positive-definite, Hermitian-symmetric function `f : ℝ → ℂ` to be
continuous everywhere, but the hypothesis that is easy to state and to check (e.g. for a
Fourier–Stieltjes transform) is only continuity **at `0`**. This file proves that the weaker
hypothesis already forces the stronger conclusion.

The mechanism is a Cauchy–Schwarz-type oscillation bound for positive-definite kernels:

`‖f(s) - f(t)‖² ≤ 2 · (f 0).re · pdVariance f (s - t)`,

where `pdVariance f h = (f 0).re - (f h).re` (`Spectra.PositiveDefinite.pdVariance`) is the
"variance" that continuity-at-`0` is already known to send to `0`. Since the right-hand side does
not depend on `t`, this gives *uniform* continuity of `f` from mere continuity of `pdVariance f`
at `0`.

## Main definitions

* `IsContinuous`: bundles positive-definiteness, Hermitian symmetry, and continuity at `0` into
  the single hypothesis Bochner's theorem needs.

## Main statements

* `pd_oscillation_sq`: the oscillation bound
  `‖f(s) - f(t)‖² ≤ 2 · (f 0).re · pdVariance f (s - t)`.
* `IsContinuous.continuity`: `IsContinuous f` implies `Continuous f`.

## References

* Rudin, *Functional Analysis*, 2nd ed., §1.4.3 (Properties of positive-definite functions)
* Reed–Simon, *Methods of Modern Mathematical Physics I*, §VII (Bochner's lemma)
-/

open Complex Filter Topology MeasureTheory
open Spectra.PositiveDefinite

namespace Spectra.Bochner

variable {f : ℝ → ℂ}

/-- **The hypothesis bundle for Bochner's theorem.**

A positive-definite, Hermitian-symmetric `f : ℝ → ℂ` that is continuous at `0`. This is the
minimal hypothesis from which `IsContinuous.continuity` below derives continuity of `f`
everywhere, so it is the one hypothesis threaded through the rest of the Bochner pipeline. -/
structure IsContinuous (f : ℝ → ℂ) : Prop where
  /-- `f` is positive-definite. -/
  pd : IsPositiveDefinite f
  /-- `f` is Hermitian-symmetric: `f(-t) = conj(f(t))`. -/
  hermitian : IsHermitian f
  /-- `f` is continuous at the single point `0`. -/
  continuous_at_zero : ContinuousAt f 0

/-- The sharp norm bound `‖f(t)‖ ≤ (f 0).re`, specialized to `IsContinuous` bundles. -/
lemma IsContinuous.norm_bound (hf : IsContinuous f) (t : ℝ) :
    ‖f t‖ ≤ (f 0).re :=
  pd_hermitian_norm_bound hf.pd hf.hermitian t

/-- `(f 0).re` is non-negative, specialized to `IsContinuous` bundles. -/
lemma IsContinuous.at_zero_nonneg (hf : IsContinuous f) :
    0 ≤ (f 0).re :=
  pd_at_zero_nonneg hf.pd

/-- `f 0` is real, specialized to `IsContinuous` bundles. -/
lemma IsContinuous.at_zero_real (hf : IsContinuous f) :
    (f 0).im = 0 :=
  hermitian_at_zero_im hf.hermitian

/-- The PD variance `pdVariance f` tends to `0` at `0`, specialized to `IsContinuous` bundles. -/
lemma IsContinuous.variance_tendsto (hf : IsContinuous f) :
    Filter.Tendsto (pdVariance f) (𝓝 0) (𝓝 0) :=
  pdVariance_tendsto_zero hf.continuous_at_zero

/-- **Oscillation bound** (Cauchy–Schwarz for PD kernels):
`‖f(s) - f(t)‖² ≤ 2 · f(0).re · pdVariance f (s - t)`.

Proved via the 3-point PD condition at `{0, s, t}` with coefficients
`c = [-conj(f s - f t), (f 0).re, -(f 0).re]`; the resulting 9-term quadratic form factors as
`p · (2 p V - ‖w‖²) ≥ 0` where `p = (f 0).re`, `w = f s - f t`,
and `V = pdVariance f (s - t)`. -/
lemma pd_oscillation_sq (hf : IsPositiveDefinite f) (hH : IsHermitian f) (s t : ℝ) :
    ‖f s - f t‖ ^ 2 ≤ 2 * (f 0).re * pdVariance f (s - t) := by
  set p := (f 0).re with hp_def
  set w := f s - f t with hw_def
  -- Degenerate case: p = 0 forces f s = f t = 0 (norm bound), so both sides vanish.
  by_cases hp : p = 0
  · have hs : f s = 0 :=
      norm_le_zero_iff.mp (by nlinarith [pd_hermitian_norm_bound hf hH s, norm_nonneg (f s)])
    have ht : f t = 0 :=
      norm_le_zero_iff.mp (by nlinarith [pd_hermitian_norm_bound hf hH t, norm_nonneg (f t)])
    simp [hw_def, hs, ht, pdVariance, hp_def]
    simp_all only [sub_self, mul_zero, zero_sub, mul_neg, zero_mul, neg_zero, Std.le_refl, p, w]
  -- Main case: p > 0.
  have hp_pos : 0 < p := lt_of_le_of_ne (pd_at_zero_nonneg hf) (Ne.symm hp)
  -- 3-point PD with c = ![-conj(w), p, -p].
  have hpd := hf 3 ![0, s, t] ![-(starRingEnd ℂ w), (↑p : ℂ), -(↑p : ℂ)]
  -- Expand the 3×3 double sum over `Fin 3` and reduce the `![...]` vector accesses.
  simp only [Fin.sum_univ_three] at hpd
  have hv0 : (![0, s, t] : Fin 3 → ℝ) 2 = t := rfl
  have hv1 : (![-(starRingEnd ℂ w), (↑p : ℂ), -(↑p : ℂ)] : Fin 3 → ℂ) 2
      = -(↑p : ℂ) := rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hv0, hv1] at hpd
  simp only [sub_self, sub_zero, zero_sub] at hpd
  -- Simplify conjugates: conj(-conj(w)) = -w, via `starRingEnd_self_apply`.
  simp only [map_neg, Complex.conj_ofReal, starRingEnd_self_apply] at hpd
  -- Apply Hermitian symmetry to fold f(-s), f(-t), f(t-s) back to conj f(s), conj f(t), f(s-t).
  rw [hH s, hH t, show t - s = -(s - t) from by ring, hH (s - t)] at hpd
  -- Replace f(0) by the real number ↑p.
  rw [hermitian_at_zero_ofReal hH] at hpd
  -- Split every term into real/imaginary components.
  simp only [map_sub, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
    Complex.sub_im, Complex.mul_im, Complex.neg_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, hw_def] at hpd
  -- ‖w‖² in components.
  have hnsq : ‖w‖ ^ 2 = ((f s).re - (f t).re) ^ 2 + ((f s).im - (f t).im) ^ 2 := by
    rw [hw_def, ← normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; ring
  -- Factor: the PD sum equals p · (2pV − ‖w‖²).
  suffices h : 0 ≤ p * (2 * p * (p - (f (s - t)).re) -
      (((f s).re - (f t).re) ^ 2 + ((f s).im - (f t).im) ^ 2)) by
    -- Extract: p > 0 and p · X ≥ 0 implies X ≥ 0.
    have hX : 0 ≤ 2 * p * (p - (f (s - t)).re) -
        (((f s).re - (f t).re) ^ 2 + ((f s).im - (f t).im) ^ 2) := by
      rcases mul_nonneg_iff.mp h with ⟨_, hh⟩ | ⟨hp_le, _⟩
      · exact hh
      · exact absurd hp_le (not_le.mpr hp_pos)
    unfold pdVariance; linarith [hnsq]
  convert hpd using 1
  simp only [← hp_def]
  ring_nf

/-- PD + Hermitian + continuous at `0` implies continuous everywhere.

Key estimate: `‖f(t+h) - f(t)‖² ≤ 2·(f 0).re·((f 0).re - Re(f(h)))`. The right-hand side
tends to `0` as `h → 0` by `continuous_at_zero`, uniformly in `t`, which gives (uniform)
continuity of `f`. -/
lemma IsContinuous.continuity (hf : IsContinuous f) : Continuous f := by
  rw [continuous_iff_continuousAt]; intro t
  rw [Metric.continuousAt_iff]; intro ε hε
  have hp_nn := hf.at_zero_nonneg
  set p := (f 0).re
  -- pdVariance f → 0 at 0.
  have hV := hf.variance_tendsto
  -- Choose δ: |h| < δ → pdVariance f h < ε²/(2p + 1).
  have hε' : (0 : ℝ) < ε ^ 2 / (2 * p + 1) := by positivity
  rw [Metric.tendsto_nhds] at hV
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.eventually_nhds_iff.mp (hV _ hε')
  refine ⟨δ, hδ, fun x hx => ?_⟩
  -- pdVariance f (x - t) < ε²/(2p + 1).
  have h_var : pdVariance f (x - t) < ε ^ 2 / (2 * p + 1) := by
    have h1 := hδ_spec (show dist (x - t) 0 < δ by rwa [Real.dist_eq, sub_zero, ← Real.dist_eq])
    rwa [Real.dist_eq, sub_zero,
         abs_of_nonneg (pdVariance_nonneg hf.pd hf.hermitian _)] at h1
  rw [Complex.dist_eq]
  -- Assemble the bound chain.
  have h_osc := pd_oscillation_sq hf.pd hf.hermitian x t
  have h_Vnn := pdVariance_nonneg hf.pd hf.hermitian (x - t)
  -- Clear denominator: (2p + 1) · V(x-t) < ε².
  have h_bound : (2 * p + 1) * pdVariance f (x - t) < ε ^ 2 := by
    rwa [lt_div_iff₀ (show (0 : ℝ) < 2 * p + 1 by linarith), mul_comm] at h_var
  -- Chain: ‖f x - f t‖² ≤ 2pV ≤ (2p+1)V < ε², using V ≥ 0.
  have h_sq : ‖f x - f t‖ ^ 2 < ε ^ 2 := by nlinarith
  -- ‖·‖² < ε² with ε > 0 gives ‖·‖ < ε.
  by_contra h_ge
  push Not at h_ge
  exact absurd h_sq (not_lt.mpr (sq_le_sq' (by linarith [norm_nonneg (f x - f t)]) h_ge))

end Spectra.Bochner

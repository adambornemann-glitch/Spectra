/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.PreHilbert.Cyclic

/-!
# The Norm Estimate Driving Strong Continuity

This file proves the norm-squared estimate that ultimately drives strong continuity of the
GNS representation: `pdInner_translate_diff_cyclic` computes
`⟨U(t)ξ-ξ, U(t)ξ-ξ⟩ = 2Re f(0) - f(t) - conj(f(t))`, `pdInner_translate_diff_re` takes its
real part, and `pdInner_translate_diff_eq_variance` identifies that real part with
`2 · pdVariance f t`.

## Main statements

* `pdInner_translate_diff_cyclic`: `⟨U(t)ξ-ξ, U(t)ξ-ξ⟩ = 2Re(f(0)) - f(t) - conj(f(t))`
* `pdInner_translate_diff_re`: the real part, `2·(Re f(0) - Re f(t))`
* `pdInner_translate_diff_eq_variance`: identified with `2 · pdVariance f t`
  (`pdVariance` is defined in `Spectra/PositiveDefinite/Basic.lean` and feeds
  `Bochner/GNS/Continuity.lean`'s continuity-propagation argument)

## References

* `pdVariance f t = f(0).re - Re(f(t))` tends to `0` as `t → 0` exactly when `f` is
  continuous at `0`; see `Spectra.PositiveDefinite.pdVariance_tendsto_zero`.
-/
open Spectra.PositiveDefinite

namespace Spectra.Bochner.GNS

-- §8  The norm estimate

/-- The "norm squared" of a translate difference:
`‖U(t)ξ - ξ‖² = 2 Re(f(0)) - 2 Re(f(t))`.

This is the estimate that will give strong continuity once we
pass to the completion. The RHS → 0 as t → 0 by `ContinuousAt f 0`. -/
lemma pdInner_translate_diff_cyclic {f : ℝ → ℂ} (hH : IsHermitian f) (t : ℝ) :
    pdInner f (translate t cyclicVector - cyclicVector)
              (translate t cyclicVector - cyclicVector) =
    2 * (f 0).re - f t - starRingEnd ℂ (f t) := by
  set ξ := cyclicVector
  set Uξ := translate t ξ
  have h_ξξ : pdInner f ξ ξ = f 0 := by
    simp only [ξ, cyclicVector, pdInner_single_one, sub_self]
  rw [pdInner_sub_left hH, pdInner_sub_right, pdInner_sub_right, pdInner_translate t ξ ξ,
      pdInner_conj_symm hH ξ Uξ, pdInner_cyclic f t, h_ξξ,
      hermitian_at_zero_ofReal hH]
  ring_nf; simp only [Complex.ofReal_re]
  -- Closes the remaining real-linear rearrangement of the `2·Re(f 0) - f t - conj(f t)` sides.
  grind

/-- Corollary: the "norm squared" of `U(t)ξ - ξ` is real and non-negative,
and equals `2(Re(f(0)) - Re(f(t)))`.

This is the form most directly useful for strong continuity:
it tends to 0 as t → 0 iff f is continuous at 0. -/
lemma pdInner_translate_diff_re {f : ℝ → ℂ} (hH : IsHermitian f) (t : ℝ) :
    (pdInner f (translate t cyclicVector - cyclicVector)
              (translate t cyclicVector - cyclicVector)).re =
    2 * ((f 0).re - (f t).re) := by
  rw [pdInner_translate_diff_cyclic hH t]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
             Complex.ofReal_im, Complex.conj_re]
  ring_nf; simp only [Complex.re_ofNat, sub_left_inj]
  -- Closes the remaining real-linear rearrangement matching `.re` on both sides.
  grind

/-- The difference norm is controlled by the variance `pdVariance`:

  Re⟨U(t)ξ - ξ, U(t)ξ - ξ⟩ = 2 · pdVariance f t

where `pdVariance f t = f(0).re - Re(f(t))` is from `Continuity.lean`.
This connects directly to the oscillation estimates already proved. -/
theorem pdInner_translate_diff_eq_variance {f : ℝ → ℂ} (hH : IsHermitian f) (t : ℝ) :
    (pdInner f (translate t cyclicVector - cyclicVector)
              (translate t cyclicVector - cyclicVector)).re =
    2 * pdVariance f t := by
  rw [pdInner_translate_diff_re hH]
  rfl

end Spectra.Bochner.GNS

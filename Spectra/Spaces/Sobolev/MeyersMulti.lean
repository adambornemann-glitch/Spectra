/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.Mollification
import Spectra.Spaces.Sobolev.MeyersCommon

/-!
# Meyers–Serrin approximation (all three directions at once)

The multi-direction, vectorized instance of the Meyers–Serrin "H = W" approximation: any
`f : (l2Rn d)` with weak derivatives `dg i` in *every* coordinate direction `i : Fin d` can be
approximated by a *single* smooth, compactly supported `φ` that is simultaneously close to `f`
in the L² norm and close to every `dg i` in the corresponding weak-derivative norm. This is the
form actually needed to build `H¹`/`H²` elements as genuine smooth functions, and is the version
called by `DensityResults.lean`, `Embeddings.lean`, and the Hydrogen/Hardy-inequality
developments.

## Main definitions and results

* `truncation_approx_multi` (`private`): the multi-direction truncation step — cuts `f` and all
  three `dg i` to compact support with one shared cutoff, within `ε` of `(f, dg)` in all four
  norms simultaneously.
* `meyers_serrin_approx_multi`: the headline result — chains `truncation_approx_multi` with
  `mollify_compactly_supported_multi` to produce a smooth, compactly supported `φ` within `ε` of
  `f` and of every `∂ᵢφ` relative to `dg i`.

## Implementation notes

Both steps hinge on the same trick: a *single* cutoff `χ` (respectively, a single mollifying bump)
works uniformly across all three directions, because the cutoff acts on `f` itself, not on the
individual derivatives — so `truncation_approx_multi` needs exactly one radius `R` and one
cutoff `χ_R`, shared across `i = 0, 1, 2`. What *does* need to be `i`-indexed is the derivative
side: `∂ᵢχ_R` differs by direction, so the per-direction truncated derivative `dh_R i` and its
L²-tail radius `R_dg i` form genuine `Fin d`-indexed families, even though the cutoff itself does
not. `truncation_approx_multi` is the `ι := Fin d`, `dir := id` specialization of the shared
cutoff-truncation construction `truncation_approx_family` (`MeyersCommon.lean`), which also
powers the single-direction case `truncation_approx` in `MeyersSerrin.lean` (`ι := Unit`) — so the
cutoff/budget argument is maintained in exactly one place rather than twice. Likewise,
`mollify_compactly_supported_multi` is the `ι := Fin d`, `dir := id` specialization of the shared
`mollify_compactly_supported_family` construction (`Mollification.lean`), which also powers the
single-direction case `mollify_compactly_supported` in `MeyersSerrin.lean`.

## References

* [Meyers, Serrin, *H = W*][meyers1964]
* [Adams, Fournier, *Sobolev Spaces*][adams2003]
-/

open MeasureTheory
open scoped ContDiff

namespace Spectra.Sobolev

variable {d : ℕ}

/-- **Multi-direction truncation step of Meyers-Serrin**: simultaneously truncate
    `f` and all three weak derivatives using a single cutoff `χ`.
    This is the `ι := Fin d`, `dir := id` specialization of the shared
    `truncation_approx_family` cutoff construction (`MeyersCommon.lean`); see
    `truncation_approx` in `MeyersSerrin.lean` for the single-direction sibling
    (`ι := Unit`). The function-side `h_R` is shared across all directions,
    only the derivative-side `dh_R i` depends on `i`. -/
private lemma truncation_approx_multi [NeZero d]
    (f : (l2Rn d)) (dg : Fin d → (l2Rn d))
    (h_dg : ∀ i, HasWeakDerivative f i (dg i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (h_R : Rn d → ℂ) (dh_R : Fin d → Rn d → ℂ)
      (hh : MemLp h_R 2 volume) (hdh : ∀ i, MemLp (dh_R i) 2 volume),
      HasCompactSupport h_R ∧ (∀ i, HasCompactSupport (dh_R i)) ∧
      (∀ i, HasWeakDerivative (hh.toLp h_R) i ((hdh i).toLp (dh_R i))) ∧
      ‖f - hh.toLp h_R‖ < ε ∧ ∀ i, ‖dg i - (hdh i).toLp (dh_R i)‖ < ε :=
  truncation_approx_family (ι := Fin d) id f dg h_dg ε hε

/-- **Multi-direction Meyers-Serrin**: `f` with weak derivatives `dg i` in every direction
    `i : Fin d` can be simultaneously approximated by a single smooth, compactly supported `φ` in
    all four norms at once — `φ` is `ε`-close to `f`, and every classical partial `∂ᵢφ` is
    `ε`-close to the corresponding `dg i`, for the *same* `φ` and the *same* `ε`. As in the
    single-direction case, the proof is truncate-then-mollify: `truncation_approx_multi` first
    cuts `(f, dg)` down to a compactly supported family within `ε/2` in all four norms, then
    `mollify_compactly_supported_multi` convolves it with a single smooth bump to land a smooth
    `φ` within a further `ε/2`; the triangle inequality combines the two `ε/2` bounds into the
    single `ε` bounds stated here. -/
lemma meyers_serrin_approx_multi [NeZero d]
    (f : (l2Rn d)) (dg : Fin d → (l2Rn d))
    (h_dg : ∀ i, HasWeakDerivative f i (dg i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : Rn d → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ),
      ‖f - (memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ‖ < ε ∧
      ∀ i, ‖dg i - (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  -- Step 1: multi-truncation gives compactly supported intermediates.
  obtain ⟨h_R, dh_R, hh, hdh, hh_supp, hdh_supp, h_wk, hf_close, hdg_close⟩ :=
    truncation_approx_multi f dg h_dg (ε / 2) hε2
  -- Step 2: a single bump convolution mollifies them all simultaneously.
  obtain ⟨φ, hφ, hφ_supp, hφ_close, hdφ_close⟩ :=
    mollify_compactly_supported_multi h_R dh_R hh hdh hh_supp hdh_supp h_wk (ε / 2) hε2
  refine ⟨φ, hφ, hφ_supp, ?_, ?_⟩
  · -- ‖f - toLp φ‖ ≤ ‖f - toLp h_R‖ + ‖toLp h_R - toLp φ‖ < ε/2 + ε/2 = ε
    calc ‖f - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖
        ≤ ‖f - hh.toLp h_R‖ +
          ‖hh.toLp h_R -
            (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖ := by
          have h_eq : f - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ =
              (f - hh.toLp h_R) +
              (hh.toLp h_R -
                (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ) := by abel
          rw [h_eq]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hf_close hφ_close
      _ = ε := add_halves ε
  · -- Per direction: ‖dg i - ∂ᵢφ‖ ≤ ‖dg i - toLp (dh_R i)‖ + ‖toLp (dh_R i) - ∂ᵢφ‖
    intro i
    calc ‖dg i - (memLp_partialDeriv φ i hφ hφ_supp).toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖
        ≤ ‖dg i - (hdh i).toLp (dh_R i)‖ +
          ‖(hdh i).toLp (dh_R i) -
            (memLp_partialDeriv φ i hφ hφ_supp).toLp
              (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ := by
          have h_eq : dg i - (memLp_partialDeriv φ i hφ hφ_supp).toLp
              (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) =
              (dg i - (hdh i).toLp (dh_R i)) +
              ((hdh i).toLp (dh_R i) - (memLp_partialDeriv φ i hφ hφ_supp).toLp
                (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) := by abel
          rw [h_eq]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hdg_close i) (hdφ_close i)
      _ = ε := add_halves ε

end Spectra.Sobolev

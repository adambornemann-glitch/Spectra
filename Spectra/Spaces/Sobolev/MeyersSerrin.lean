/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.Mollification
import Spectra.Spaces.Sobolev.MeyersCommon

/-!
# Meyers–Serrin approximation (single direction)

The single-direction instance of the Meyers–Serrin "H = W" approximation: any `g : (l2Rn d)`
with a weak derivative `dg` in one coordinate direction `i` can be approximated, simultaneously
in the L² norm and in the direction-`i` weak-derivative norm, by a genuinely smooth,
compactly supported function.

## Main results

* `meyers_serrin_approx`: given `g` and its weak derivative `dg` in direction `i`, produces a
  smooth, compactly supported `φ` with `‖g - φ‖ < ε` and `‖dg - ∂ᵢφ‖ < ε` simultaneously, for any
  `ε > 0`.

## Implementation notes

The proof is a two-step architecture, truncate then mollify:

1. **Truncate** (`truncation_approx`, `private`): multiply `g` by a smooth cutoff `χ_R` to land a
   compactly supported pair `(h_R, dh_R)` still within `ε` of `(g, dg)` in both norms. This is the
   `ι := Unit` specialization of the shared cutoff construction
   `Spectra.Sobolev.truncation_approx_family` (`MeyersCommon.lean`), which also powers the
   three-direction sibling `truncation_approx_multi` in `MeyersMulti.lean`.
2. **Mollify** (`mollify_compactly_supported`, `Mollification.lean`): convolve the compactly
   supported truncation with a smooth bump to land a genuinely smooth `φ`, still within `ε` of the
   truncation in both norms. This is likewise the `ι := Unit` specialization of the shared
   `mollify_compactly_supported_family` construction (`Mollification.lean`), which also powers
   the three-direction sibling `mollify_compactly_supported_multi` in `MeyersMulti.lean`.

The triangle inequality then combines the two `ε/2` bounds into a single `ε` bound for `g` and for
`dg`, closing `meyers_serrin_approx`.

## References

* [Meyers, Serrin, *H = W*][meyers1964]
* [Adams, Fournier, *Sobolev Spaces*][adams2003]
-/

open MeasureTheory
open scoped ContDiff

namespace Spectra.Sobolev

variable {d : ℕ}

/-- Truncation step of Meyers-Serrin: multiply `g` by a smooth cutoff `χ_R` to get compactly
    supported approximations `(h_R, dh_R)` of `(g, dg)` preserving weak derivative structure
    (`χ_R · g` has weak derivative `χ_R · dg + g · ∂ᵢχ_R` by `hasWeakDerivative_smul_smooth`).
    The radius `R` is chosen large enough to make four independent error contributions each
    less than `ε / 4`: the L²-tail of `g` past radius `R`, the L²-tail of `dg` past radius `R`,
    and — because `∂ᵢχ_R` is not literally zero, only bounded by `M / R` for a cutoff-independent
    constant `M` — the two pieces of the Leibniz cross-term `g · ∂ᵢχ_R`, whose L² norm is
    controlled by `(M / R) · ‖g‖`. Driving `R → ∞` sends `(M / R) · ‖g‖ → 0`, which is the
    mechanism that makes this cross-term (rather than just the two genuine tails) negligible too.
    The single direction `i` is the `ι := Unit` specialization of the shared
    `truncation_approx_family` cutoff construction (`MeyersCommon.lean`), which carries out this
    whole argument once, generically in the index set; see `truncation_approx_multi` in
    `MeyersMulti.lean` for the `Fin d` sibling. We unpack the trivial `Unit`-indexed output
    (`h_R`/`dh_R`/… at the single point `()`) back into the bare, un-indexed shape this lemma has
    always had. -/
private lemma truncation_approx (i : Fin d) (g dg : (l2Rn d))
    (h_dg : HasWeakDerivative g i dg) (ε : ℝ) (hε : 0 < ε) :
    ∃ (h_R : Rn d → ℂ) (dh_R : Rn d → ℂ)
      (hh : MemLp h_R 2 volume) (hdh : MemLp dh_R 2 volume),
      HasCompactSupport h_R ∧ HasCompactSupport dh_R ∧
      HasWeakDerivative (hh.toLp h_R) i (hdh.toLp dh_R) ∧
      ‖g - hh.toLp h_R‖ < ε ∧ ‖dg - hdh.toLp dh_R‖ < ε := by
  obtain ⟨h_R, dh_R, hh, hdh, hh_supp, hdh_supp, h_wk, hg_close, hdg_close⟩ :=
    truncation_approx_family (ι := Unit) (fun _ => i) g (fun _ => dg)
      (fun _ => h_dg) ε hε
  exact ⟨h_R, dh_R (), hh, hdh (), hh_supp, hdh_supp (), h_wk (), hg_close, hdg_close ()⟩

/-- **Meyers-Serrin approximation**: `g` with weak derivative `dg` in direction `i` can be
    simultaneously approximated by a smooth, compactly supported `φ` in both norms — i.e. `φ`
    is `ε`-close to `g` in the ambient `L²` norm, and its classical partial derivative `∂ᵢφ` is
    `ε`-close to `dg` in the same `L²` norm, for the *same* `φ` and the *same* `ε`. The proof is
    the two-step truncate-then-mollify architecture: `truncation_approx` first cuts `(g, dg)`
    down to a compactly supported pair within `ε/2` in both norms, then
    `mollify_compactly_supported` convolves that pair with a smooth bump to land a genuinely
    smooth `φ` within a further `ε/2` of the truncation in both norms; the triangle inequality
    combines the two `ε/2` bounds into the single `ε` bounds stated here. -/
lemma meyers_serrin_approx (i : Fin d) (g dg : (l2Rn d))
    (h_dg : HasWeakDerivative g i dg) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : Rn d → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ),
      ‖g - (memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ‖ < ε ∧
      ‖dg - (memLp_partialDeriv φ i hφ hsupp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  -- Step 1: Truncate g to get compactly supported approximation
  obtain ⟨h_R, dh_R, hh, hdh, hh_supp, hdh_supp, h_wk, hg_close, hdg_close⟩ :=
    truncation_approx i g dg h_dg (ε / 2) hε2
  -- Step 2: Mollify the truncation to get smooth c.s. approximation
  obtain ⟨φ, hφ, hφ_supp, hφ_close, hdφ_close⟩ :=
    mollify_compactly_supported i h_R dh_R hh hdh hh_supp hdh_supp h_wk (ε / 2) hε2
  -- Step 3: Triangle inequality assembles the two ε/2 bounds
  refine ⟨φ, hφ, hφ_supp, ?_, ?_⟩
  · -- ‖g - φ‖ ≤ ‖g - h_R‖ + ‖h_R - φ‖ < ε/2 + ε/2 = ε
    calc ‖g - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖
        ≤ ‖g - hh.toLp h_R‖ +
          ‖hh.toLp h_R - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ‖ := by
          have : g - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ =
            (g - hh.toLp h_R) +
            (hh.toLp h_R - (memLp_of_smooth_compactSupport φ hφ hφ_supp).toLp φ) := by abel
          rw [this]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hg_close hφ_close
      _ = ε := add_halves ε
  · -- ‖dg - ∂ᵢφ‖ ≤ ‖dg - dh_R‖ + ‖dh_R - ∂ᵢφ‖ < ε/2 + ε/2 = ε
    calc ‖dg - (memLp_partialDeriv φ i hφ hφ_supp).toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖
        ≤ ‖dg - hdh.toLp dh_R‖ +
          ‖hdh.toLp dh_R - (memLp_partialDeriv φ i hφ hφ_supp).toLp
            (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))‖ := by
          have : dg - (memLp_partialDeriv φ i hφ hφ_supp).toLp
              (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) =
            (dg - hdh.toLp dh_R) +
            (hdh.toLp dh_R - (memLp_partialDeriv φ i hφ hφ_supp).toLp
              (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) := by abel
          rw [this]; exact norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdg_close hdφ_close
      _ = ε := add_halves ε

end Spectra.Sobolev

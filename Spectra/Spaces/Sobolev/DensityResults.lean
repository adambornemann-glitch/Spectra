/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.IntegrationByParts
import Spectra.Spaces.Sobolev.MeyersMulti
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Density of smooth compactly supported functions in the Sobolev scale

This file assembles the Meyers–Serrin approximation machinery (`MeyersSerrin.lean`,
`MeyersMulti.lean`) and the `L²` test-function density chain (`dense_test_functions_L2`,
from `Density.lean`) into the two density results the operator theory needs to build `-Δ`
with a core: `H²(ℝ³)` is dense in `L²(ℝ³)`, and `C_c^∞(ℝ³)` is dense in `H¹(ℝ³)`.

## Main results

* `sobolevH2_dense`: `H²(ℝ³)` is dense in `L²(ℝ³)`.
* `smooth_compactly_supported_dense_H1`: `C_c^∞(ℝ³)` is dense in `H¹(ℝ³)` — every `f ∈ H¹(ℝ³)`
  is `ε`-approximated by a smooth, compactly supported `g ∈ H²(ℝ³)`, simultaneously in the
  ambient `L²` norm and in *every* weak-gradient component (`‖f - g‖ < ε` together with
  `‖∂ᵢf - ∂ᵢg‖ < ε` for each `i`), not as a single combined Sobolev norm.

Both are instances of the classical Meyers–Serrin "H = W" theorem: for domains with no
boundary regularity to worry about (here, all of `ℝ³`), the space of functions with weak
derivatives coincides with the closure of smooth functions in the corresponding Sobolev norm.

## Implementation notes

Density is proved via `dense_test_functions_L2` composed with Meyers–Serrin, not via a
mollifier argument run directly against an arbitrary `H¹`/`H²` element. Concretely:

* `hasWeakDerivative_of_smooth_compactSupport` identifies the classical partial derivative
  `∂ᵢφ` of a smooth, compactly supported `φ` with the weak derivative of its `L²` class, via
  Fréchet-derivative integration by parts
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).
* `smooth_compactSupport_memSobolevH2` upgrades this to full `H²` membership (both a first
  weak derivative in every direction and a second weak derivative in every pair of
  directions).
* `sobolevH2_dense` transports `H²`-membership along `dense_test_functions_L2`: every point of
  the ambient `L²` test-function-dense set is already smooth and compactly supported, hence
  (by the previous bullet) already in `H²`.
* `smooth_compactly_supported_dense_H1` instead starts from an arbitrary `f ∈ H¹(ℝ³)`, invokes
  the three-direction Meyers–Serrin approximation `meyers_serrin_approx_multi` to produce a
  smooth compactly supported approximant `φ` within `ε` of `f` and of every weak-gradient
  component, and closes with weak-derivative uniqueness (`hasWeakDerivative_unique`) to
  identify `φ`'s classical partial derivatives with `g`'s weak gradient.

This two-stage route (test-function density first, Meyers–Serrin second) is what lets both
theorems reuse the same smoothing machinery instead of re-deriving a mollifier argument for
each Sobolev order.

## References

* [Meyers, Serrin, *H = W*][meyers1964]
* [Adams, Fournier, *Sobolev Spaces*][adams2003]
-/

open MeasureTheory Complex
open scoped Pointwise ContDiff

namespace Spectra.Sobolev

variable {d : ℕ}

/-- For smooth compactly supported `φ`, the classical partial derivative `∂ᵢφ`
    is the weak derivative of `hmem.toLp φ` in direction `i`. -/
lemma hasWeakDerivative_of_smooth_compactSupport
    (φ : Rn d → ℂ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    {i : Fin d}
    (hmem : MemLp φ 2 (volume : Measure (Rn d)))
    (hdmem : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2
      (volume : Measure (Rn d))) :
    HasWeakDerivative (hmem.toLp φ) i
      (hdmem.toLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
  intro ψ hψ_s _hψ_c
  -- Continuities & compact supports
  have hφ_cont  : Continuous φ := hφ.continuous
  have hψ_cont  : Continuous ψ := hψ_s.continuous
  have hdφ_cont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (contDiff_partialDeriv φ i hφ).continuous
  have hdψ_cont : Continuous (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) :=
    (contDiff_partialDeriv ψ i hψ_s).continuous
  have hdφ_supp : HasCompactSupport
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    hasCompactSupport_partialDeriv φ i hsupp
  -- Integrabilities for IBP
  have hint_f'g : Integrable
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1) * ψ x) volume :=
    (hdφ_cont.mul hψ_cont).integrable_of_hasCompactSupport hdφ_supp.mul_right
  have hint_fg' : Integrable
      (fun x => φ x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) volume :=
    (hφ_cont.mul hdψ_cont).integrable_of_hasCompactSupport hsupp.mul_right
  have hint_fg : Integrable (fun x => φ x * ψ x) volume :=
    (hφ_cont.mul hψ_cont).integrable_of_hasCompactSupport hsupp.mul_right
  -- Differentiability everywhere
  have hφ_diff  : Differentiable ℝ φ :=
    hφ.differentiable  (by exact_mod_cast ENat.top_ne_zero)
  have hψ_diff  : Differentiable ℝ ψ :=
    hψ_s.differentiable (by exact_mod_cast ENat.top_ne_zero)
  -- Mathlib's IBP for Fréchet derivatives along a direction
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Rn d))) (𝕜 := ℂ)
    (v := (EuclideanSpace.single i (1 : ℝ)))
    hint_f'g hint_fg' hint_fg
    (fun x _ => hφ_diff x) (fun x _ => hψ_diff x)
  -- Bridge L² coercions to bare functions
  have h_lhs : ∫ x, (hmem.toLp φ : Rn d → ℂ) x *
        fderiv ℝ ψ x (EuclideanSpace.single i 1) =
      ∫ x, φ x * fderiv ℝ ψ x (EuclideanSpace.single i 1) :=
    integral_congr_ae (hmem.coeFn_toLp.mono fun x hx => by simp [hx])
  have h_rhs : ∫ x,
        (hdmem.toLp (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) : Rn d → ℂ) x *
        ψ x = ∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) * ψ x :=
    integral_congr_ae (hdmem.coeFn_toLp.mono fun x hx => by simp [hx])
  rw [h_lhs, h_rhs]
  exact hibp

/-- Smooth compactly supported functions belong to H². -/
lemma smooth_compactSupport_memSobolevH2 (φ : Rn d → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hmem : MemLp φ 2 (volume : Measure (Rn d))) :
    MemSobolevH2 (MemLp.toLp φ hmem) := by
  refine ⟨?h1, ?h2⟩
  case h1 =>
    intro i
    exact ⟨_, hasWeakDerivative_of_smooth_compactSupport φ hφ hsupp
      hmem (memLp_partialDeriv φ i hφ hsupp)⟩
  case h2 =>
    intro i j
    have hdiφ_s : ContDiff ℝ ∞
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      contDiff_partialDeriv φ i hφ
    have hdiφ_c : HasCompactSupport
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      hasCompactSupport_partialDeriv φ i hsupp
    exact ⟨_, _,
      hasWeakDerivative_of_smooth_compactSupport φ hφ hsupp
        hmem (memLp_partialDeriv φ i hφ hsupp),
      hasWeakDerivative_of_smooth_compactSupport _ hdiφ_s hdiφ_c
        (memLp_partialDeriv φ i hφ hsupp)
        (memLp_partialDeriv _ j hdiφ_s hdiφ_c)⟩

/-- **H²(ℝ³) is dense in L²(ℝ³).** An instance of the classical Meyers–Serrin "H = W"
    theorem: every point of the `L²`-dense set of smooth, compactly supported test functions
    (`dense_test_functions_L2`) already lies in `H²(ℝ³)`
    (`smooth_compactSupport_memSobolevH2`), so density transports along the inclusion. -/
theorem sobolevH2_dense : Dense (SobolevH2 (d := d) : Set (l2Rn d)) := by
  apply Dense.mono _ dense_test_functions_L2
  rintro g ⟨φ, hφ, hsupp, hae⟩
  change MemSobolevH2 g
  have hmem := memLp_of_smooth_compactSupport φ hφ hsupp
  have h_eq : g = hmem.toLp φ :=
    Subtype.ext (AEEqFun.ext (hae.trans hmem.coeFn_toLp.symm))
  rw [h_eq]
  exact smooth_compactSupport_memSobolevH2 φ hφ hsupp hmem

/-- **C_c^∞(ℝ³) is dense in H¹(ℝ³).** The classical Meyers–Serrin "H = W" theorem: every
    `f ∈ H¹(ℝ³)` is `ε`-approximated by a smooth, compactly supported `g ∈ H²(ℝ³)`, with the
    approximation holding simultaneously in the ambient `L²` norm (`‖f - g‖ < ε`) and in every
    weak-gradient component separately (`‖∂ᵢf - ∂ᵢg‖ < ε` for each `i`) — not as a single
    combined Sobolev norm. -/
theorem smooth_compactly_supported_dense_H1 (f : l2R3) (hf : MemSobolevH1 f) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (g : l2R3) (hg : MemSobolevH2 g),
      ‖f - g‖ < ε ∧
      ∀ i, ‖weakGradient f hf i - weakGradient g (sobolevH2_le_sobolevH1 hg) i‖ < ε := by
  obtain ⟨φ, hφ, hφ_supp, hf_close, hgrad_close⟩ :=
    meyers_serrin_approx_multi f (weakGradient f hf)
      (weakGradient_spec f hf) ε hε
  set hmem := memLp_of_smooth_compactSupport φ hφ hφ_supp
  refine ⟨hmem.toLp φ,
    smooth_compactSupport_memSobolevH2 φ hφ hφ_supp hmem,
    hf_close, ?_⟩
  intro i
  have h_grad_eq : weakGradient (hmem.toLp φ)
      (sobolevH2_le_sobolevH1
        (smooth_compactSupport_memSobolevH2 φ hφ hφ_supp hmem)) i =
      (memLp_partialDeriv φ i hφ hφ_supp).toLp
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    apply hasWeakDerivative_unique (hmem.toLp φ) i
    · exact weakGradient_spec _ _ i
    · exact hasWeakDerivative_of_smooth_compactSupport φ hφ hφ_supp hmem
        (memLp_partialDeriv φ i hφ hφ_supp)
  rw [h_grad_eq]
  exact hgrad_close i

end Spectra.Sobolev

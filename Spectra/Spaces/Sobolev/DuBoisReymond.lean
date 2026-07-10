/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.Density
/-!
# Du Bois–Reymond Lemma

This file proves the fundamental lemma of the calculus of variations (du Bois-Reymond) for
`L²(ℝ³, ℂ)`: an L² function that integrates to zero against every smooth compactly supported
test function is itself zero. As an immediate consequence, the weak derivative of an `l2R3`
function is unique.

## Main results

* `inner_L2_test_eq_zero`: the L² inner product against `h` vanishes on any test-function
  representative, given that `h` integrates to zero against every test function.
* `eq_zero_of_integral_against_test_eq_zero`: **the fundamental lemma itself** — if `h : l2R3`
  integrates to zero against every smooth compactly supported test function, then `h = 0`.
* `hasWeakDerivative_unique`: the weak derivative of an `l2R3` function, in a given coordinate
  direction, is unique as an L² element (i.e. unique a.e.).

## Implementation notes

The fundamental lemma is proved by the standard closed-set/density argument: the set of
`w : l2R3` orthogonal to `h` is closed (inner product is continuous), it contains every test
function (by hypothesis, via `inner_L2_test_eq_zero`), and test functions are dense in `l2R3`
(`dense_test_functions_L2`, from `Density.lean`); density then forces every `w` — in particular
`h` itself — into that closed set, giving `h = 0`.

`inner_L2_test_eq_zero` is the conjugation bridge: the hypothesis is stated with a bare product
`∫ h * φ`, while the L² inner product `⟪h, g⟫` unfolds to `∫ g * conj h`. The lemma reconciles
the two by applying the hypothesis to `conj φ` (still smooth and compactly supported) and using
that integration commutes with the continuous conjugation map `starRingEnd ℂ`; integrability of
the products throughout relies on Hölder for `L² · L² → L¹` (`MemLp.integrable_mul`).

## References

* [Adams, Fournier, *Sobolev Spaces*][adams2003]
* [Reed, Simon, *Methods of Modern Mathematical Physics II*][reed1975]
-/
open MeasureTheory
open scoped ContDiff

namespace Spectra.Sobolev

/-- The L² inner product vanishes against test function representatives -/
lemma inner_L2_test_eq_zero {d : ℕ} (h : l2Rn d)
    (htest : ∀ (φ : Rn d → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, h x * φ x = 0)
    (g : l2Rn d) (φ : Rn d → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hae : (g : Rn d → ℂ) =ᵐ[volume] φ) :
    @inner ℂ (l2Rn d) _ h g = 0 := by
  have h0 : ∫ x, (h : Rn d → ℂ) x * starRingEnd ℂ (φ x) = 0 :=
    htest _ (contDiff_starRingEnd_comp hφ) (hasCompactSupport_starRingEnd_comp hsupp)
  have hint : Integrable (fun x => (h : Rn d → ℂ) x * starRingEnd ℂ (φ x)) volume := by
    have hh : MemLp (h : Rn d → ℂ) 2 volume := Lp.memLp h
    have hφ_L2 : MemLp (fun x => starRingEnd ℂ (φ x)) 2 volume :=
      memLp_of_smooth_compactSupport _ (contDiff_starRingEnd_comp hφ)
        (hasCompactSupport_starRingEnd_comp hsupp)
    exact hh.integrable_mul hφ_L2
  have h1 : ∫ x, φ x * starRingEnd ℂ ((h : Rn d → ℂ) x) = 0 := by
    have eq : ∫ x, starRingEnd ℂ ((h : Rn d → ℂ) x * starRingEnd ℂ (φ x)) =
              starRingEnd ℂ (∫ x, (h : Rn d → ℂ) x * starRingEnd ℂ (φ x)) :=
      Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hint
    rw [h0, map_zero] at eq
    simp only [map_mul, starRingEnd_apply, star_star, mul_comm] at eq
    simp only [starRingEnd_apply]
    exact eq
  rw [L2.inner_def]
  simp only [RCLike.inner_apply]
  trans ∫ a, φ a * starRingEnd ℂ ((h : Rn d → ℂ) a)
  · exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  · exact h1

/-- **Fundamental lemma of the calculus of variations (du Bois-Reymond).**
    If an L² function integrates to zero against every smooth compactly
    supported test function, then it is zero (as an element of L²). -/
lemma eq_zero_of_integral_against_test_eq_zero {d : ℕ}
    (h : l2Rn d)
    (htest : ∀ (φ : Rn d → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, h x * φ x = 0) :
    h = 0 := by
  apply @ext_inner_right ℂ; intro g; rw [inner_zero_left]
  have hclosed : IsClosed {w : l2Rn d | @inner ℂ _ _ h w = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hcontains : {g : l2Rn d | ∃ (φ : Rn d → ℂ),
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (g : Rn d → ℂ) =ᵐ[volume] φ} ⊆
      {w : l2Rn d | @inner ℂ _ _ h w = 0} := by
    rintro w ⟨φ, hφ, hsupp, hae⟩
    exact inner_L2_test_eq_zero h htest w φ hφ hsupp hae
  have h_closure := closure_minimal hcontains hclosed
  rw [dense_test_functions_L2.closure_eq] at h_closure
  exact h_closure (Set.mem_univ g)

/-- Weak derivative is unique (as L² elements, i.e., a.e.). -/
lemma hasWeakDerivative_unique {d : ℕ}
    (f : l2Rn d) (i : Fin d) (g₁ g₂ : l2Rn d)
    (h₁ : HasWeakDerivative f i g₁) (h₂ : HasWeakDerivative f i g₂) :
    g₁ = g₂ := by
  suffices h : g₁ - g₂ = 0 from sub_eq_zero.mp h
  apply eq_zero_of_integral_against_test_eq_zero
  intro φ hφ hsupp
  -- Both definitions give ∫ f · ∂ᵢφ = -∫ gₖ · φ, so the integrals agree
  have key : ∫ x, (g₁ : Rn d → ℂ) x * φ x = ∫ x, (g₂ : Rn d → ℂ) x * φ x := by
    have e₁ := h₁ φ hφ hsupp
    have e₂ := h₂ φ hφ hsupp
    have : -∫ x, (g₁ : Rn d → ℂ) x * φ x = -∫ x, (g₂ : Rn d → ℂ) x * φ x :=
      e₁.symm.trans e₂
    exact neg_inj.mp this
  -- Integrability (Hölder: L² · L² → L¹)
  have hφ_L2 := memLp_of_smooth_compactSupport φ hφ hsupp
  have hint₁ : Integrable (fun x => (g₁ : Rn d → ℂ) x * φ x) volume :=
    (Lp.memLp g₁).integrable_mul hφ_L2
  have hint₂ : Integrable (fun x => (g₂ : Rn d → ℂ) x * φ x) volume :=
    (Lp.memLp g₂).integrable_mul hφ_L2
  -- ae: (g₁ - g₂)(x) * φ(x) = g₁(x) * φ(x) - g₂(x) * φ(x)
  rw [integral_congr_ae ((Lp.coeFn_sub g₁ g₂).mono fun x hx => by
      simp only [Pi.sub_apply] at hx; rw [hx, sub_mul]),
    integral_sub hint₁ hint₂, key, sub_self]

end Spectra.Sobolev

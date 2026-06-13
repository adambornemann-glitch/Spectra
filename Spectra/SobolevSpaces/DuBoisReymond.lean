/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/SoboleveSpaces/DuBoisReyemond.lean
-/
import Spectra.SobolevSpaces.Density

open MeasureTheory Complex Filter MeasurableSet ContDiffBump
open scoped Topology NNReal ENNReal TopologicalSpace ProbabilityTheory Pointwise ContDiff

namespace Spectra.Sobolev

/-! ### Configuration space and Hilbert space -/

-- `MeasurableSpace`/`BorelSpace`/`MeasureSpace R3` come from `WeakDerivative.lean`
-- (transitively imported); no re-declaration here. `MeasureSpace` is Mathlib's
-- `measureSpaceOfInnerProductSpace` — see the note in `WeakDerivative.lean`.

/-- The L² inner product vanishes against test function representatives -/
lemma inner_L2_test_eq_zero (h : L2_R3)
    (htest : ∀ (φ : R3 → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, h x * φ x = 0)
    (g : L2_R3) (φ : R3 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hae : (g : R3 → ℂ) =ᵐ[volume] φ) :
    @inner ℂ L2_R3 _ h g = 0 := by
  have h0 : ∫ x, (h : R3 → ℂ) x * starRingEnd ℂ (φ x) = 0 :=
    htest _ (contDiff_starRingEnd_comp hφ) (hasCompactSupport_starRingEnd_comp hsupp)
  have hint : Integrable (fun x => (h : R3 → ℂ) x * starRingEnd ℂ (φ x)) volume := by
    have hh : MemLp (h : R3 → ℂ) 2 volume := Lp.memLp h
    have hφ_L2 : MemLp (fun x => starRingEnd ℂ (φ x)) 2 volume :=
      memLp_of_smooth_compactSupport _ (contDiff_starRingEnd_comp hφ)
        (hasCompactSupport_starRingEnd_comp hsupp)
    exact hh.integrable_mul hφ_L2
  have h1 : ∫ x, φ x * starRingEnd ℂ ((h : R3 → ℂ) x) = 0 := by
    have eq : ∫ x, starRingEnd ℂ ((h : R3 → ℂ) x * starRingEnd ℂ (φ x)) =
              starRingEnd ℂ (∫ x, (h : R3 → ℂ) x * starRingEnd ℂ (φ x)) :=
      Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hint
    rw [h0, map_zero] at eq
    simp only [map_mul, starRingEnd_apply, star_star, mul_comm] at eq
    simp only [starRingEnd_apply]
    exact eq
  rw [L2.inner_def]
  simp only [RCLike.inner_apply]
  trans ∫ a, φ a * starRingEnd ℂ ((h : R3 → ℂ) a)
  · exact integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  · exact h1


/-- **Fundamental lemma of the calculus of variations (du Bois-Reymond).**
    If an L² function integrates to zero against every smooth compactly
    supported test function, then it is zero (as an element of L²). -/
lemma Lp.eq_zero_of_integral_against_test_eq_zero
    (h : L2_R3)
    (htest : ∀ (φ : R3 → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, h x * φ x = 0) :
    h = 0 := by
  apply @ext_inner_right ℂ; intro g; rw [inner_zero_left]
  have hclosed : IsClosed {w : L2_R3 | @inner ℂ _ _ h w = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hcontains : {g : L2_R3 | ∃ (φ : R3 → ℂ),
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (g : R3 → ℂ) =ᵐ[volume] φ} ⊆
      {w : L2_R3 | @inner ℂ _ _ h w = 0} := by
    rintro w ⟨φ, hφ, hsupp, hae⟩
    exact inner_L2_test_eq_zero h htest w φ hφ hsupp hae
  have h_closure := closure_minimal hcontains hclosed
  rw [dense_test_functions_L2.closure_eq] at h_closure
  exact h_closure (Set.mem_univ g)


/-- Weak derivative is unique (as L² elements, i.e., a.e.). -/
lemma hasWeakDerivative_unique
    (f : L2_R3) (i : Fin 3) (g₁ g₂ : L2_R3)
    (h₁ : HasWeakDerivative f i g₁) (h₂ : HasWeakDerivative f i g₂) :
    g₁ = g₂ := by
  suffices h : g₁ - g₂ = 0 from sub_eq_zero.mp h
  apply Lp.eq_zero_of_integral_against_test_eq_zero
  intro φ hφ hsupp
  -- Both definitions give ∫ f · ∂ᵢφ = -∫ gₖ · φ, so the integrals agree
  have key : ∫ x, (g₁ : R3 → ℂ) x * φ x = ∫ x, (g₂ : R3 → ℂ) x * φ x := by
    have e₁ := h₁ φ hφ hsupp
    have e₂ := h₂ φ hφ hsupp
    have : -∫ x, (g₁ : R3 → ℂ) x * φ x = -∫ x, (g₂ : R3 → ℂ) x * φ x :=
      e₁.symm.trans e₂
    exact neg_inj.mp this
  -- Integrability (Hölder: L² · L² → L¹)
  have hφ_L2 := memLp_of_smooth_compactSupport φ hφ hsupp
  have hint₁ : Integrable (fun x => (g₁ : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp g₁).integrable_mul hφ_L2
  have hint₂ : Integrable (fun x => (g₂ : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp g₂).integrable_mul hφ_L2
  -- ae: (g₁ - g₂)(x) * φ(x) = g₁(x) * φ(x) - g₂(x) * φ(x)
  rw [integral_congr_ae ((Lp.coeFn_sub g₁ g₂).mono fun x hx => by
      simp only [Pi.sub_apply] at hx; rw [hx, sub_mul]),
    integral_sub hint₁ hint₂, key, sub_self]


end Spectra.Sobolev

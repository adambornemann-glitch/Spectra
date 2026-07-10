/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.MapsResolvent

/-!
# Boundedness below through the Cayley transform

For a symmetric operator pencil `A`, `μ` fails to be an approximate eigenvalue exactly when
`A - μ` is bounded below. This file transfers that property across the Cayley transform: if the
bounded shift `U - w` is bounded below (equivalently a unit), where `w = (μ - i)/(μ + i)` is the
Möbius image of the real point `μ`, then `A - μ` is bounded below, with an explicit constant.

## Main definitions

* `HasEigenvalue`: `μ` is an eigenvalue of `A`, i.e. `A` fixes some nonzero domain vector up to
  scaling by `μ`.
* `IsBoundedBelow`: `A - μ` is bounded below on its domain.

## Main results

* `isBoundedBelow_of_cayleyTransform_sub_smul_boundedBelow`: boundedness below of `U - w`
  transfers to boundedness below of `A - μ`.
* `isBoundedBelow_of_isUnit_cayleyTransform_sub_smul`: the same transfer stated from invertibility
  of `U - w`.
* `norm_lower_bound_of_approx_eigenvalue_of_unit`: a quantitative lower bound on `‖ψ‖` for an
  approximate eigenvector, in terms of `μ` and the approximation error `δ`.
-/

open InnerProductSpace MeasureTheory Complex Filter Topology
open Spectra.Operator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Spectra.Cayley

/-- `μ` is an eigenvalue of `A`: a nonzero domain vector fixed up to `μ`. -/
def HasEigenvalue (A : H →ₗ.[ℂ] H) (μ : ℂ) : Prop :=
  ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = μ • (ψ : H)

/-- `A - μ` is bounded below on its domain
(equivalently: `μ` is outside the approximate point spectrum of `A`). -/
def IsBoundedBelow (A : H →ₗ.[ℂ] H) (μ : ℂ) : Prop :=
  ∃ C > 0, ∀ ψ : A.domain, C * ‖(ψ : H)‖ ≤ ‖A ψ - μ • (ψ : H)‖

/-- If the Cayley shift `U - w` is bounded below (by `c`), so is `A - μ`. -/
lemma isBoundedBelow_of_cayleyTransform_sub_smul_boundedBelow
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) (c : ℝ) (hc_pos : 0 < c)
    (hc_bound : ∀ φ, c * ‖φ‖ ≤
      ‖(cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖) :
    IsBoundedBelow A μ := by
  set U := cayleyTransform hsym hplus with _hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := by
    rw [hw_def]; exact one_sub_mobius_norm_pos μ hμ_ne
  refine ⟨c / ‖(1 : ℂ) - w‖, div_pos hc_pos h_one_sub_w_norm_pos, fun ψ => ?_⟩
  set φ := A ψ + I • (ψ : H) with hφ_def
  have h_key : (U - w • ContinuousLinearMap.id ℂ H) φ
      = ((1 : ℂ) - w) • (A ψ - (↑μ : ℂ) • (ψ : H)) :=
    cayley_shift_identity hsym hplus μ hμ_ne ψ
  have h_phi_bound : ‖(ψ : H)‖ ≤ ‖φ‖ := by
    have h_sq := self_adjoint_norm_sq_add hsym ψ
    rw [← hφ_def] at h_sq
    have h2 : ‖(ψ : H)‖ ^ 2 ≤ ‖φ‖ ^ 2 := by rw [h_sq]; linarith [sq_nonneg ‖A ψ‖]
    nlinarith [norm_nonneg φ, norm_nonneg (ψ : H), h2]
  have h_chain : c * ‖(ψ : H)‖ ≤ ‖(1 : ℂ) - w‖ * ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ := by
    have h_eq : ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
        = ‖(1 : ℂ) - w‖ * ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ := by rw [h_key, norm_smul]
    calc c * ‖(ψ : H)‖
        ≤ c * ‖φ‖ := mul_le_mul_of_nonneg_left h_phi_bound (le_of_lt hc_pos)
      _ ≤ ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ := hc_bound φ
      _ = ‖(1 : ℂ) - w‖ * ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ := h_eq
  rw [div_mul_eq_mul_div, div_le_iff₀ h_one_sub_w_norm_pos,
      mul_comm ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ ‖(1 : ℂ) - w‖]
  exact h_chain

/-- If `U - w` is invertible, then `A - μ` is bounded below. -/
lemma isBoundedBelow_of_isUnit_cayleyTransform_sub_smul [Nontrivial H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ)
    (h_unit : IsUnit (cayleyTransform hsym hplus -
      ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)) :
    IsBoundedBelow A μ := by
  obtain ⟨c, hc_pos, hc_bound⟩ := isUnit_bounded_below h_unit
  exact isBoundedBelow_of_cayleyTransform_sub_smul_boundedBelow hsym hplus μ
    (real_add_I_ne_zero μ) c hc_pos hc_bound

/-- If `(A + iI)ψ` is a unit vector and `Aψ` is within `δ` of `μψ`, then `‖ψ‖` is
bounded below by an explicit function of `(μ, δ)`. The quantitative engine behind the
backward transfer of approximate eigenvalues through the Cayley transform. -/
lemma norm_lower_bound_of_approx_eigenvalue_of_unit
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (μ : ℝ) (ψ : A.domain)
    (h_norm : ‖A ψ + I • (ψ : H)‖ = 1)
    (δ : ℝ) (hδ_pos : 0 ≤ δ) (hδ_small : δ ^ 2 < 1 + μ ^ 2)
    (h_approx : ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ ≤ δ) :
    (Real.sqrt (1 + μ ^ 2 - δ ^ 2) - |μ| * δ) / (1 + μ ^ 2) ≤ ‖(ψ : H)‖ := by
  have hx0   : (0 : ℝ) ≤ ‖(ψ : H)‖ := norm_nonneg _
  have hcoeff : (0 : ℝ) < 1 + μ ^ 2 := by positivity
  -- Pythagoras through the +i picture: ‖Aψ‖² + ‖ψ‖² = 1.
  have hpy : ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 = 1 := by
    have h := self_adjoint_norm_sq_add hsym ψ
    rw [h_norm, one_pow] at h; linarith
  -- Reverse triangle inequality bounds ‖Aψ‖ above.
  have hμψ : ‖(↑μ : ℂ) • (ψ : H)‖ = |μ| * ‖(ψ : H)‖ := by
    rw [norm_smul]; simp [Complex.norm_real, Real.norm_eq_abs]
  have hAψ_upper : ‖A ψ‖ ≤ |μ| * ‖(ψ : H)‖ + δ := by
    have ht := abs_norm_sub_norm_le (A ψ) ((↑μ : ℂ) • (ψ : H))
    rw [hμψ] at ht
    have := (abs_le.mp (le_trans ht h_approx)).2
    linarith
  -- The defining quadratic inequality q(‖ψ‖) ≥ 0.
  have hq : 0 ≤ (1 + μ ^ 2) * ‖(ψ : H)‖ ^ 2 + 2 * |μ| * δ * ‖(ψ : H)‖ + (δ ^ 2 - 1) := by
    have hsq : ‖A ψ‖ ^ 2 ≤ (|μ| * ‖(ψ : H)‖ + δ) ^ 2 :=
      sq_le_sq' (by nlinarith [norm_nonneg (A ψ), mul_nonneg (abs_nonneg μ) hx0]) hAψ_upper
    nlinarith [hpy, hsq, sq_abs μ]
  -- S = √(1+μ²−δ²) ≤ L = (1+μ²)‖ψ‖ + |μ|δ, because L² − S² = (1+μ²)·q(‖ψ‖) ≥ 0.
  set S := Real.sqrt (1 + μ ^ 2 - δ ^ 2) with _hS
  have hS0  : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = 1 + μ ^ 2 - δ ^ 2 := Real.sq_sqrt (by linarith)
  set L := (1 + μ ^ 2) * ‖(ψ : H)‖ + |μ| * δ with hL
  have hL0 : 0 ≤ L := by positivity
  have hLS : S ≤ L := by
    have hL2 : S ^ 2 ≤ L ^ 2 := by
      have := mul_nonneg hcoeff.le hq    -- 0 ≤ (1+μ²)·q(‖ψ‖) = L² − S²
      nlinarith [this, sq_abs μ, hSsq]
    have := Real.sqrt_le_sqrt hL2        -- √(S²) ≤ √(L²)
    rwa [Real.sqrt_sq hS0, Real.sqrt_sq hL0] at this
  rw [div_le_iff₀ hcoeff, hL] at *
  nlinarith [hLS]

end Spectra.Cayley

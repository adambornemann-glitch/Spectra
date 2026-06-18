/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Yosida/Bounds.lean
-/
import Spectra.Stone.Yosida.Defs
/-!
# Norm Bounds on Yosida Operators

This file establishes norm bounds for the Yosida approximation operators.
The key results show that `Jₙ` and `Jₙ⁻` are contractions (norm ≤ 1).

## Main results

* `yosidaApprox_norm_bound`: `‖Aₙ‖ ≤ 2n`
* `yosidaJ_norm_bound`: `‖Jₙ‖ ≤ 1`
* `yosidaJNeg_norm_bound`: `‖Jₙ⁻‖ ≤ 1`

-/
open Complex Spectra.Resolvent
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Stone.Yosida

lemma yosidaApprox_norm_bound {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    ‖yosidaApprox hsym hplus hminus n‖ ≤ 2 * (n : ℝ) := by
  unfold yosidaApprox
  have h_first : ‖(n : ℂ)^2 • resolventAtIn hsym hplus hminus n‖ ≤ (n : ℝ) := by
    calc ‖(n : ℂ)^2 • resolventAtIn hsym hplus hminus n‖
        = ‖(n : ℂ)^2‖ * ‖resolventAtIn hsym hplus hminus n‖ := norm_smul ((n : ℂ)^2) _
      _ ≤ ‖(n : ℂ)^2‖ * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (resolventAtIn_bound hsym hplus hminus n)
          exact norm_nonneg _
      _ = (n : ℝ)^2 * (1 / (n : ℝ)) := by rw [norm_pnat_sq]
      _ = (n : ℝ) := by field_simp
  have h_second : ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ ≤ (n : ℝ) := by
    calc ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
        = ‖I * (n : ℂ)‖ * ‖ContinuousLinearMap.id ℂ H‖ := norm_smul (I * (n : ℂ)) _
      _ ≤ ‖I * (n : ℂ)‖ * 1 := by
          apply mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
          exact norm_nonneg _
      _ = ‖I * (n : ℂ)‖ := mul_one _
      _ = (n : ℝ) := norm_I_mul_pnat n
  calc ‖(n : ℂ)^2 • resolventAtIn hsym hplus hminus n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
      ≤ ‖(n : ℂ)^2 • resolventAtIn hsym hplus hminus n‖ + ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ :=
          norm_sub_le _ _
    _ ≤ (n : ℝ) + (n : ℝ) := add_le_add h_first h_second
    _ = 2 * (n : ℝ) := by ring

lemma yosidaJ_norm_bound {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    ‖(-I * (n : ℂ)) • resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ ≤ 1 := by
  have h_neg : (-I : ℂ) * (n : ℂ) = -(I * (n : ℂ)) := by ring
  have h_coeff : ‖(-I * (n : ℂ))‖ = (n : ℝ) := by
    calc ‖(-I * (n : ℂ))‖
        = ‖-(I * (n : ℂ))‖ := by rw [h_neg]
      _ = ‖I * (n : ℂ)‖ := norm_neg _
      _ = (n : ℝ) := norm_I_mul_pnat n
  have h_res : ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ ≤ 1 / (n : ℝ) := by
    calc ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
        ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound hsym hplus hminus _ _
      _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
  calc ‖(-I * (n : ℂ)) • resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
      = ‖(-I * (n : ℂ))‖ * ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_res
          exact le_of_lt hn_pos
    _ = 1 := by field_simp

lemma yosidaJNeg_norm_bound {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    ‖yosidaJNeg hsym hplus hminus n‖ ≤ 1 := by
  unfold yosidaJNeg resolventAtNegIn
  have h_coeff : ‖I * (n : ℂ)‖ = (n : ℝ) := norm_I_mul_pnat n
  have h_res : ‖resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ ≤ 1 / (n : ℝ) := by
    calc ‖resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
        ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound hsym hplus hminus _ _
      _ = 1 / (n : ℝ) := by
          simp only [neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
          rw [← h_coeff]
          rw [h_coeff]
          rw [@abs_neg]
          rw [natCast_re]
          rw [abs_of_pos (Nat.cast_pos.mpr n.pos)]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
  calc ‖(I * (n : ℂ)) • resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
      = ‖I * (n : ℂ)‖ * ‖resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left h_res (le_of_lt hn_pos)
    _ = 1 := by field_simp

end Spectra.Stone.Yosida

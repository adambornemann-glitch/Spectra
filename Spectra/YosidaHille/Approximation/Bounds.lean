/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Approximation.Defs

/-!
# Norm bounds on the Yosida operators

Norm bounds for the Yosida approximation operators: the approximant `Aₙ` is bounded by `2n`, and
the contractions `Jₙ`, `Jₙ⁻` have norm `≤ 1`. The contraction bounds drive the convergence of the
exponential series for `Aₙ`.

## Main statements

* `yosidaApprox_norm_bound` — `‖Aₙ‖ ≤ 2n`.
* `yosidaJ_norm_bound` / `yosidaJNeg_norm_bound` — `‖Jₙ‖ ≤ 1` and `‖Jₙ⁻‖ ≤ 1`.
-/

open Complex Spectra.Resolvent
open Spectra.OneParameterUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.YosidaHille.Approximation

/-- The Yosida approximant is norm-bounded by `2n`: `‖Aₙ‖ ≤ 2n`. -/
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
      _ ≤ ‖(n : ℂ)^2‖ * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (resolventAtIn_bound hsym hplus hminus n) (norm_nonneg _)
      _ = (n : ℝ)^2 * (1 / (n : ℝ)) := by rw [norm_pnat_sq]
      _ = (n : ℝ) := by field_simp
  have h_second : ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ ≤ (n : ℝ) := by
    calc ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
        = ‖I * (n : ℂ)‖ * ‖ContinuousLinearMap.id ℂ H‖ := norm_smul (I * (n : ℂ)) _
      _ ≤ ‖I * (n : ℂ)‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖I * (n : ℂ)‖ := mul_one _
      _ = (n : ℝ) := norm_I_mul_pnat n
  calc ‖(n : ℂ)^2 • resolventAtIn hsym hplus hminus n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖
      ≤ ‖(n : ℂ)^2 • resolventAtIn hsym hplus hminus n‖
          + ‖(I * (n : ℂ)) • ContinuousLinearMap.id ℂ H‖ := norm_sub_le _ _
    _ ≤ (n : ℝ) + (n : ℝ) := add_le_add h_first h_second
    _ = 2 * (n : ℝ) := by ring

/-- The contraction `Jₙ = -in·R(in)` has norm `≤ 1`. -/
lemma yosidaJ_norm_bound {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    ‖yosidaJ hsym hplus hminus n‖ ≤ 1 := by
  unfold yosidaJ resolventAtIn
  have h_coeff : ‖(-I * (n : ℂ))‖ = (n : ℝ) := by
    rw [neg_mul, norm_neg, norm_I_mul_pnat]
  have h_res : ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
      ≤ 1 / (n : ℝ) := by
    calc ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
        ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound _ _ hsym hplus hminus
      _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
  calc ‖(-I * (n : ℂ)) • resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
      = ‖(-I * (n : ℂ))‖ * ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left h_res hn_pos.le
    _ = 1 := by field_simp

/-- The contraction `Jₙ⁻ = in·R(-in)` has norm `≤ 1`. -/
lemma yosidaJNeg_norm_bound {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (n : ℕ+) :
    ‖yosidaJNeg hsym hplus hminus n‖ ≤ 1 := by
  unfold yosidaJNeg resolventAtNegIn
  have h_coeff : ‖I * (n : ℂ)‖ = (n : ℝ) := norm_I_mul_pnat n
  have h_res : ‖resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
      ≤ 1 / (n : ℝ) := by
    calc ‖resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
        ≤ 1 / |(-I * (n : ℂ)).im| := resolvent_bound _ _ hsym hplus hminus
      _ = 1 / (n : ℝ) := by
          simp only [neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
          rw [@abs_neg, natCast_re, abs_of_pos (Nat.cast_pos.mpr n.pos)]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
  calc ‖(I * (n : ℂ)) • resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖
      = ‖I * (n : ℂ)‖
        * ‖resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ :=
          norm_smul _ _
    _ = (n : ℝ) * ‖resolvent (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsym hplus hminus‖ := by
          rw [h_coeff]
    _ ≤ (n : ℝ) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left h_res hn_pos.le
    _ = 1 := by field_simp

end Spectra.YosidaHille.Approximation

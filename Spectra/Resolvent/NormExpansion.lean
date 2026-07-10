/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Defs
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Norm Expansion for Symmetric Operators

This file proves the key identity used throughout resolvent theory:
for a symmetric operator `A` and purely imaginary `λ`, the cross term
in `‖Aψ - λψ‖²` vanishes, giving `‖Aψ - λψ‖² = ‖Aψ‖² + |λ|²‖ψ‖²`.

## Main statements

* `inner_self_im_eq_zero_of_symmetric`: `⟪Aψ, ψ⟫` is real for symmetric `A`.
* `cross_term_re_eq_zero_of_symmetric`: the cross term `⟪Aψ, λψ⟫` has zero real part for
  imaginary `λ`.
* `norm_sq_sub_smul_of_symmetric`: `‖Aψ - λψ‖² = ‖Aψ‖² + |λ|²‖ψ‖²`.
* `norm_sq_sub_I_smul`: special case for `λ = I`.
* `norm_sq_add_I_smul`: special case for `λ = -I` (written as `Aψ + Iψ`).
* `norm_le_norm_sub_I_smul` / `norm_le_norm_add_I_smul`: `‖ψ‖ ≤ ‖Aψ ∓ Iψ‖`.

## Implementation notes

These lemmas eliminate the repeated `Aψ ± Iψ` norm calculation that would otherwise be redone at
every `s = ±I` specialization in the resolvent construction: `Resolvent/SpecialCases.lean` calls
`norm_le_norm_sub_I_smul`/`norm_le_norm_add_I_smul` from five call sites (as the generic contraction
hypothesis fed to `resolventAtImaginary` at `s = I` and `s = -I`) that would each need this argument
inline. The key insight is that symmetric operators have real expectation values, and purely
imaginary scalars rotate these to purely imaginary cross terms.
-/
open InnerProductSpace Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Spectra.Resolvent

/-! ## Symmetric operators have real expectation values -/

/-- For a symmetric operator, `⟪Aψ, ψ⟫` is real (has zero imaginary part). -/
lemma inner_self_im_eq_zero_of_symmetric
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 := by
  have h_sym := hsym ψ ψ
  have h_conj : ⟪A ψ, (ψ : H)⟫_ℂ = (starRingEnd ℂ) ⟪A ψ, (ψ : H)⟫_ℂ := by
    calc ⟪A ψ, (ψ : H)⟫_ℂ
        = ⟪(ψ : H), A ψ⟫_ℂ := h_sym
      _ = (starRingEnd ℂ) ⟪A ψ, (ψ : H)⟫_ℂ := (inner_conj_symm (ψ : H) (A ψ)).symm
  have h_parts := Complex.ext_iff.mp h_conj
  simp only [Complex.conj_im] at h_parts
  linarith [h_parts.2]

/-! ## Cross term vanishing for purely imaginary scalars -/

/-- For symmetric `A` and purely imaginary `λ`, the cross term `⟪Aψ, λψ⟫` has zero real part. -/
lemma cross_term_re_eq_zero_of_symmetric
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) (s : ℂ) (hs : s.re = 0) :
    (⟪A ψ, s • (ψ : H)⟫_ℂ).re = 0 := by
  rw [inner_smul_right]
  have h_real := inner_self_im_eq_zero_of_symmetric hsym ψ
  have h_inner_eq : s * ⟪A ψ, (ψ : H)⟫_ℂ = s * (⟪A ψ, (ψ : H)⟫_ℂ).re := by
    conv_lhs => rw [← Complex.re_add_im ⟪A ψ, (ψ : H)⟫_ℂ, h_real]
    simp
  rw [h_inner_eq, Complex.mul_re]
  simp [hs]

/-- **Key Lemma**: For symmetric `A` and purely imaginary `λ`,
    `‖Aψ - λψ‖² = ‖Aψ‖² + |λ|²‖ψ‖²`. -/
lemma norm_sq_sub_smul_of_symmetric
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) (s : ℂ) (hs : s.re = 0) :
    ‖A ψ - s • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖s‖^2 * ‖(ψ : H)‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex, cross_term_re_eq_zero_of_symmetric hsym ψ s hs, norm_smul]
  ring

/-- **Corollary**: For `λ = I`, we have `‖Aψ - Iψ‖² = ‖Aψ‖² + ‖ψ‖²`. -/
lemma norm_sq_sub_I_smul
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖A ψ - I • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖(ψ : H)‖^2 := by
  have h := norm_sq_sub_smul_of_symmetric hsym ψ I (by simp)
  simpa using h

/-- **Corollary**: For `λ = -I`, we have `‖Aψ + Iψ‖² = ‖Aψ‖² + ‖ψ‖²`. -/
lemma norm_sq_add_I_smul
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖A ψ + I • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖(ψ : H)‖^2 := by
  have h := norm_sq_sub_smul_of_symmetric hsym ψ (-I) (by simp)
  simp only [neg_smul, sub_neg_eq_add, norm_neg, Complex.norm_I, one_pow, one_mul] at h
  exact h

omit [InnerProductSpace ℂ H] in
/-- Private helper shared by `norm_le_norm_sub_I_smul` and `norm_le_norm_add_I_smul`: given the
`‖v‖² = ‖x‖² + ‖w‖²` norm-expansion identity for vectors `v`, `x`, `w`, conclude `‖w‖ ≤ ‖v‖`. -/
private lemma norm_le_of_norm_sq_eq_add {x v w : H}
    (h_sq : ‖v‖ ^ 2 = ‖x‖ ^ 2 + ‖w‖ ^ 2) :
    ‖w‖ ≤ ‖v‖ := by
  have : ‖w‖^2 ≤ ‖v‖^2 := by nlinarith [sq_nonneg ‖x‖]
  exact le_of_sq_le_sq this (norm_nonneg _)

/-- From the norm expansion, `‖ψ‖ ≤ ‖Aψ - Iψ‖`. -/
lemma norm_le_norm_sub_I_smul
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖(ψ : H)‖ ≤ ‖A ψ - I • (ψ : H)‖ :=
  norm_le_of_norm_sq_eq_add (norm_sq_sub_I_smul hsym ψ)

/-- From the norm expansion, `‖ψ‖ ≤ ‖Aψ + Iψ‖`. -/
lemma norm_le_norm_add_I_smul
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖(ψ : H)‖ ≤ ‖A ψ + I • (ψ : H)‖ :=
  norm_le_of_norm_sq_eq_add (norm_sq_add_I_smul hsym ψ)

end Spectra.Resolvent

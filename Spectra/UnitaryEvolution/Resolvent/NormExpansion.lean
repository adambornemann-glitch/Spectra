/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Resolvent/NormExpansion.lean
-/
import Spectra.UnitaryEvolution.Resolvent.Basic
/-!
# Norm Expansion for Symmetric Operators

This file proves the key identity used throughout resolvent theory:
for a symmetric operator `A` and purely imaginary `λ`, the cross term
in `‖Aψ - λψ‖²` vanishes, giving `‖Aψ - λψ‖² = ‖Aψ‖² + |λ|²‖ψ‖²`.

## Main statements

* `inner_self_im_eq_zero_of_symmetric`: `⟪Aψ, ψ⟫` is real for symmetric `A`
* `cross_term_re_eq_zero`: The cross term `⟪Aψ, λψ⟫` has zero real part when `λ` is purely imaginary
* `norm_sq_sub_smul_of_symmetric`: `‖Aψ - λψ‖² = ‖Aψ‖² + |λ|²‖ψ‖²`
* `norm_sq_sub_I_smul`: Special case for `λ = I`
* `norm_sq_add_I_smul`: Special case for `λ = -I` (written as `Aψ + Iψ`)

## Implementation notes

These lemmas eliminate ~100 lines of repeated calculation in the resolvent
construction. The key insight is that symmetric operators have real expectation
values, and purely imaginary scalars rotate these to purely imaginary cross terms.
-/

namespace QuantumMechanics.Resolvent

open InnerProductSpace Complex QuantumMechanics.Bochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

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

/-- Variant: the inner product `⟪Aψ, ψ⟫` equals its real part. -/
lemma inner_self_eq_re_of_symmetric
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ⟪A ψ, (ψ : H)⟫_ℂ = (⟪A ψ, (ψ : H)⟫_ℂ).re := by
  conv_lhs => rw [← Complex.re_add_im ⟪A ψ, (ψ : H)⟫_ℂ]
  rw [inner_self_im_eq_zero_of_symmetric hsym ψ]
  simp

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

/-- Special case: cross term for `I`. -/
lemma cross_term_I_re_eq_zero
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    (⟪A ψ, I • (ψ : H)⟫_ℂ).re = 0 :=
  cross_term_re_eq_zero_of_symmetric hsym ψ I (by simp)

/-- Special case: cross term for `-I`. -/
lemma cross_term_neg_I_re_eq_zero
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    (⟪A ψ, (-I) • (ψ : H)⟫_ℂ).re = 0 :=
  cross_term_re_eq_zero_of_symmetric hsym ψ (-I) (by simp)

/-- **Key Lemma**: For symmetric `A` and purely imaginary `λ`,
    `‖Aψ - λψ‖² = ‖Aψ‖² + |λ|²‖ψ‖²`. -/
lemma norm_sq_sub_smul_of_symmetric
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) (s : ℂ) (hs : s.re = 0) :
    ‖A ψ - s • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖s‖^2 * ‖(ψ : H)‖^2 := by
  have h_expand : ‖A ψ - s • (ψ : H)‖^2 =
      ‖A ψ‖^2 + ‖s • (ψ : H)‖^2 - 2 * (⟪A ψ, s • (ψ : H)⟫_ℂ).re := by
    have h_inner : (⟪A ψ - s • (ψ : H), A ψ - s • (ψ : H)⟫_ℂ).re =
        ‖A ψ - s • (ψ : H)‖^2 := by
      have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (A ψ - s • (ψ : H))
      rw [this]; norm_cast
    rw [← h_inner, inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [Complex.sub_re]
    have h1 : (⟪A ψ, A ψ⟫_ℂ).re = ‖A ψ‖^2 := by
      have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (A ψ)
      rw [this]; norm_cast
    have h2 : (⟪s • (ψ : H), s • (ψ : H)⟫_ℂ).re = ‖s • (ψ : H)‖^2 := by
      have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (s • (ψ : H))
      rw [this]; norm_cast
    rw [h1, h2]
    have h_cross : (⟪A ψ, s • (ψ : H)⟫_ℂ).re + (⟪s • (ψ : H), A ψ⟫_ℂ).re =
        2 * (⟪A ψ, s • (ψ : H)⟫_ℂ).re := by
      have h_eq : (⟪s • (ψ : H), A ψ⟫_ℂ).re = (⟪A ψ, s • (ψ : H)⟫_ℂ).re := by
        calc (⟪s • (ψ : H), A ψ⟫_ℂ).re
            = ((starRingEnd ℂ) ⟪A ψ, s • (ψ : H)⟫_ℂ).re := by rw [inner_conj_symm]
          _ = (⟪A ψ, s • (ψ : H)⟫_ℂ).re := by simp only [Complex.conj_re]
      rw [h_eq]; ring
    rw [← h_cross]; ring
  have h_norm_smul : ‖s • (ψ : H)‖ = ‖s‖ * ‖(ψ : H)‖ := norm_smul s (ψ : H)
  have h_cross_zero := cross_term_re_eq_zero_of_symmetric hsym ψ s hs
  rw [h_expand, h_norm_smul, h_cross_zero]
  ring

/-- **Corollary**: For `λ = I`, we have `‖Aψ - Iψ‖² = ‖Aψ‖² + ‖ψ‖²`. -/
lemma norm_sq_sub_I_smul
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖A ψ - I • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖(ψ : H)‖^2 := by
  have h := norm_sq_sub_smul_of_symmetric hsym ψ I (by simp)
  simp at h
  exact h

/-- **Corollary**: For `λ = -I`, we have `‖Aψ + Iψ‖² = ‖Aψ‖² + ‖ψ‖²`. -/
lemma norm_sq_add_I_smul
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖A ψ + I • (ψ : H)‖^2 = ‖A ψ‖^2 + ‖(ψ : H)‖^2 := by
  have h_eq : A ψ + I • (ψ : H) = A ψ - (-I) • (ψ : H) := by
    rw [neg_smul, sub_neg_eq_add]
  rw [h_eq]
  have h := norm_sq_sub_smul_of_symmetric hsym ψ (-I) (by simp)
  simp at h
  simp only [neg_smul, sub_neg_eq_add]
  exact h

/-- From the norm expansion, `‖ψ‖ ≤ ‖Aψ - Iψ‖`. -/
lemma norm_le_norm_sub_I_smul
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖(ψ : H)‖ ≤ ‖A ψ - I • (ψ : H)‖ := by
  have h_sq := norm_sq_sub_I_smul hsym ψ
  have h_le : ‖(ψ : H)‖^2 ≤ ‖A ψ - I • (ψ : H)‖^2 := by
    rw [h_sq]
    have : 0 ≤ ‖A ψ‖^2 := sq_nonneg _
    linarith
  have h1 : 0 ≤ ‖(ψ : H)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖A ψ - I • (ψ : H)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖(ψ : H)‖ - ‖A ψ - I • (ψ : H)‖)]

/-- From the norm expansion, `‖ψ‖ ≤ ‖Aψ + Iψ‖`. -/
lemma norm_le_norm_add_I_smul
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖(ψ : H)‖ ≤ ‖A ψ + I • (ψ : H)‖ := by
  have h_sq := norm_sq_add_I_smul hsym ψ
  have h_le : ‖(ψ : H)‖^2 ≤ ‖A ψ + I • (ψ : H)‖^2 := by
    rw [h_sq]
    have : 0 ≤ ‖A ψ‖^2 := sq_nonneg _
    linarith
  have h1 : 0 ≤ ‖(ψ : H)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖A ψ + I • (ψ : H)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖(ψ : H)‖ - ‖A ψ + I • (ψ : H)‖)]

end QuantumMechanics.Resolvent

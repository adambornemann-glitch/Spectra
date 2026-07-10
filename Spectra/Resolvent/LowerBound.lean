/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Defs
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Lower Bound Estimate for Symmetric Operators

This file proves the fundamental estimate for symmetric operators:
for `A` symmetric, `‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖` (most useful when `Im(z) ≠ 0`).

This estimate is the key to proving that the resolvent is bounded and that
`(A - zI)` has closed range.

## Main statements

* `lower_bound_estimate`: `‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖` for symmetric `A`, i.e.
  `A.IsFormalAdjoint A`. Full self-adjointness (domain equality with the adjoint) is not needed.

## Implementation notes

The proof is a Pythagorean decomposition `(A - zI)ψ = (A - x•1)ψ - (y·I)ψ` where `z = x + yi`.
Symmetry of `A` makes `⟪(A - x•1)ψ, ψ⟫` real, which in turn makes the cross term
`⟪(A - x•1)ψ, (y·I)ψ⟫` purely imaginary and hence its real part — the only part the norm expansion
sees — vanish. What remains is `‖(A - x•1)ψ‖² + |y|²‖ψ‖² ≥ |y|²‖ψ‖²`, giving the bound.

## References

* [Reed–Simon, *Methods of Modern Mathematical Physics I*][reedsimon1980], Theorem VIII.3
* [Kato, *Perturbation Theory for Linear Operators*][kato1995], Section V.3

## Physics interpretation

This estimate shows that `(A - zI)` is bounded below when `z` is off the real axis.
The spectrum of a self-adjoint operator is real, so moving `z` off the real axis
creates a "gap" proportional to `|Im(z)|`.
-/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
open InnerProductSpace Complex
namespace Spectra.Resolvent

/-- The fundamental lower bound: for symmetric `A`,
    `‖(A - zI)ψ‖ ≥ |Im(z)| · ‖ψ‖` (most useful off the real axis, where `|Im(z)| > 0`). -/
lemma lower_bound_estimate {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (ψ : H) (hψ : ψ ∈ A.domain) :
    ‖A ⟨ψ, hψ⟩ - z • ψ‖ ≥ |z.im| * ‖ψ‖ := by
  set x := z.re
  set y := z.im
  have h_decomp : A ⟨ψ, hψ⟩ - z • ψ = (A ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ := by
    have hz_eq : z = x + y * I := by simp [x, y]
    calc A ⟨ψ, hψ⟩ - z • ψ
        = A ⟨ψ, hψ⟩ - (x + y * I) • ψ := by rw [hz_eq]
      _ = A ⟨ψ, hψ⟩ - (x • ψ + (y * I) • ψ) := by rw [add_smul]; rfl
      _ = (A ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ := by abel
  rw [h_decomp]
  have h_expand : ‖(A ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2 =
                ‖A ⟨ψ, hψ⟩ - x • ψ‖^2 + ‖(y * I) • ψ‖^2 +
                2 * (⟪A ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    rw [inner_neg_right, Complex.neg_re]
    simp only [RCLike.re_to_complex]
    ring
  have h_norm_scale : ‖(y * I) • ψ‖ = |y| * ‖ψ‖ := by
    calc ‖(y * I) • ψ‖
        = ‖(y * I : ℂ)‖ * ‖ψ‖ := norm_smul _ _
      _ = |y| * ‖ψ‖ := by simp
  have h_cross_zero : (⟪A ⟨ψ, hψ⟩ - x • ψ, -((y * I) • ψ)⟫_ℂ).re = 0 := by
    rw [inner_neg_right, inner_smul_right]
    have h_real : (⟪A ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ).im = 0 := by
      rw [inner_sub_left]
      have h_Areal : (⟪A ⟨ψ, hψ⟩, ψ⟫_ℂ).im = 0 := by
        have h_sym := hsym ⟨ψ, hψ⟩ ⟨ψ, hψ⟩
        have h_conj : ⟪A ⟨ψ, hψ⟩, ψ⟫_ℂ = (starRingEnd ℂ) ⟪A ⟨ψ, hψ⟩, ψ⟫_ℂ := by
          calc ⟪A ⟨ψ, hψ⟩, ψ⟫_ℂ
              = ⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ := h_sym
            _ = (starRingEnd ℂ) ⟪A ⟨ψ, hψ⟩, ψ⟫_ℂ :=
                (inner_conj_symm ψ (A ⟨ψ, hψ⟩)).symm
        have h_parts := Complex.ext_iff.mp h_conj
        simp only [Complex.conj_im] at h_parts
        linarith [h_parts.2]
      have h_xreal : (⟪x • ψ, ψ⟫_ℂ).im = 0 := by
        have h_eq : x • ψ = (x : ℂ) • ψ := (RCLike.real_smul_eq_coe_smul x ψ).symm
        rw [h_eq, inner_smul_left]
        have h_inner_real : (⟪ψ, ψ⟫_ℂ).im = 0 := by
          have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
          rw [this]; norm_cast
        simp only [Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re,
                    Complex.ofReal_im, h_inner_real, mul_zero, zero_mul, add_zero]
      simp only [sub_im]
      simp [h_xreal]
      linarith [h_Areal]
    have h_as_real : ⟪A ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ =
        ((⟪A ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ).re : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im (⟪A ⟨ψ, hψ⟩ - x • ψ, ψ⟫_ℂ), h_real]
      simp
    rw [h_as_real]
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im,
              Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    simp only [I_re, mul_zero, zero_mul, neg_zero]
  have h_sq : (|y| * ‖ψ‖)^2 ≤ ‖(A ⟨ψ, hψ⟩ - x • ψ) - (y * I) • ψ‖^2 := by
    rw [h_expand, h_norm_scale, h_cross_zero]
    simp only [mul_zero, add_zero]
    have : 0 ≤ ‖A ⟨ψ, hψ⟩ - x • ψ‖^2 := sq_nonneg _
    linarith
  exact le_of_sq_le_sq h_sq (norm_nonneg _)

end Spectra.Resolvent

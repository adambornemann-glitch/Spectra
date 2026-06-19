/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Analytic

/-!
# Basic lemmas for the Yosida approximation

Foundational facts used throughout the Yosida-approximation construction: arithmetic of the
imaginary parts and norms of `I * n` and `-I * n` for `n : ℕ+` (these supply the off-axis
spectral parameters `z = I * n`), together with the defining specification of the resolvent
obtained from the surjectivity of `A ± I` on a formally self-adjoint operator.

## Main statements

* `I_mul_pnat_im_ne_zero` / `neg_I_mul_pnat_im_ne_zero` — `± I * n` has nonzero imaginary part,
  so it lies off the real axis and the resolvent is defined there.
* `norm_I_mul_pnat` — `‖I * n‖ = n`.
* `resolvent_spec` / `resolvent_spec'` — the resolvent `R(z)φ` lies in `dom A` and satisfies
  `(A - z) R(z) φ = φ`.
-/

open Complex
open Spectra.Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.YosidaHille.Approximation

/-! ### Arithmetic of `I * n` for `n : ℕ+` -/

/-- The imaginary part of `I * n` is nonzero for `n : ℕ+`, so `I * n` is off the real axis. -/
lemma I_mul_pnat_im_ne_zero (n : ℕ+) : (I * (n : ℂ)).im ≠ 0 := by
  simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  exact Nat.cast_ne_zero.mpr n.ne_zero

/-- The imaginary part of `-I * n` is nonzero for `n : ℕ+`. -/
lemma neg_I_mul_pnat_im_ne_zero (n : ℕ+) : (-I * (n : ℂ)).im ≠ 0 := by
  simp only [neg_mul, neg_im]
  exact neg_ne_zero.mpr (I_mul_pnat_im_ne_zero n)

/-- The imaginary part of `I * n` equals `n` for `n : ℕ+`. -/
lemma I_mul_pnat_im (n : ℕ+) : (I * (n : ℂ)).im = (n : ℝ) := by
  simp [mul_im]

/-- The absolute value of the imaginary part of `I * n` equals `n` for `n : ℕ+`. -/
lemma abs_I_mul_pnat_im (n : ℕ+) : |(I * (n : ℂ)).im| = (n : ℝ) := by
  rw [I_mul_pnat_im]
  exact abs_of_pos (Nat.cast_pos.mpr n.pos)

/-- The norm of `(n : ℂ)²` equals `n²` for `n : ℕ+`. -/
lemma norm_pnat_sq (n : ℕ+) : ‖((n : ℂ)^2)‖ = (n : ℝ)^2 := by
  simp [norm_pow]

/-- The norm of `I * n` equals `n` for `n : ℕ+`. -/
lemma norm_I_mul_pnat (n : ℕ+) : ‖I * (n : ℂ)‖ = (n : ℝ) := by
  simp

/-! ### Resolvent specifications -/

/-- The resolvent `R(z)φ` lies in `dom A`, and the chosen domain witness satisfies
`(A - z) R(z) φ = φ`. Here the membership proof is the `Classical.choose` witness coming from the
surjectivity of `A - z` (via `self_adjoint_range_all_z`). -/
lemma resolvent_spec {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    (Resolvent.resolvent z hz hsym hplus hminus φ) ∈ A.domain ∧
    A ⟨Resolvent.resolvent z hz hsym hplus hminus φ,
       (Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists).property⟩ -
    z • (Resolvent.resolvent z hz hsym hplus hminus φ) = φ := by
  have h_eq := Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists
  refine ⟨(Classical.choose
    (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists).property, ?_⟩
  convert h_eq using 2

/-- The existential form of `resolvent_spec`: there is a membership proof `h` for which the chosen
domain witness satisfies `(A - z) R(z) φ = φ`. -/
lemma resolvent_spec' {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H) :
    ∃ (h : Resolvent.resolvent z hz hsym hplus hminus φ ∈ A.domain),
      A ⟨Resolvent.resolvent z hz hsym hplus hminus φ, h⟩ -
      z • (Resolvent.resolvent z hz hsym hplus hminus φ) = φ := by
  have h_eq := Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists
  exact ⟨(Classical.choose
    (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists).property, h_eq⟩

end Spectra.YosidaHille.Approximation

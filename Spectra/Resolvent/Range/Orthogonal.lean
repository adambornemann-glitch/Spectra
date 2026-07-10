/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.SpecialCases
/-!
# Orthogonal Complement of the Range is Trivial

This file proves that for a self-adjoint generator `A` and any `z` with
`Im(z) ≠ 0`, the orthogonal complement of `ran(A - zI)` is trivial.

The proof exploits self-adjointness: if `χ ⊥ ran(A - zI)`, then `χ` satisfies
a "weak eigenvalue equation" `⟪Aψ, χ⟫ = z̄⟪ψ, χ⟫` for all `ψ` in the domain.
Using surjectivity at `±i`, we construct test vectors and derive `z̄ = z`,
contradicting `Im(z) ≠ 0` unless `χ = 0`.

## Main statements

* `weak_eigenvalue_of_orthogonal_to_range`: Orthogonality implies weak eigenvalue equation
* `orthogonal_range_eq_zero`: The orthogonal complement is trivial

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/
open Complex
open scoped InnerProductSpace
namespace Spectra.Resolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- If χ is orthogonal to ran(A - zI), then ⟪Aψ, χ⟫ = z̄ * ⟪ψ, χ⟫ for all ψ in the domain. -/
lemma weak_eigenvalue_of_orthogonal_to_range {A : H →ₗ.[ℂ] H} (z : ℂ) (χ : H)
    (h_orth : ∀ (ψ : A.domain), ⟪A ψ - z • (ψ : H), χ⟫_ℂ = 0) :
    ∀ (ψ : H) (hψ : ψ ∈ A.domain),
      ⟪A ⟨ψ, hψ⟩, χ⟫_ℂ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ := by
  intro ψ hψ
  have h := h_orth ⟨ψ, hψ⟩
  simp only at h
  calc ⟪A ⟨ψ, hψ⟩, χ⟫_ℂ
      = ⟪A ⟨ψ, hψ⟩ - z • ψ + z • ψ, χ⟫_ℂ := by simp
    _ = ⟪A ⟨ψ, hψ⟩ - z • ψ, χ⟫_ℂ + ⟪z • ψ, χ⟫_ℂ := by rw [inner_add_left]
    _ = 0 + ⟪z • ψ, χ⟫_ℂ := by rw [h]
    _ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ := by rw [inner_smul_left]; ring

/-- If `Aη - Iη = c • χ` (a resolvent-image equation) then `Aη = c • χ + Iη`: the shared
rearrangement underlying both `relation_from_plus_i`'s `h_Aη` step and the analogous step inside
`orthogonal_range_eq_zero`. -/
private lemma A_apply_of_sub_I_smul_eq {A : H →ₗ.[ℂ] H} {η χ : H} {c : ℂ} (hdom : η ∈ A.domain)
    (heq : A ⟨η, hdom⟩ - I • η = c • χ) :
    A ⟨η, hdom⟩ = c • χ + I • η := by
  calc A ⟨η, hdom⟩
      = (A ⟨η, hdom⟩ - I • η) + I • η := by simp
    _ = c • χ + I • η := by rw [heq]

/-- If `Aξ + Iξ = c • χ` (a resolvent-image equation) then `Aξ = c • χ - Iξ`: the shared
rearrangement underlying both `relation_from_minus_i`'s `h_Aξ` step and the analogous step inside
`orthogonal_range_eq_zero`. -/
private lemma A_apply_of_add_I_smul_eq {A : H →ₗ.[ℂ] H} {ξ χ : H} {c : ℂ} (hdom : ξ ∈ A.domain)
    (heq : A ⟨ξ, hdom⟩ + I • ξ = c • χ) :
    A ⟨ξ, hdom⟩ = c • χ - I • ξ := by
  calc A ⟨ξ, hdom⟩
      = (A ⟨ξ, hdom⟩ + I • ξ) - I • ξ := by simp
    _ = c • χ - I • ξ := by rw [heq]

/-- `conj (conj z - I) = z + I`: the conjugate identity shared by `relation_from_plus_i` and the
matching step inside `orthogonal_range_eq_zero`. -/
private lemma conj_conj_sub_I_add_I (z : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) z - I) = z + I := by
  simp only [map_sub, conj_I, sub_neg_eq_add, add_left_inj]
  exact RCLike.conj_conj z

/-- `conj (conj z + I) = z - I`: the conjugate identity shared by `relation_from_minus_i` and the
symmetric route through `conj_conj_sub_I_add_I`. -/
private lemma conj_conj_add_I_sub_I (z : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) z + I) = z - I := by
  simp only [map_add, conj_I]
  rw [RCLike.conj_conj]
  ring

/-- From orthogonality's weak eigenvalue equation and an `i`-resolvent-image vector `η` with
`Aη - iη = (z̄ - i) • χ`, derives `(z̄ + i) * ⟪η, χ⟫ = (z + i) * ‖χ‖²`. -/
private lemma relation_from_plus_i {A : H →ₗ.[ℂ] H} (z : ℂ) (χ : H)
    (h_eigen : ∀ (ψ : H) (hψ : ψ ∈ A.domain),
      ⟪A ⟨ψ, hψ⟩, χ⟫_ℂ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ)
    (η : H) (hη_dom : η ∈ A.domain)
    (hη_eq : A ⟨η, hη_dom⟩ - I • η = ((starRingEnd ℂ) z - I) • χ) :
    ((starRingEnd ℂ) z + I) * ⟪η, χ⟫_ℂ = (z + I) * ‖χ‖^2 := by
  set z_bar := (starRingEnd ℂ) z
  have h_Aη : A ⟨η, hη_dom⟩ = (z_bar - I) • χ + I • η := A_apply_of_sub_I_smul_eq hη_dom hη_eq
  have h_eigen_η : ⟪A ⟨η, hη_dom⟩, χ⟫_ℂ = z_bar * ⟪η, χ⟫_ℂ := h_eigen η hη_dom
  have h_inner_Aη : ⟪A ⟨η, hη_dom⟩, χ⟫_ℂ =
      (starRingEnd ℂ) (z_bar - I) * ‖χ‖^2 + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
    calc ⟪A ⟨η, hη_dom⟩, χ⟫_ℂ
        = ⟪(z_bar - I) • χ + I • η, χ⟫_ℂ := by rw [h_Aη]
      _ = ⟪(z_bar - I) • χ, χ⟫_ℂ + ⟪I • η, χ⟫_ℂ := by rw [inner_add_left]
      _ = (starRingEnd ℂ) (z_bar - I) * ⟪χ, χ⟫_ℂ + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
          rw [inner_smul_left, inner_smul_left]
      _ = (starRingEnd ℂ) (z_bar - I) * ‖χ‖^2 + (starRingEnd ℂ) I * ⟪η, χ⟫_ℂ := by
          rw [inner_self_eq_norm_sq_to_K]; simp
  have h_conj_zbar_minus_I : (starRingEnd ℂ) (z_bar - I) = z + I := conj_conj_sub_I_add_I z
  have h_conj_I : (starRingEnd ℂ) I = -I := Complex.conj_I
  rw [h_conj_zbar_minus_I, h_conj_I] at h_inner_Aη
  calc (z_bar + I) * ⟪η, χ⟫_ℂ
      = z_bar * ⟪η, χ⟫_ℂ + I * ⟪η, χ⟫_ℂ := by ring
    _ = ⟪A ⟨η, hη_dom⟩, χ⟫_ℂ + I * ⟪η, χ⟫_ℂ := by rw [h_eigen_η]
    _ = ((z + I) * ‖χ‖^2 + (-I) * ⟪η, χ⟫_ℂ) + I * ⟪η, χ⟫_ℂ := by rw [h_inner_Aη]
    _ = (z + I) * ‖χ‖^2 := by ring

/-- From orthogonality's weak eigenvalue equation and a `-i`-resolvent-image vector `ξ` with
`Aξ + iξ = (z̄ + i) • χ`, derives `(z̄ - i) * ⟪ξ, χ⟫ = (z - i) * ‖χ‖²`. -/
private lemma relation_from_minus_i {A : H →ₗ.[ℂ] H} (z : ℂ) (χ : H)
    (h_eigen : ∀ (ψ : H) (hψ : ψ ∈ A.domain),
      ⟪A ⟨ψ, hψ⟩, χ⟫_ℂ = (starRingEnd ℂ) z * ⟪ψ, χ⟫_ℂ)
    (ξ : H) (hξ_dom : ξ ∈ A.domain)
    (hξ_eq : A ⟨ξ, hξ_dom⟩ + I • ξ = ((starRingEnd ℂ) z + I) • χ) :
    ((starRingEnd ℂ) z - I) * ⟪ξ, χ⟫_ℂ = (z - I) * ‖χ‖^2 := by
  set z_bar := (starRingEnd ℂ) z
  have h_Aξ : A ⟨ξ, hξ_dom⟩ = (z_bar + I) • χ - I • ξ := A_apply_of_add_I_smul_eq hξ_dom hξ_eq
  have h_eigen_ξ : ⟪A ⟨ξ, hξ_dom⟩, χ⟫_ℂ = z_bar * ⟪ξ, χ⟫_ℂ := h_eigen ξ hξ_dom
  have h_inner_Aξ : ⟪A ⟨ξ, hξ_dom⟩, χ⟫_ℂ =
      (starRingEnd ℂ) (z_bar + I) * ‖χ‖^2 - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
    calc ⟪A ⟨ξ, hξ_dom⟩, χ⟫_ℂ
        = ⟪(z_bar + I) • χ - I • ξ, χ⟫_ℂ := by rw [h_Aξ]
      _ = ⟪(z_bar + I) • χ, χ⟫_ℂ - ⟪I • ξ, χ⟫_ℂ := by rw [inner_sub_left]
      _ = (starRingEnd ℂ) (z_bar + I) * ⟪χ, χ⟫_ℂ - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
          rw [inner_smul_left, inner_smul_left]
      _ = (starRingEnd ℂ) (z_bar + I) * ‖χ‖^2 - (starRingEnd ℂ) I * ⟪ξ, χ⟫_ℂ := by
          rw [inner_self_eq_norm_sq_to_K]; simp
  have h_conj_zbar_plus_I : (starRingEnd ℂ) (z_bar + I) = z - I := conj_conj_add_I_sub_I z
  have h_conj_I : (starRingEnd ℂ) I = -I := Complex.conj_I
  rw [h_conj_zbar_plus_I, h_conj_I] at h_inner_Aξ
  calc (z_bar - I) * ⟪ξ, χ⟫_ℂ
      = z_bar * ⟪ξ, χ⟫_ℂ - I * ⟪ξ, χ⟫_ℂ := by ring
    _ = ⟪A ⟨ξ, hξ_dom⟩, χ⟫_ℂ - I * ⟪ξ, χ⟫_ℂ := by rw [h_eigen_ξ]
    _ = ((z - I) * ‖χ‖^2 - (-I) * ⟪ξ, χ⟫_ℂ) - I * ⟪ξ, χ⟫_ℂ := by rw [h_inner_Aξ]
    _ = (z - I) * ‖χ‖^2 := by ring

/-- The orthogonal complement of ran(A - zI) is trivial when Im(z) ≠ 0. -/
lemma orthogonal_range_eq_zero {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) (χ : H)
    (h_orth : ∀ (ψ : A.domain), ⟪A ψ - z • (ψ : H), χ⟫_ℂ = 0) : χ = 0 := by
  set z_bar := (starRingEnd ℂ) z with hz_bar_def
  have h_eigen := weak_eigenvalue_of_orthogonal_to_range z χ h_orth
  set η := Rminus hminus ((z_bar - I) • χ)
  have hη_dom : η ∈ A.domain := Rminus_mem hminus ((z_bar - I) • χ)
  have hη_eq : A ⟨η, hη_dom⟩ - I • η = (z_bar - I) • χ :=
    Rminus_eq hminus ((z_bar - I) • χ)
  set ξ := Rplus hplus ((z_bar + I) • χ)
  have hξ_dom : ξ ∈ A.domain := Rplus_mem hplus ((z_bar + I) • χ)
  have hξ_eq : A ⟨ξ, hξ_dom⟩ + I • ξ = (z_bar + I) • χ :=
    Rplus_eq hplus ((z_bar + I) • χ)
  have h_relation_η := relation_from_plus_i z χ h_eigen η hη_dom hη_eq
  have h_relation_ξ := relation_from_minus_i z χ h_eigen ξ hξ_dom hξ_eq
  have h_sym : ⟪A ⟨η, hη_dom⟩, ξ⟫_ℂ = ⟪η, A ⟨ξ, hξ_dom⟩⟫_ℂ :=
    hsym ⟨η, hη_dom⟩ ⟨ξ, hξ_dom⟩
  have h_Aη : A ⟨η, hη_dom⟩ = (z_bar - I) • χ + I • η := A_apply_of_sub_I_smul_eq hη_dom hη_eq
  have h_Aξ : A ⟨ξ, hξ_dom⟩ = (z_bar + I) • χ - I • ξ := A_apply_of_add_I_smul_eq hξ_dom hξ_eq
  have h_conj_zbar_minus_I : (starRingEnd ℂ) (z_bar - I) = z + I := conj_conj_sub_I_add_I z
  have h_conj_I : (starRingEnd ℂ) I = -I := Complex.conj_I
  have h_LHS : ⟪A ⟨η, hη_dom⟩, ξ⟫_ℂ = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
    calc ⟪A ⟨η, hη_dom⟩, ξ⟫_ℂ
        = ⟪(z_bar - I) • χ + I • η, ξ⟫_ℂ := by rw [h_Aη]
      _ = ⟪(z_bar - I) • χ, ξ⟫_ℂ + ⟪I • η, ξ⟫_ℂ := by rw [inner_add_left]
      _ = (starRingEnd ℂ) (z_bar - I) * ⟪χ, ξ⟫_ℂ + (starRingEnd ℂ) I * ⟪η, ξ⟫_ℂ := by
          rw [inner_smul_left, inner_smul_left]
      _ = (z + I) * ⟪χ, ξ⟫_ℂ + (-I) * ⟪η, ξ⟫_ℂ := by rw [h_conj_zbar_minus_I, h_conj_I]
      _ = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by ring
  have h_RHS : ⟪η, A ⟨ξ, hξ_dom⟩⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
    calc ⟪η, A ⟨ξ, hξ_dom⟩⟫_ℂ
        = ⟪η, (z_bar + I) • χ - I • ξ⟫_ℂ := by rw [h_Aξ]
      _ = ⟪η, (z_bar + I) • χ⟫_ℂ - ⟪η, I • ξ⟫_ℂ := by rw [inner_sub_right]
      _ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by rw [inner_smul_right, inner_smul_right]
  have h_cancel : (z + I) * ⟪χ, ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ := by
    have h : (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ := by
      rw [← h_LHS, ← h_RHS, h_sym]
    calc (z + I) * ⟪χ, ξ⟫_ℂ
        = (z + I) * ⟪χ, ξ⟫_ℂ - I * ⟪η, ξ⟫_ℂ + I * ⟪η, ξ⟫_ℂ := by ring
      _ = (z_bar + I) * ⟪η, χ⟫_ℂ - I * ⟪η, ξ⟫_ℂ + I * ⟪η, ξ⟫_ℂ := by rw [h]
      _ = (z_bar + I) * ⟪η, χ⟫_ℂ := by ring
  have h_chi_xi_eq : (z + I) * ⟪χ, ξ⟫_ℂ = (z + I) * ‖χ‖^2 := by
    calc (z + I) * ⟪χ, ξ⟫_ℂ
        = (z_bar + I) * ⟪η, χ⟫_ℂ := h_cancel
      _ = (z + I) * ‖χ‖^2 := h_relation_η
  have hχ0 : (‖χ‖^2 : ℂ) = 0 → χ = 0 := fun h =>
    norm_eq_zero.mp (Complex.ofReal_eq_zero.mp (sq_eq_zero_iff.mp h))
  by_cases h_z_eq_neg_I : z = -I
  · have h_zbar_eq : z_bar = I := by
      simp only [hz_bar_def, h_z_eq_neg_I, map_neg, Complex.conj_I]; ring
    have h_zbar_minus_I : z_bar - I = 0 := by rw [h_zbar_eq]; ring
    have h_z_minus_I : z - I = -2 * I := by rw [h_z_eq_neg_I]; ring
    rw [h_zbar_minus_I, h_z_minus_I] at h_relation_ξ
    simp only [zero_mul] at h_relation_ξ
    have h_two_I_ne : (-2 : ℂ) * I ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, neg_eq_zero,
        OfNat.ofNat_ne_zero, or_self, not_false_eq_true]
    have h_norm_sq_zero : (‖χ‖^2 : ℂ) = 0 := by
      have := mul_eq_zero.mp h_relation_ξ.symm
      cases this with
      | inl h => exact absurd h h_two_I_ne
      | inr h => exact h
    exact hχ0 h_norm_sq_zero
  · have h_z_plus_i_ne : z + I ≠ 0 := by
      intro h_eq
      apply h_z_eq_neg_I
      calc z = z + I - I := by ring
        _ = 0 - I := by rw [h_eq]
        _ = -I := by ring
    have h_inner_chi_xi : ⟪χ, ξ⟫_ℂ = ‖χ‖^2 := by
      have := mul_left_cancel₀ h_z_plus_i_ne h_chi_xi_eq
      calc ⟪χ, ξ⟫_ℂ = (‖χ‖^2 : ℂ) := this
        _ = ‖χ‖^2 := by norm_cast
    have h_inner_xi_chi : ⟪ξ, χ⟫_ℂ = ‖χ‖^2 := by
      have h1 : ⟪ξ, χ⟫_ℂ = (starRingEnd ℂ) ⟪χ, ξ⟫_ℂ := (inner_conj_symm ξ χ).symm
      rw [h_inner_chi_xi] at h1
      simp only [map_pow, conj_ofReal] at h1
      exact h1
    have h_final : (z_bar - I) * (‖χ‖^2 : ℂ) = (z - I) * ‖χ‖^2 := by
      calc (z_bar - I) * (‖χ‖^2 : ℂ)
          = (z_bar - I) * ⟪ξ, χ⟫_ℂ := by rw [← h_inner_xi_chi]
        _ = (z - I) * ↑‖χ‖^2 := h_relation_ξ
    have h_diff_zero : (z_bar - z) * (‖χ‖^2 : ℂ) = 0 := by
      have : (z_bar - I) * (‖χ‖^2 : ℂ) - (z - I) * ‖χ‖^2 = 0 := by
        rw [h_final]; ring
      calc (z_bar - z) * (‖χ‖^2 : ℂ)
          = (z_bar - I - (z - I)) * ‖χ‖^2 := by ring
        _ = (z_bar - I) * ‖χ‖^2 - (z - I) * ‖χ‖^2 := by ring
        _ = 0 := this
    have h_zbar_minus_z_ne : z_bar - z ≠ 0 := by
      intro h_eq
      have h_zbar_eq_z : z_bar = z := sub_eq_zero.mp h_eq
      have h_im_zero : z.im = 0 := by
        have h1 : ((starRingEnd ℂ) z).im = z.im := by
          rw [hz_bar_def] at h_zbar_eq_z
          exact congrArg Complex.im h_zbar_eq_z
        simp only [Complex.conj_im] at h1
        linarith
      exact hz h_im_zero
    have h_norm_sq_zero : (‖χ‖^2 : ℂ) = 0 := by
      have := mul_eq_zero.mp h_diff_zero
      cases this with
      | inl h => exact absurd h h_zbar_minus_z_ne
      | inr h => exact h
    exact hχ0 h_norm_sq_zero

end Spectra.Resolvent

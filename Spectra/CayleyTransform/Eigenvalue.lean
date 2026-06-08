/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: CayleyTransform/EigenValue.lean
-/
import Spectra.CayleyTransform.Transform
import Spectra.CayleyTransform.Mobius
/-!
# Eigenvalue Correspondence for the Cayley Transform

This file proves the eigenvalue correspondence between a self-adjoint operator `A` and
its Cayley transform `U`: real eigenvalues `μ` of `A` correspond to eigenvalues
`(μ - i)/(μ + i)` of `U` on the unit circle.

## Main statements

* `cayley_neg_one_eigenvalue_iff`: `-1` is an eigenvalue of `U` iff `0` is an eigenvalue of `A`
* `cayley_eigenvalue_correspondence`: `μ ∈ ℝ` is an eigenvalue of `A` iff
  `(μ - i)/(μ + i)` is an eigenvalue of `U`
* `cayley_shift_identity`: Key identity relating `(U - w)φ` to `(A - μ)ψ`
-/
open InnerProductSpace MeasureTheory Complex Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
open Spectra.QuantumMechanics

namespace Spectra.Cayley

/-- `−1` is an eigenvalue of `U` iff `0` is an eigenvalue of `A`. -/
theorem cayley_neg_one_eigenvalue_iff
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform hsym hplus φ = -φ) ↔
    (∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = 0) := by
  constructor
  · rintro ⟨φ, hφ_ne, hUφ⟩
    obtain ⟨ψ, hψ⟩ := hplus φ
    have hCφ : cayleyTransform hsym hplus φ = A ψ - I • (ψ : H) := by
      rw [← hψ]; exact cayleyTransform_apply_resolvent hsym hplus ψ
    have hAψ0 : A ψ = 0 := by
      have heq : A ψ - I • (ψ : H) = -(A ψ + I • (ψ : H)) := by
        rw [← hCφ, hUφ, ← hψ]
      have e : (A ψ - I • (ψ : H)) + (A ψ + I • (ψ : H)) = (2 : ℂ) • A ψ := by module
      have h2 : (2 : ℂ) • A ψ = 0 := by rw [← e, heq]; abel
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    refine ⟨ψ, ?_, hAψ0⟩
    intro hψ0
    apply hφ_ne
    rw [← hψ, hAψ0, hψ0]; simp
  · rintro ⟨ψ, hψ_ne, hAψ⟩
    have hφ_eq : A ψ + I • (ψ : H) = I • (ψ : H) := by rw [hAψ, zero_add]
    refine ⟨I • (ψ : H), ?_, ?_⟩
    · intro h
      exact hψ_ne ((smul_eq_zero.mp h).resolve_left Complex.I_ne_zero)
    · have hCφ : cayleyTransform hsym hplus (I • (ψ : H)) = A ψ - I • (ψ : H) := by
        have h := cayleyTransform_apply_resolvent hsym hplus ψ
        rwa [hφ_eq] at h
      rw [hCφ, hAψ, zero_sub]

open ContinuousLinearMap in
/-- Key identity: `(U − w)φ = (1 − w)(Aψ − μψ)` where `φ = (A + iI)ψ`, `w = (μ−i)/(μ+i)`. -/
lemma cayley_shift_identity
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (μ : ℝ) (hμ_ne : (↑μ : ℂ) + I ≠ 0) (ψ : A.domain) :
    (cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H)
        (A ψ + I • (ψ : H))
      = ((1 : ℂ) - (↑μ - I) * (↑μ + I)⁻¹) • (A ψ - (↑μ : ℂ) • (ψ : H)) := by
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw
  have h_Uφ : cayleyTransform hsym hplus (A ψ + I • (ψ : H)) = A ψ - I • (ψ : H) :=
    cayleyTransform_apply_resolvent hsym hplus ψ
  have h_coeff : I * ((1 : ℂ) + w) = ((1 : ℂ) - w) * ↑μ := mobius_coeff_identity μ hμ_ne
  simp only [sub_apply, smul_apply, id_apply, h_Uφ]
  have key : A ψ - I • (ψ : H) - w • (A ψ + I • (ψ : H))
           = (1 - w) • A ψ - (I * ((1 : ℂ) + w)) • (ψ : H) := by rw [smul_add]; module
  rw [key, h_coeff, mul_smul, ← smul_sub]

/-- Real eigenvalues of `A` correspond to eigenvalues of `U` via the Möbius map. -/
theorem cayley_eigenvalue_correspondence
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ) :
    (∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = (↑μ : ℂ) • (ψ : H)) ↔
    (∃ φ : H, φ ≠ 0 ∧ cayleyTransform hsym hplus φ = ((↑μ - I) * (↑μ + I)⁻¹) • φ) := by
  set w := (↑μ - I) * (↑μ + I)⁻¹ with hw_def
  have hμ_ne : (↑μ : ℂ) + I ≠ 0 := by
    intro h
    have him : ((↑μ : ℂ) + I).im = 0 := by rw [h]; simp
    simp at him
  constructor
  · rintro ⟨ψ, hψ_ne, h_eig⟩
    have hφ_ne : A ψ + I • (ψ : H) ≠ 0 := by
      rw [h_eig, ← add_smul]
      intro h
      rcases smul_eq_zero.mp h with h | h
      · exact hμ_ne h
      · exact hψ_ne h
    refine ⟨A ψ + I • (ψ : H), hφ_ne, ?_⟩
    have h_Uφ : cayleyTransform hsym hplus (A ψ + I • (ψ : H)) = A ψ - I • (ψ : H) :=
      cayleyTransform_apply_resolvent hsym hplus ψ
    rw [h_Uφ, h_eig, ← sub_smul, ← add_smul, smul_smul, hw_def, inv_mul_cancel_right₀ hμ_ne]
  · rintro ⟨φ, hφ_ne, h_eig⟩
    obtain ⟨ψ₀, hψ₀⟩ := hplus φ
    have h_Uφ : cayleyTransform hsym hplus φ = A ψ₀ - I • (ψ₀ : H) := by
      rw [← hψ₀]; exact cayleyTransform_apply_resolvent hsym hplus ψ₀
    have hψ_ne : (ψ₀ : H) ≠ 0 := fun h => hφ_ne <| by
      rw [← hψ₀, show ψ₀ = 0 from by ext; simpa using h]; simp
    have hw_ne_one : w ≠ 1 := by
      intro h_eq
      rw [hw_def] at h_eq
      have h1 : (↑μ : ℂ) - I = ↑μ + I := by
        have h := congrArg (· * (↑μ + I)) h_eq
        rwa [inv_mul_cancel_right₀ hμ_ne, one_mul] at h
      exact (mul_ne_zero two_ne_zero Complex.I_ne_zero) (by linear_combination -h1)
    have h_one_sub_ne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne_one)
    have h_collect : (1 - w) • A ψ₀ = (I + w * I) • (ψ₀ : H) := by
      have h_key : A ψ₀ - I • (ψ₀ : H) = w • (A ψ₀ + I • (ψ₀ : H)) := by
        rw [← h_Uφ, h_eig, hψ₀]
      have e : (1 - w) • A ψ₀ - (I + w * I) • (ψ₀ : H)
             = (A ψ₀ - I • (ψ₀ : H)) - w • (A ψ₀ + I • (ψ₀ : H)) := by module
      rw [← sub_eq_zero, e, h_key, sub_self]
    have hcoeff : I + w * I = (1 - w) * ↑μ := by
      have e : I + w * I = I * (1 + w) := by ring
      rw [e]; exact mobius_coeff_identity μ hμ_ne
    refine ⟨ψ₀, hψ_ne, ?_⟩
    calc A ψ₀
        = (1 - w)⁻¹ • (1 - w) • A ψ₀ := by
          rw [smul_smul, inv_mul_cancel₀ h_one_sub_ne, one_smul]
      _ = (1 - w)⁻¹ • (I + w * I) • (ψ₀ : H) := by rw [h_collect]
      _ = ((1 - w)⁻¹ * (I + w * I)) • (ψ₀ : H) := by rw [smul_smul]
      _ = (↑μ : ℂ) • (ψ₀ : H) := by
          congr 1
          rw [hcoeff, ← mul_assoc, inv_mul_cancel₀ h_one_sub_ne, one_mul]

/-- `(U − w)` is injective when `A − μ` is bounded below. -/
lemma cayley_shift_injective
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ)
    (hC : ∃ C > 0, ∀ ψ (hψ : ψ ∈ A.domain),
            ‖A ⟨ψ, hψ⟩ - (↑μ : ℂ) • ψ‖ ≥ C * ‖ψ‖) :
    let U := cayleyTransform hsym hplus
    let w := (↑μ - I) * (↑μ + I)⁻¹
    Function.Injective (U - w • ContinuousLinearMap.id ℂ H) := by
  intro U w φ₁ φ₂ h_eq
  rw [← sub_eq_zero]
  set φ := φ₁ - φ₂ with hφ_def
  have h_zero : (U - w • ContinuousLinearMap.id ℂ H) φ = 0 := by
    rw [hφ_def, map_sub, h_eq, sub_self]
  by_contra hφ_ne
  have h_eig : U φ = w • φ := by
    have h := h_zero
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
               ContinuousLinearMap.id_apply, sub_eq_zero] at h
    exact h
  have h_exists : ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ A ψ = (↑μ : ℂ) • (ψ : H) := by
    rw [cayley_eigenvalue_correspondence hsym hplus μ]
    exact ⟨φ, hφ_ne, h_eig⟩
  obtain ⟨ψ, hψ_ne, h_Aψ⟩ := h_exists
  obtain ⟨C, hC_pos, hC_bound⟩ := hC
  have h_bound := hC_bound (ψ : H) ψ.2
  simp only [Subtype.coe_eta] at h_bound
  rw [h_Aψ, sub_self, norm_zero] at h_bound
  have hψ_zero : ‖(ψ : H)‖ = 0 := by nlinarith [norm_nonneg (ψ : H)]
  exact hψ_ne (norm_eq_zero.mp hψ_zero)

end Spectra.Cayley

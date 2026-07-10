/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Defs
/-!
# The Inverse Cayley Transform

This file develops the inverse Cayley transform, recovering the generator `A` from the
unitary operator `U`, and proves the fundamental domain characterization `dom(A) = range(I - U)`.

## Main definitions

* `inverseCayleyOp`: The inverse Cayley transform recovering `A` from `U`

## Main statements

* `one_minus_cayley_apply`: Formula for `(I - U)φ` on range elements
* `one_plus_cayley_apply`: Formula for `(I + U)φ` on range elements
* `inverse_cayley_formula`: Both formulas combined
* `inverseCayleyOp_symmetric`: The inverse Cayley transform is symmetric
* `generator_domain_eq_range_one_minus_cayley`: `dom(A) = range(I - U)`
-/
open Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Spectra.Cayley

/-- Formula for `(I − U)φ` where `φ = (A + iI)ψ`. -/
lemma one_minus_cayley_apply
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (ψ : A.domain) :
    (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ψ + I • (ψ : H))
      = (2 * I) • (ψ : H) := by
  have h := cayleyTransform_apply_resolvent hsym hplus ψ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [h]; module

/-- Formula for `(I + U)φ` where `φ = (A + iI)ψ`. -/
lemma one_plus_cayley_apply
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (ψ : A.domain) :
    (ContinuousLinearMap.id ℂ H + cayleyTransform hsym hplus) (A ψ + I • (ψ : H))
      = (2 : ℂ) • A ψ := by
  have h := cayleyTransform_apply_resolvent hsym hplus ψ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply]
  rw [h]; module

/-- The relation `(2i)Aψ = i(I + U)φ` for `φ = (A + iI)ψ`. -/
lemma inverse_cayley_relation
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (ψ : A.domain) :
    (2 * I) • A ψ
      = I • ((ContinuousLinearMap.id ℂ H + cayleyTransform hsym hplus) (A ψ + I • (ψ : H))) := by
  rw [one_plus_cayley_apply hsym hplus ψ]; module

/-- Combined formulas for `(I − U)φ` and `(I + U)φ`. -/
lemma inverse_cayley_formula
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (ψ : A.domain) :
    (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ψ + I • (ψ : H))
      = (2 * I) • (ψ : H) ∧
    (ContinuousLinearMap.id ℂ H + cayleyTransform hsym hplus) (A ψ + I • (ψ : H)) = (2 : ℂ) • A ψ :=
  ⟨one_minus_cayley_apply hsym hplus ψ, one_plus_cayley_apply hsym hplus ψ⟩

/-- Every domain element lies in the range of `I − U` (up to the scalar `2i`). -/
lemma range_one_minus_cayley
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    ∀ ψ : H, ψ ∈ A.domain →
      ∃ φ : H, (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) φ = (2 * I) • ψ := by
  intro ψ hψ
  exact ⟨A ⟨ψ, hψ⟩ + I • ψ, one_minus_cayley_apply hsym hplus ⟨ψ, hψ⟩⟩

/-- Recovery formula: `ψ = (−i/2)(I − U)φ`. -/
lemma inverse_cayley_domain
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (ψ : A.domain) :
    (ψ : H)
      = ((-I) / 2) •
          ((ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ψ + I • (ψ : H))) := by
  have hscal : (-I) / 2 * (2 * I) = 1 := by
    rw [div_mul_eq_mul_div, mul_comm (2 : ℂ) I, ← mul_assoc, neg_mul, Complex.I_mul_I]
    norm_num
  rw [one_minus_cayley_apply hsym hplus ψ, smul_smul, hscal, one_smul]

/-- Bijection formulas: recovering both `ψ` and `Aψ` from `φ`. -/
lemma cayley_bijection
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (ψ : A.domain) :
    ((-I) / 2) •
        ((ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ψ + I • (ψ : H))) = (ψ : H) ∧
    ((1 : ℂ) / 2) •
        ((ContinuousLinearMap.id ℂ H + cayleyTransform hsym hplus) (A ψ + I • (ψ : H))) = A ψ := by
  refine ⟨(inverse_cayley_domain hsym hplus ψ).symm, ?_⟩
  rw [one_plus_cayley_apply hsym hplus ψ, smul_smul, show (1 : ℂ) / 2 * 2 = 1 by norm_num, one_smul]

open InnerProductSpace in
/-- The inverse Cayley transform as a linear map on `range(I - U)`. -/
noncomputable def inverseCayleyOp (U : H →L[ℂ] H)
    (_ : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)
    (_ : ∀ ψ, U ψ = -ψ → ψ = 0) :
    LinearMap.range (↑(ContinuousLinearMap.id ℂ H - U) : H →ₗ[ℂ] H) →ₗ[ℂ] H where
  toFun := fun ⟨φ, hφ⟩ =>
    let ψ := Classical.choose hφ
    I • (U ψ + ψ)
  map_add' := by
    intro ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
    simp only [smul_add]
    set ψ₁ := Classical.choose hφ₁ with _hψ₁_def
    set ψ₂ := Classical.choose hφ₂ with _hψ₂_def
    have hψ₁ : (ContinuousLinearMap.id ℂ H - U) ψ₁ = φ₁ := Classical.choose_spec hφ₁
    have hψ₂ : (ContinuousLinearMap.id ℂ H - U) ψ₂ = φ₂ := Classical.choose_spec hφ₂
    have hφ₁₂ : ∃ ψ, (ContinuousLinearMap.id ℂ H - U) ψ = φ₁ + φ₂ := ⟨ψ₁ + ψ₂, by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_add]
      rw [← hψ₁, ← hψ₂]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]⟩
    set ψ₁₂ := Classical.choose hφ₁₂ with _hψ₁₂_def
    have hψ₁₂ : (ContinuousLinearMap.id ℂ H - U) ψ₁₂ = φ₁ + φ₂ := Classical.choose_spec hφ₁₂
    have h_diff : ψ₁₂ = ψ₁ + ψ₂ := by
      have h_eq : (ContinuousLinearMap.id ℂ H - U) ψ₁₂ =
                  (ContinuousLinearMap.id ℂ H - U) (ψ₁ + ψ₂) := by
        rw [hψ₁₂]
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_add]
        rw [← hψ₁, ← hψ₂]
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      have h_sub : (ContinuousLinearMap.id ℂ H - U) (ψ₁₂ - (ψ₁ + ψ₂)) = 0 := by
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
                   map_sub, map_add]
        rw [sub_eq_zero]
        convert h_eq using 1
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
        rw [map_add]
        abel
      have h_fixed : U (ψ₁₂ - (ψ₁ + ψ₂)) = ψ₁₂ - (ψ₁ + ψ₂) := by
        have : ψ₁₂ - (ψ₁ + ψ₂) - U (ψ₁₂ - (ψ₁ + ψ₂)) = 0 := by
          convert h_sub using 1
        exact (sub_eq_zero.mp this).symm
      exact eq_of_sub_eq_zero (h_one _ h_fixed)
    rw [h_diff, map_add]
    simp only [smul_add]
    abel
  map_smul' := by
    intro c ⟨φ, hφ⟩
    simp only [RingHom.id_apply, smul_add]
    set ψ := Classical.choose hφ with _hψ_def
    have hψ : (ContinuousLinearMap.id ℂ H - U) ψ = φ := Classical.choose_spec hφ
    have hcφ : ∃ ψ', (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := ⟨c • ψ, by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_smul]
      rw [← hψ]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]⟩
    set ψ' := Classical.choose hcφ with _hψ'_def
    have hψ' : (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := Classical.choose_spec hcφ
    have h_diff : ψ' = c • ψ := by
      have h_sub : (ContinuousLinearMap.id ℂ H - U) (ψ' - c • ψ) = 0 := by
        have eq1 : (ContinuousLinearMap.id ℂ H - U) ψ' = c • φ := hψ'
        have eq2 : (ContinuousLinearMap.id ℂ H - U) ψ = φ := hψ
        simp only [map_sub, map_smul, eq1, eq2]
        abel
      have h_fixed : U (ψ' - c • ψ) = ψ' - c • ψ := by
        have : ψ' - c • ψ - U (ψ' - c • ψ) = 0 := by
          convert h_sub using 1
        exact (sub_eq_zero.mp this).symm
      exact eq_of_sub_eq_zero (h_one _ h_fixed)
    rw [h_diff, map_smul, smul_comm c I (U ψ), smul_comm c I ψ]

open InnerProductSpace in
/-- The inverse Cayley transform is symmetric. -/
lemma inverseCayleyOp_symmetric (U : H →L[ℂ] H)
    (hU : ∀ ψ φ, ⟪U ψ, U φ⟫_ℂ = ⟪ψ, φ⟫_ℂ)
    (h_one : ∀ ψ, U ψ = ψ → ψ = 0)
    (h_neg_one : ∀ ψ, U ψ = -ψ → ψ = 0) :
    ∀ ψ φ : LinearMap.range (↑(ContinuousLinearMap.id ℂ H - U) : H →ₗ[ℂ] H),
      ⟪inverseCayleyOp U hU h_one h_neg_one ψ, (φ : H)⟫_ℂ =
      ⟪(ψ : H), inverseCayleyOp U hU h_one h_neg_one φ⟫_ℂ := by
  intro ⟨φ₁, hφ₁⟩ ⟨φ₂, hφ₂⟩
  set χ₁ := Classical.choose hφ₁ with _hχ₁_def
  set χ₂ := Classical.choose hφ₂ with _hχ₂_def
  have hχ₁ : (ContinuousLinearMap.id ℂ H - U) χ₁ = φ₁ := Classical.choose_spec hφ₁
  have hχ₂ : (ContinuousLinearMap.id ℂ H - U) χ₂ = φ₂ := Classical.choose_spec hφ₂
  have hφ₁_eq : φ₁ = χ₁ - U χ₁ := by
    rw [← hχ₁]; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have hφ₂_eq : φ₂ = χ₂ - U χ₂ := by
    rw [← hχ₂]; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  have _hcoe₁ :
      (⟨φ₁, hφ₁⟩ : LinearMap.range (↑(ContinuousLinearMap.id ℂ H - U) : H →ₗ[ℂ] H)).val = φ₁ := rfl
  have _hcoe₂ :
      (⟨φ₂, hφ₂⟩ : LinearMap.range (↑(ContinuousLinearMap.id ℂ H - U) : H →ₗ[ℂ] H)).val = φ₂ := rfl
  change ⟪I • (U χ₁ + χ₁), φ₂⟫_ℂ = ⟪φ₁, I • (U χ₂ + χ₂)⟫_ℂ
  rw [hφ₁_eq, hφ₂_eq]
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  rw [inner_add_left, inner_sub_right, inner_sub_right]
  rw [inner_sub_left, inner_add_right, inner_add_right]
  rw [hU χ₁ χ₂]
  simp only [RCLike.star_def, conj_I, sub_add_sub_cancel, neg_mul]
  ring

/-- The domain of `A` equals the range of `I − U`:  `dom A = ran (I − U)`. -/
theorem generator_domain_eq_range_one_minus_cayley
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    (A.domain : Set H)
      = ↑(LinearMap.range
          (↑(ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) : H →ₗ[ℂ] H)) := by
  have hne : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  ext ψ
  constructor
  · intro hψ
    rw [SetLike.mem_coe] at hψ
    rw [SetLike.mem_coe, LinearMap.mem_range]
    have h_apply : (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) (A ⟨ψ, hψ⟩ + I • ψ)
        = (2 * I) • ψ := one_minus_cayley_apply hsym hplus ⟨ψ, hψ⟩
    refine ⟨(2 * I)⁻¹ • (A ⟨ψ, hψ⟩ + I • ψ), ?_⟩
    rw [map_smul, ContinuousLinearMap.coe_coe, h_apply, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · intro hψ
    rw [SetLike.mem_coe, LinearMap.mem_range] at hψ
    obtain ⟨χ, hχ⟩ := hψ
    rw [ContinuousLinearMap.coe_coe] at hχ
    obtain ⟨η, hη⟩ := hplus χ
    have h_Uχ : cayleyTransform hsym hplus χ = A η - I • (η : H) := by
      rw [← hη]; exact cayleyTransform_apply_resolvent hsym hplus η
    have h_diff :
        (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) χ = (2 * I) • (η : H) := by
      have hsplit : (ContinuousLinearMap.id ℂ H - cayleyTransform hsym hplus) χ
          = χ - cayleyTransform hsym hplus χ := by
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      rw [hsplit, h_Uχ, ← hη]; module
    rw [SetLike.mem_coe, ← hχ, h_diff]
    exact Submodule.smul_mem A.domain (2 * I) η.2


end Spectra.Cayley

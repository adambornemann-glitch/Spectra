/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.YosidaHille.Basic
import Spectra.Operator.SelfAdjoint
import Spectra.Resolvent.SpecialCases
import Spectra.Resolvent.NormExpansion
import Spectra.Resolvent.Integral.Domain
import Spectra.Operator.Unitary.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
/-!
# The Cayley Transform

This file defines the Cayley transform of a self-adjoint generator and proves its
fundamental properties: it is an isometry, surjective, and unitary.
-/
open Complex
open Spectra.Resolvent
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.Operator
open SelfAdjointOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace Spectra.Cayley

/-- Cayley transform `C = I − 2i (A + iI)⁻¹` of a symmetric `A` with full lower deficiency. -/
noncomputable def cayleyTransform
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - (2 * I) • resolventAtNegI hsym hplus

/-- The defining action: `C (A+iI)ψ = (A−iI)ψ`. Uses only the left-inverse + linearity. -/
lemma cayleyTransform_apply_resolvent
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (ψ : A.domain) :
    cayleyTransform hsym hplus (A ψ + I • (ψ : H)) = A ψ - I • (ψ : H) := by
  have h := resolvent_at_neg_i_left_inverse hsym hplus (ψ : H) ψ.2  -- ⟨(ψ:H),ψ.2⟩ = ψ defeq
  simp only [cayleyTransform, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply]
  rw [h]; module

/-- The Cayley transform is an isometry. -/
theorem cayleyTransform_isometry
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (φ : H) :
    ‖cayleyTransform hsym hplus φ‖ = ‖φ‖ := by
  obtain ⟨ψ, hψ⟩ := hplus φ
  have hcay : cayleyTransform hsym hplus φ = A ψ - I • (ψ : H) := by
    rw [← hψ]; exact cayleyTransform_apply_resolvent hsym hplus ψ
  have hsq : ‖cayleyTransform hsym hplus φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [hcay, norm_sq_sub_I_smul hsym ψ, ← hψ, norm_sq_add_I_smul hsym ψ]
  nlinarith [hsq, norm_nonneg (cayleyTransform hsym hplus φ), norm_nonneg φ,
             sq_nonneg (‖cayleyTransform hsym hplus φ‖ - ‖φ‖)]

/-- The Cayley transform is surjective (full lower deficiency). -/
theorem cayleyTransform_surjective
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    Function.Surjective (cayleyTransform hsym hplus) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := hminus χ
  exact ⟨A ψ + I • (ψ : H), by rw [cayleyTransform_apply_resolvent hsym hplus ψ]; exact hψ⟩

open InnerProductSpace in
/-- The Cayley transform of a self-adjoint operator is unitary. -/
theorem cayleyTransform_unitary [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    Unitary (cayleyTransform hsym hplus) := by
  set U := cayleyTransform hsym hplus with hU
  have h_isometry : ∀ x, ‖U x‖ = ‖x‖ := by
    intro x; rw [hU]; exact cayleyTransform_isometry hsym hplus x
  -- `U` preserves the inner product, by complex polarization from the isometry.
  have h_inner : ∀ φ ψ : H, ⟪U φ, U ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
    let L : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, h_isometry⟩
    intro φ ψ
    exact L.inner_map_map φ ψ
  -- `U⋆U = 1` is now immediate from inner-product preservation.
  have h_star_self : U.adjoint * U = 1 := by
    ext φ
    apply ext_inner_left ℂ
    intro ψ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact h_inner ψ φ
  -- `UU⋆ = 1` from surjectivity plus the line above.
  have h_self_star : U * U.adjoint = 1 := by
    ext φ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
    obtain ⟨ψ, hψ⟩ := cayleyTransform_surjective hsym hplus hminus φ
    have hUψ : U ψ = φ := by rw [hU]; exact hψ
    have hadj : U.adjoint (U ψ) = ψ := by
      have h := congrFun (congrArg DFunLike.coe h_star_self) ψ
      simpa using h
    rw [← hUψ, hadj]
  exact ⟨h_star_self, h_self_star⟩

/-- The Cayley transform of a self-adjoint operator, as an element of Mathlib's `unitary`. -/
theorem cayleyTransform_mem_unitary [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    cayleyTransform hsym hplus ∈ unitary (H →L[ℂ] H) :=
  (mem_unitary_iff_Unitary _).mpr (cayleyTransform_unitary hsym hplus hminus)

/-- The spectrum of the Cayley transform of `A` lies on the unit circle, since the transform is
unitary. -/
lemma cayleyTransform_spectrum_subset_circle [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    spectrum ℂ (cayleyTransform hsym hplus) ⊆ Metric.sphere (0 : ℂ) 1 :=
  spectrum.subset_circle_of_unitary (cayleyTransform_mem_unitary hsym hplus hminus)

/-- `U U⋆ = I` for the Cayley transform. -/
lemma cayleyTransform_comp_adjoint [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    (cayleyTransform hsym hplus).comp (cayleyTransform hsym hplus).adjoint =
      ContinuousLinearMap.id ℂ H :=
  (cayleyTransform_unitary hsym hplus hminus).2

/-- `U⋆ U = I` for the Cayley transform. -/
lemma cayleyTransform_adjoint_comp [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    (cayleyTransform hsym hplus).adjoint.comp (cayleyTransform hsym hplus) =
      ContinuousLinearMap.id ℂ H :=
  (cayleyTransform_unitary hsym hplus hminus).1

/-- The Cayley transform is invertible. -/
lemma cayleyTransform_isUnit [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    IsUnit (cayleyTransform hsym hplus) := by
  refine ⟨⟨cayleyTransform hsym hplus, (cayleyTransform hsym hplus).adjoint, ?_, ?_⟩, rfl⟩
  · exact cayleyTransform_comp_adjoint hsym hplus hminus
  · exact cayleyTransform_adjoint_comp hsym hplus hminus

/-- The operator norm of the Cayley transform is `1`. -/
theorem cayleyTransform_norm_one [Nontrivial H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) :
    ‖cayleyTransform hsym hplus‖ = 1 := by
  set U := cayleyTransform hsym hplus with hU
  have h_norm : ∀ ψ, ‖U ψ‖ = ‖ψ‖ := fun ψ => by
    rw [hU]; exact cayleyTransform_isometry hsym hplus ψ
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun ψ => by simp only [one_mul, h_norm, le_refl])
  · obtain ⟨ψ, hψ⟩ := exists_ne (0 : H)
    have hψ' : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    calc 1 = ‖U ψ‖ / ‖ψ‖ := by rw [h_norm ψ, div_self hψ']
      _ ≤ ‖U‖ := ContinuousLinearMap.ratio_le_opNorm U ψ

/-- For symmetric operators, `‖Aψ + iψ‖² = ‖Aψ‖² + ‖ψ‖²`. -/
lemma symmetric_norm_sq_add
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖A ψ + I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 :=
  norm_sq_add_I_smul hsym ψ

/-- The Cayley transform of a self-adjoint operator is a normal element of the
C⋆-algebra `H →L[ℂ] H`. This is the gate to Mathlib's `cfc`. -/
lemma cayleyTransform_isStarNormal [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    IsStarNormal (cayleyTransform hsym hplus) := by
  have hU := cayleyTransform_unitary hsym hplus hminus
  refine ⟨?_⟩
  change star (cayleyTransform hsym hplus) * cayleyTransform hsym hplus
      = cayleyTransform hsym hplus * star (cayleyTransform hsym hplus)
  rw [ContinuousLinearMap.star_eq_adjoint, hU.1, hU.2]

end Spectra.Cayley

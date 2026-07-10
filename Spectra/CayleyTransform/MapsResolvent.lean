/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Eigenvalue
import Spectra.Resolvent.SpecialCases

/-!
# The Cayley transform maps the resolvent set

This file identifies the resolvent `(A + iI)⁻¹` with the continuous functional calculus of the
Cayley transform `U` at `w ↦ (1 - w)/(2i)` (`resolvent_at_neg_i_eq_cfc`), and uses this together
with the unitarity of `U` to show that every non-real `z` lies in the resolvent set of `A`: the
Möbius image `w = (z - i)/(z + i)` falls off the unit circle, so `U - w` is a unit
(`cayley_maps_resolvent`).

## Main results

* `resolvent_at_neg_i_eq_cfc` : `(A + iI)⁻¹ = cfc (fun w => (1 - w) / (2 * I)) (cayleyTransform ..)`
* `cayley_maps_resolvent` : for `z.im ≠ 0`, `cayleyTransform .. - w • 1` is a unit, where
  `w = (z - i) * (z + i)⁻¹`.
-/

open Complex
open Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Cayley

/-- The resolvent `(A + iI)⁻¹` of `A` is the continuous functional calculus of the Cayley
transform `U` evaluated at `w ↦ (1 - w) / (2i)`; equivalently `(2 * I)⁻¹ • (1 - U)`. -/
lemma resolvent_at_neg_i_eq_cfc
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) :
    resolventAtNegI hsym hplus
      = cfc (fun w : ℂ => (1 - w) / (2 * I)) (cayleyTransform hsym hplus) := by
  -- normality puts `cfc` in business; `2i` is a unit
  have hn : IsStarNormal (cayleyTransform hsym hplus) :=
    cayleyTransform_isStarNormal hsym hplus hminus
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  -- the transform, with the ring unit `1` in place of `id`
  have hcay : cayleyTransform hsym hplus
      = (1 : H →L[ℂ] H) - (2 * I) • resolventAtNegI hsym hplus := rfl
  -- `cfc` of the affine pullback, by the algebra-hom laws
  have key : cfc (fun w : ℂ => (1 - w) / (2 * I)) (cayleyTransform hsym hplus)
      = (2 * I)⁻¹ • ((1 : H →L[ℂ] H) - cayleyTransform hsym hplus) := by
    have hfun : (fun w : ℂ => (1 - w) / (2 * I)) = fun w : ℂ => (2 * I)⁻¹ * (1 - w) := by
      funext w; rw [div_eq_inv_mul]
    have hinner : cfc (fun w : ℂ => (1 : ℂ) - w) (cayleyTransform hsym hplus)
        = (1 : H →L[ℂ] H) - cayleyTransform hsym hplus := by
      rw [cfc_sub (fun _ : ℂ => (1 : ℂ)) (fun w : ℂ => w) (cayleyTransform hsym hplus),
          cfc_const (1 : ℂ) (cayleyTransform hsym hplus),
          cfc_id' (R := ℂ) (a := cayleyTransform hsym hplus),
          map_one]
    rw [hfun, cfc_const_mul (2 * I)⁻¹ (fun w : ℂ => 1 - w) (cayleyTransform hsym hplus), hinner]
  -- assemble: both sides are `(2i)⁻¹ • (1 - U)`
  rw [key, hcay, sub_sub_cancel, smul_smul, inv_mul_cancel₀ h2I, one_smul]

/-- The Cayley transform sends non-real points to the resolvent set:
for `Im z ≠ 0` the Möbius image `w = (z-i)/(z+i)` lies off the unit circle, so `U - w` is a unit. -/
theorem cayley_maps_resolvent [Nontrivial H]
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) :
    let w := (z - I) * (z + I)⁻¹
    IsUnit (cayleyTransform hsym hplus - w • ContinuousLinearMap.id ℂ H) := by
  intro w
  -- (1) `w` is off the unit circle, because `Im z ≠ 0`.
  have hw_norm_ne_one : ‖w‖ ≠ 1 := by
    simp only [w, norm_mul, norm_inv]
    intro h_eq
    have h_ne : ‖z + I‖ ≠ 0 := fun h0 => by
      rw [h0, inv_zero, mul_zero] at h_eq; exact zero_ne_one h_eq
    have h_abs_eq : ‖z - I‖ = ‖z + I‖ := by
      field_simp [h_ne] at h_eq; linarith [h_eq]
    have hz0 : z.im = 0 := by
      have h1 : ‖z - I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
        rw [Complex.sq_norm]; simp [Complex.normSq, Complex.I_re, Complex.I_im]; ring
      have h2 : ‖z + I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
        rw [Complex.sq_norm]; simp [Complex.normSq, Complex.I_re, Complex.I_im]; ring
      have h3 : ‖z - I‖ ^ 2 = ‖z + I‖ ^ 2 := by rw [h_abs_eq]
      rw [h1, h2] at h3; nlinarith
    exact hz hz0
  -- (2) `U` is unitary, so its spectrum lies on the circle; `w ∉ σ(U)`.
  have hU := cayleyTransform_unitary hsym hplus hminus
  set U := cayleyTransform hsym hplus with _hU_def
  have hUUadj : ∀ ψ, U (U.adjoint ψ) = ψ := fun ψ => by
    simpa using congrFun (congrArg DFunLike.coe hU.2) ψ
  rcases lt_or_gt_of_ne hw_norm_ne_one with hw_lt | hw_gt
  · -- ‖w‖ < 1 : factor `U - w = U (1 - w U⋆)`.
    have h_adj_norm : ‖w • U.adjoint‖ < 1 := by
      calc ‖w • U.adjoint‖ ≤ ‖w‖ * ‖U.adjoint‖ :=
            ContinuousLinearMap.opNorm_smul_le w U.adjoint
        _ = ‖w‖ * 1 := by
            congr 1
            simp only [LinearIsometryEquiv.norm_map]
            exact cayleyTransform_norm_one hsym hplus
        _ = ‖w‖ := mul_one _
        _ < 1 := hw_lt
    have h_inv : IsUnit (ContinuousLinearMap.id ℂ H - w • U.adjoint) :=
      Resolvent.isUnit_one_sub _ h_adj_norm
    have h_factor : U - w • ContinuousLinearMap.id ℂ H =
        U.comp (ContinuousLinearMap.id ℂ H - w • U.adjoint) := by
      ext ψ
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
                 ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
                 map_sub, map_smul, hUUadj]
    rw [h_factor]
    exact (cayleyTransform_isUnit hsym hplus hminus).mul h_inv
  · -- ‖w‖ > 1 : factor `U - w = (-w)(1 - w⁻¹ U)`.
    have hw_ne : w ≠ 0 := fun h => by rw [h, norm_zero] at hw_gt; linarith
    have h_inv_norm : ‖w⁻¹ • U‖ < 1 := by
      calc ‖w⁻¹ • U‖ ≤ ‖w⁻¹‖ * ‖U‖ := ContinuousLinearMap.opNorm_smul_le w⁻¹ U
        _ = ‖w‖⁻¹ * 1 := by rw [norm_inv, cayleyTransform_norm_one hsym hplus]
        _ = ‖w‖⁻¹ := mul_one _
        _ < 1 := inv_lt_one_of_one_lt₀ hw_gt
    have h_inv : IsUnit (ContinuousLinearMap.id ℂ H - w⁻¹ • U) :=
      Resolvent.isUnit_one_sub _ h_inv_norm
    have h_factor : U - w • ContinuousLinearMap.id ℂ H =
        (-w • ContinuousLinearMap.id ℂ H) * (ContinuousLinearMap.id ℂ H - w⁻¹ • U) := by
      ext ψ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
                 ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hw_ne]
      module
    rw [h_factor]
    refine IsUnit.mul ?_ h_inv
    exact ⟨⟨-w • ContinuousLinearMap.id ℂ H, (-w)⁻¹ • ContinuousLinearMap.id ℂ H,
        by ext ψ
           simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply, smul_smul,
             mul_inv_cancel₀ (neg_ne_zero.mpr hw_ne), one_smul],
        by ext ψ
           simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply, smul_smul,
             inv_mul_cancel₀ (neg_ne_zero.mpr hw_ne), one_smul]⟩, rfl⟩

end Spectra.Cayley

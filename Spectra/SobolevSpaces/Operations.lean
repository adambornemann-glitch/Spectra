/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
File: Spectra/SoboleveSpaces/Operations.lean
-/
import Spectra.SobolevSpaces.DuBoisReymond
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory
open scoped ContDiff

namespace Spectra.Sobolev

/-- The zero function has weak derivative zero. -/
lemma hasWeakDerivative_zero (i : Fin 3) :
    HasWeakDerivative (0 : L2_R3) i 0 := by
  intro φ hφ hsupp
  have hae := Lp.coeFn_zero ℂ 2 (volume : Measure R3)
  have lhs : ∫ x, ((0 : L2_R3) : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 :=
    integral_eq_zero_of_ae (hae.mono fun x hx => by
      simp only [ZeroMemClass.coe_zero, Pi.zero_apply, mul_eq_zero]
      exact mul_eq_mul_left_iff.mp (congrArg (HMul.hMul ((fderiv ℝ φ x)
        (EuclideanSpace.single i 1))) hx))
  have rhs : ∫ x, ((0 : L2_R3) : R3 → ℂ) x * φ x = 0 :=
    integral_eq_zero_of_ae (hae.mono fun x hx => by
      simp only [ZeroMemClass.coe_zero, Pi.zero_apply, mul_eq_zero]
      exact mul_eq_mul_left_iff.mp (congrArg (HMul.hMul (φ x)) hx))
  rw [lhs, rhs, neg_zero]

/-- Weak derivative is linear in f. -/
lemma hasWeakDerivative_add
    (f₁ f₂ : L2_R3) (i : Fin 3) (g₁ g₂ : L2_R3)
    (h₁ : HasWeakDerivative f₁ i g₁) (h₂ : HasWeakDerivative f₂ i g₂) :
    HasWeakDerivative (f₁ + f₂) i (g₁ + g₂) := by
  intro φ hφ hsupp
  have e₁ := h₁ φ hφ hsupp
  have e₂ := h₂ φ hφ hsupp
  have hψ_L2 := memLp_partialDeriv φ i hφ hsupp
  have hφ_L2 := memLp_of_smooth_compactSupport φ hφ hsupp
  have hint_l1 : Integrable (fun x => (f₁ : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) volume :=
    (Lp.memLp f₁).integrable_mul hψ_L2
  have hint_l2 : Integrable (fun x => (f₂ : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) volume :=
    (Lp.memLp f₂).integrable_mul hψ_L2
  have hint_r1 : Integrable (fun x => (g₁ : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp g₁).integrable_mul hφ_L2
  have hint_r2 : Integrable (fun x => (g₂ : R3 → ℂ) x * φ x) volume :=
    (Lp.memLp g₂).integrable_mul hφ_L2
  -- Rewrite LHS pointwise via ae
  have lhs : ∫ x, ((f₁ + f₂ : L2_R3) : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1) =
    (∫ x, (f₁ : R3 → ℂ) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) +
    (∫ x, (f₂ : R3 → ℂ) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    rw [integral_congr_ae ((Lp.coeFn_add f₁ f₂).mono fun x hx => by
      simp only [Pi.add_apply] at hx; rw [hx, add_mul])]
    exact integral_add hint_l1 hint_l2
  have rhs : ∫ x, ((g₁ + g₂ : L2_R3) : R3 → ℂ) x * φ x =
    (∫ x, (g₁ : R3 → ℂ) x * φ x) + (∫ x, (g₂ : R3 → ℂ) x * φ x) := by
    rw [integral_congr_ae ((Lp.coeFn_add g₁ g₂).mono fun x hx => by
      simp only [Pi.add_apply] at hx; rw [hx, add_mul])]
    exact integral_add hint_r1 hint_r2
  rw [lhs, rhs, neg_add]
  exact congr_arg₂ (· + ·) e₁ e₂


/-- Weak derivative commutes with scalar multiplication. -/
lemma hasWeakDerivative_smul
    (c : ℂ) (f : L2_R3) (i : Fin 3) (g : L2_R3)
    (h : HasWeakDerivative f i g) :
    HasWeakDerivative (c • f) i (c • g) := by
  intro φ hφ hsupp
  have e := h φ hφ hsupp
  -- LHS: ∫ (c • f) · ∂ᵢφ = c * ∫ f · ∂ᵢφ
  have lhs : ∫ x, ((c • f : L2_R3) : R3 → ℂ) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1) =
    c * ∫ x, (f : R3 → ℂ) x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    rw [integral_congr_ae ((Lp.coeFn_smul c f).mono fun x hx => by
      simp only [Pi.smul_apply, smul_eq_mul] at hx; rw [hx, mul_assoc])]
    exact integral_const_mul c _
  -- RHS: ∫ (c • g) · φ = c * ∫ g · φ
  have rhs : ∫ x, ((c • g : L2_R3) : R3 → ℂ) x * φ x =
    c * ∫ x, (g : R3 → ℂ) x * φ x := by
    rw [integral_congr_ae ((Lp.coeFn_smul c g).mono fun x hx => by
      simp only [Pi.smul_apply, smul_eq_mul] at hx; rw [hx, mul_assoc])]
    exact integral_const_mul c _
  rw [lhs, rhs, e, mul_neg]


/-- Second-order weak partial derivative. -/
def HasWeakSecondDerivative
    (f : L2_R3) (i j : Fin 3) (g : L2_R3) : Prop :=
  ∃ (h : L2_R3), HasWeakDerivative f i h ∧ HasWeakDerivative h j g


/-- Classical Schwarz: mixed partials of smooth functions commute. -/
private lemma schwarz_partials (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (i j : Fin 3) (x : R3) :
    fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single j 1) =
    fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1) := by
  set eᵢ := EuclideanSpace.single i (1 : ℝ)
  set eⱼ := EuclideanSpace.single j (1 : ℝ)
  have hφ' : ContDiff ℝ ∞ (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.mp hφ).2
  have hφ'_da : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ'.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt
  -- Reduce: fderiv (fun y => F'(y) v) x w = (fderiv F' x w) v
  have reduce : ∀ v, fderiv ℝ (fun y => fderiv ℝ φ y v) x =
      (fderiv ℝ (fderiv ℝ φ) x).flip v := by
    intro v
    have h := hφ'_da.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    simp only [ContinuousLinearMap.comp_zero] at h
    simp only [zero_add] at h
    exact h.fderiv
  rw [reduce eᵢ, reduce eⱼ]
  simp only [ContinuousLinearMap.flip_apply]
  have hφx : ContDiffAt ℝ ∞ φ x := hφ.contDiffAt
  have hsymm := hφx.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact right_eq_inf.mp rfl)
  exact hsymm eⱼ eᵢ

/-- Symmetry of second weak derivatives (Schwarz's theorem, L² version).
    Requires that `∂ⱼf` exists (automatic for H² functions). -/
lemma hasWeakSecondDerivative_comm
    (f : L2_R3) (i j : Fin 3) (g : L2_R3)
    (h : HasWeakSecondDerivative f i j g)
    (hfj : ∃ mid', HasWeakDerivative f j mid') :
    HasWeakSecondDerivative f j i g := by
  obtain ⟨mid, hmid_i, hg_j⟩ := h
  obtain ⟨mid', hmid'_j⟩ := hfj
  refine ⟨mid', hmid'_j, fun φ hφ hsupp => ?_⟩
  -- Test functions: ∂ᵢφ and ∂ⱼφ are smooth with compact support
  have hdiφ_s := contDiff_partialDeriv φ i hφ
  have hdiφ_c := hasCompactSupport_partialDeriv φ i hsupp
  have hdjφ_s := contDiff_partialDeriv φ j hφ
  have hdjφ_c := hasCompactSupport_partialDeriv φ j hsupp
  -- (A) test ∂ⱼf = mid' against ∂ᵢφ:
  --     ∫ f·∂ⱼ(∂ᵢφ) = −∫ mid'·∂ᵢφ
  have eA := hmid'_j _ hdiφ_s hdiφ_c
  -- (B) test ∂ᵢf = mid against ∂ⱼφ:
  --     ∫ f·∂ᵢ(∂ⱼφ) = −∫ mid·∂ⱼφ
  have eB := hmid_i _ hdjφ_s hdjφ_c
  -- (C) test ∂ⱼmid = g against φ:
  --     ∫ mid·∂ⱼφ = −∫ g·φ
  have eC := hg_j φ hφ hsupp
  -- (D) Schwarz: ∂ⱼ(∂ᵢφ) = ∂ᵢ(∂ⱼφ) pointwise, hence under ∫ f·(−)
  have eD : ∫ x, (f : R3 → ℂ) x *
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
    ∫ x, (f : R3 → ℂ) x *
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) :=
    integral_congr_ae (ae_of_all _ fun x => by
      dsimp only
      rw [schwarz_partials φ hφ i j x])
  -- Chain: ∫ mid'·∂ᵢφ = −∫ f·∂ⱼ(∂ᵢφ) = −∫ f·∂ᵢ(∂ⱼφ) = ∫ mid·∂ⱼφ = −∫ g·φ
  linear_combination eA - eD - eB + eC

/-- Second weak derivative is unique. -/
lemma hasWeakSecondDerivative_unique
    (f : L2_R3) (i j : Fin 3) (g₁ g₂ : L2_R3)
    (h₁ : HasWeakSecondDerivative f i j g₁)
    (h₂ : HasWeakSecondDerivative f i j g₂) :
    g₁ = g₂ := by
  obtain ⟨mid₁, hd₁, hd₁'⟩ := h₁
  obtain ⟨mid₂, hd₂, hd₂'⟩ := h₂
  have : mid₁ = mid₂ := hasWeakDerivative_unique f i mid₁ mid₂ hd₁ hd₂
  subst this
  exact hasWeakDerivative_unique mid₁ j g₁ g₂ hd₁' hd₂'

end Spectra.Sobolev

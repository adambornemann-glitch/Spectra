/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.CayleyTransform.Defs
import Spectra.CayleyTransform.Mobius
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
open Complex
open Spectra.Resolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
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
  set w := (↑μ - I) * (↑μ + I)⁻¹ with _hw
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

/-- For symmetric operators, `‖Aψ + iψ‖² = ‖Aψ‖² + ‖ψ‖²`. -/
lemma self_adjoint_norm_sq_add
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (ψ : A.domain) :
    ‖A ψ + I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 :=
  norm_sq_add_I_smul hsym ψ

/-- Pure real-arithmetic core of the δ-independent norm floor used in
`cayley_approx_eigenvalue_backward`: given the norm identity `‖Aψ‖² + ‖ψ‖² = 1`, the upper bound
`‖Aψ‖ ≤ |μ|·‖ψ‖ + δ`, and `δ` small relative to `denom`, conclude `1/(2·denom) ≤ ‖ψ‖`. Extracted as
a standalone real-number lemma (no Hilbert-space dependency) — run in place inside the accumulated
proof context of `cayley_approx_eigenvalue_backward`, the same `nlinarith` calls cost ~10× more
(context-size cost, not a repeated-coercion bug; see the compile-time case study). -/
lemma cayley_norm_lower_bound {μ nψ nAψ δ denom : ℝ}
    (hnψ_nonneg : 0 ≤ nψ) (hnAψ_nonneg : 0 ≤ nAψ) (hδ_nonneg : 0 ≤ δ)
    (hdenom_pos : denom > 0) (hdenom_ge_one : denom ≥ 1)
    (h_denom_sq : denom ^ 2 = 1 + μ ^ 2)
    (hδ_small : δ < 1 / (4 * denom))
    (h_norm_identity : nAψ ^ 2 + nψ ^ 2 = 1)
    (h_Aψ_upper : nAψ ≤ |μ| * nψ + δ) :
    1 / (2 * denom) ≤ nψ := by
  have hδ_half : δ ≤ 1 / 2 := by
    have hle : (1 : ℝ) / (4 * denom) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hdenom_ge_one]
    linarith [hδ_small, hle]
  have h_crude : (1 : ℝ) ≤ (1 + 2 * μ ^ 2) * nψ ^ 2 + 2 * δ ^ 2 := by
    have hsq : nAψ ^ 2 ≤ (|μ| * nψ + δ) ^ 2 :=
      sq_le_sq'
        (by nlinarith [hnAψ_nonneg, mul_nonneg (abs_nonneg μ) hnψ_nonneg, hδ_nonneg])
        h_Aψ_upper
    rw [← sq_abs μ]
    nlinarith [h_norm_identity, hsq, sq_nonneg (|μ| * nψ - δ)]
  have hsq_lower : 1 / (4 * denom ^ 2) ≤ nψ ^ 2 := by
    have hge : (1 : ℝ) / 2 ≤ (1 + 2 * μ ^ 2) * nψ ^ 2 := by
      nlinarith [h_crude, hδ_half, hδ_nonneg]
    have hsq1 : 1 / (2 * (1 + 2 * μ ^ 2)) ≤ nψ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hge]
    have hcmp : 1 / (4 * denom ^ 2) ≤ 1 / (2 * (1 + 2 * μ ^ 2)) := by
      rw [h_denom_sq, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg μ]
    linarith [hsq1, hcmp]
  have h := Real.sqrt_le_sqrt hsq_lower
  rwa [Real.sqrt_sq hnψ_nonneg,
       show Real.sqrt (1 / (4 * denom ^ 2)) = 1 / (2 * denom) by
         rw [show (1 : ℝ) / (4 * denom ^ 2) = (1 / (2 * denom)) ^ 2 by ring,
             Real.sqrt_sq (by positivity)]] at h

/-- Approximate eigenvalues of `U` give approximate eigenvalues of `A`. -/
lemma cayley_approx_eigenvalue_backward
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧
      ‖(cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) • ContinuousLinearMap.id ℂ H) φ‖ < ε) →
    (∀ C > 0, ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ < C * ‖(ψ : H)‖) := by
  intro h_approx C hC
  set U := cayleyTransform hsym hplus with _hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with _hw_def
  have h_one_sub_w_ne : (1 : ℂ) - w ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := norm_pos_iff.mpr h_one_sub_w_ne
  set denom := Real.sqrt (1 + μ ^ 2) with hdenom
  have hdenom_pos : denom > 0 := Real.sqrt_pos.mpr (by linarith [sq_nonneg μ])
  have hdenom_ge_one : denom ≥ 1 := by
    rw [hdenom]
    calc Real.sqrt (1 + μ ^ 2) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [sq_nonneg μ])
      _ = 1 := Real.sqrt_one
  have h_denom_sq : denom ^ 2 = 1 + μ ^ 2 := by
    rw [hdenom]; exact Real.sq_sqrt (by linarith [sq_nonneg μ])
  set C' := min C (1 / 2) with _hC'_def
  have hC'_pos : C' > 0 := lt_min hC (by norm_num)
  have hC'_le_half : C' ≤ 1 / 2 := min_le_right C (1 / 2)
  have hC'_le_C : C' ≤ C := min_le_left C (1 / 2)
  obtain ⟨φ, hφ_norm, hφ_bound⟩ := h_approx (C' * ‖(1 : ℂ) - w‖ / (2 * denom)) (by positivity)
  obtain ⟨ψ, hφ_eq⟩ := hplus φ
  have hφ_ne : φ ≠ 0 := by
    intro h; rw [h, norm_zero] at hφ_norm; exact one_ne_zero hφ_norm.symm
  have hψ_ne : (ψ : H) ≠ 0 := by
    intro h
    have hψ0 : ψ = 0 := Subtype.ext h
    apply hφ_ne; rw [← hφ_eq, hψ0]; simp
  refine ⟨ψ, hψ_ne, ?_⟩
  -- Cayley shift identity, transported through `φ = (A + iI)ψ`.
  have h_key : (U - w • ContinuousLinearMap.id ℂ H) φ
      = ((1 : ℂ) - w) • (A ψ - (↑μ : ℂ) • (ψ : H)) := by
    have h := cayley_shift_identity hsym hplus μ hμ_ne ψ
    rw [hφ_eq] at h; exact h
  have h_norm_eq : ‖A ψ - (↑μ : ℂ) • (ψ : H)‖
      = ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ / ‖(1 : ℂ) - w‖ := by
    rw [h_key, norm_smul]; field_simp [ne_of_gt h_one_sub_w_norm_pos]
  set δ := ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ with hδ_def
  have hδ_nonneg : 0 ≤ δ := norm_nonneg _
  have hδ_bound : δ < C' / (2 * denom) := by
    calc δ = ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖ / ‖(1 : ℂ) - w‖ := h_norm_eq
      _ < (C' * ‖(1 : ℂ) - w‖ / (2 * denom)) / ‖(1 : ℂ) - w‖ :=
          div_lt_div_of_pos_right hφ_bound h_one_sub_w_norm_pos
      _ = C' / (2 * denom) := by field_simp
  have hδ_small : δ < 1 / (4 * denom) := by
    calc δ < C' / (2 * denom) := hδ_bound
      _ ≤ (1 / 2) / (2 * denom) := div_le_div_of_nonneg_right hC'_le_half (by positivity)
      _ = 1 / (4 * denom) := by ring
  have h_norm_identity : ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 = 1 := by
    have h := self_adjoint_norm_sq_add hsym ψ
    rw [hφ_eq, hφ_norm, one_pow] at h; linarith
  -- The δ-independent floor, by the crude `(a+b)² ≤ 2a²+2b²` estimate.
  have hψ_norm_lower : 1 / (2 * denom) ≤ ‖(ψ : H)‖ := by
    have h_Aψ_upper : ‖A ψ‖ ≤ |μ| * ‖(ψ : H)‖ + δ := by
      have h1 : ‖(↑μ : ℂ) • (ψ : H)‖ = |μ| * ‖(ψ : H)‖ := by
        rw [norm_smul]; simp [Complex.norm_real, Real.norm_eq_abs]
      calc ‖A ψ‖
          = ‖(A ψ - (↑μ : ℂ) • (ψ : H)) + (↑μ : ℂ) • (ψ : H)‖ := by rw [sub_add_cancel]
        _ ≤ ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ + ‖(↑μ : ℂ) • (ψ : H)‖ := norm_add_le _ _
        _ = δ + |μ| * ‖(ψ : H)‖ := by rw [← hδ_def, h1]
        _ = |μ| * ‖(ψ : H)‖ + δ := by ring
    exact cayley_norm_lower_bound (norm_nonneg (ψ : H)) (norm_nonneg (A ψ)) hδ_nonneg
      hdenom_pos hdenom_ge_one h_denom_sq hδ_small h_norm_identity h_Aψ_upper
  calc δ < C' / (2 * denom) := hδ_bound
    _ ≤ C / (2 * denom) := div_le_div_of_nonneg_right hC'_le_C (by positivity)
    _ ≤ C * ‖(ψ : H)‖ := by
        calc C / (2 * denom) = C * (1 / (2 * denom)) := by ring
          _ ≤ C * ‖(ψ : H)‖ := mul_le_mul_of_nonneg_left hψ_norm_lower (le_of_lt hC)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [IsScalarTower ℝ ℂ H]

/-- Approximate eigenvalues of `A` give approximate eigenvalues of `U`. -/
lemma cayley_approx_eigenvalue_forward
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ) (μ : ℝ)
    (hμ_ne : (↑μ : ℂ) + I ≠ 0) :
    (∀ C > 0, ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧ ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ < C * ‖(ψ : H)‖) →
    (∀ ε > 0, ∃ φ, ‖φ‖ = 1 ∧
      ‖(cayleyTransform hsym hplus - ((↑μ - I) * (↑μ + I)⁻¹) •
          ContinuousLinearMap.id ℂ H) φ‖ < ε) := by
  intro h_approx ε hε
  set U := cayleyTransform hsym hplus with _hU_def
  set w := (↑μ - I) * (↑μ + I)⁻¹ with _hw_def
  have h_one_sub_w_ne : (1 : ℂ) - w ≠ 0 := one_sub_mobius_ne_zero μ hμ_ne
  have h_one_sub_w_norm_pos : ‖(1 : ℂ) - w‖ > 0 := norm_pos_iff.mpr h_one_sub_w_ne
  obtain ⟨ψ, hψ_ne, h_Aμψ_bound⟩ := h_approx (ε / ‖(1 : ℂ) - w‖) (by positivity)
  have hψ_norm_pos : ‖(ψ : H)‖ > 0 := norm_pos_iff.mpr hψ_ne
  set φ' := A ψ + I • (ψ : H) with _hφ'_def
  have hφ'_norm_pos : ‖φ'‖ > 0 := by
    have h_sq := self_adjoint_norm_sq_add hsym ψ
    have _h_ge : ‖φ'‖ ^ 2 ≥ ‖(ψ : H)‖ ^ 2 := by
      calc ‖φ'‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := h_sq
        _ ≥ 0 + ‖(ψ : H)‖ ^ 2 := by linarith [sq_nonneg ‖A ψ‖]
        _ = ‖(ψ : H)‖ ^ 2 := by ring
    nlinarith [norm_nonneg φ', sq_nonneg ‖φ'‖, sq_nonneg ‖(ψ : H)‖]
  have hφ'_ne : φ' ≠ 0 := norm_pos_iff.mp hφ'_norm_pos
  have hφ'_norm_ge_ψ : ‖φ'‖ ≥ ‖(ψ : H)‖ := by
    have h_sq := self_adjoint_norm_sq_add hsym ψ
    have _h_ge : ‖φ'‖ ^ 2 ≥ ‖(ψ : H)‖ ^ 2 := by
      calc ‖φ'‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := h_sq
        _ ≥ ‖(ψ : H)‖ ^ 2 := by linarith [sq_nonneg ‖A ψ‖]
    nlinarith [norm_nonneg φ', norm_nonneg (ψ : H), sq_nonneg (‖φ'‖ - ‖(ψ : H)‖)]
  set φ := ‖φ'‖⁻¹ • φ' with hφ_def
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ_def, norm_smul, norm_inv, norm_norm]
    field_simp [ne_of_gt hφ'_norm_pos]
  have h_Uwφ' : (U - w • ContinuousLinearMap.id ℂ H) φ' =
      ((1 : ℂ) - w) • (A ψ - (↑μ : ℂ) • (ψ : H)) :=
    cayley_shift_identity hsym hplus μ hμ_ne ψ
  have h_norm_Uwφ' : ‖(U - w • ContinuousLinearMap.id ℂ H) φ'‖ =
      ‖(1 : ℂ) - w‖ * ‖A ψ - (↑μ : ℂ) • (ψ : H)‖ := by
    rw [h_Uwφ', norm_smul]
  calc ‖(U - w • ContinuousLinearMap.id ℂ H) φ‖
      = ‖(U - w • ContinuousLinearMap.id ℂ H) (‖φ'‖⁻¹ • φ')‖ := by rw [hφ_def]
    _ = ‖‖φ'‖⁻¹ • (U - w • ContinuousLinearMap.id ℂ H) φ'‖ := by
        simp only [ContinuousLinearMap.map_smul_of_tower,
          ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul',
          ContinuousLinearMap.coe_id', Pi.sub_apply, Pi.smul_apply, id_eq]
    _ = ‖φ'‖⁻¹ * ‖(U - w • ContinuousLinearMap.id ℂ H) φ'‖ := by
        rw [norm_smul, norm_inv, norm_norm]
    _ = ‖φ'‖⁻¹ * (‖(1 : ℂ) - w‖ * ‖A ψ - (↑μ : ℂ) • (ψ : H)‖) := by rw [h_norm_Uwφ']
    _ < ‖φ'‖⁻¹ * (‖(1 : ℂ) - w‖ * (ε / ‖(1 : ℂ) - w‖ * ‖(ψ : H)‖)) := by
        apply mul_lt_mul_of_pos_left _ (inv_pos.mpr hφ'_norm_pos)
        exact mul_lt_mul_of_pos_left h_Aμψ_bound h_one_sub_w_norm_pos
    _ = ‖φ'‖⁻¹ * (ε * ‖(ψ : H)‖) := by field_simp
    _ ≤ ‖φ'‖⁻¹ * (ε * ‖φ'‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
        exact mul_le_mul_of_nonneg_left hφ'_norm_ge_ψ (le_of_lt hε)
    _ = ε := by field_simp [ne_of_gt hφ'_norm_pos]

end Spectra.Cayley

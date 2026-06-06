/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla
Ported by: Adam Bornemann
-/
import Spectra.BellsTheorem.CHSH_bounds.CHSH_Basic

open MeasureTheory ProbabilityTheory Matrix Complex

/-! ## Quantum State Foundations -/

namespace QuantumInfo

/-! ## Main lemma: Separable States Cannot Violate CHSH -/

/-- Separable states cannot violate the CHSH inequality.

The proof proceeds by:
1. Expanding CHSH_expect for product state ρ_A ⊗ ρ_B
2. Using trace factorization: Tr((A⊗I)(I⊗B)(ρ_A⊗ρ_B)) = Tr(Aρ_A)·Tr(Bρ_B)
3. Applying dichotomic expectation bounds: |Tr(Aᵢρ_A)|, |Tr(Bⱼρ_B)| ≤ 1
4. Using algebraic bound for CHSH expression with bounded expectations
-/
lemma CHSH_separable_bound {m n : ℕ} [NeZero m] [NeZero n]
    (A₀ A₁ : Matrix (Fin m) (Fin m) ℂ)
    (B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀ : A₀.IsHermitian) (hA₁ : A₁.IsHermitian)
    (hB₀ : B₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1)
    (hB₀_sq : B₀ * B₀ = 1) (hB₁_sq : B₁ * B₁ = 1)
    (ρ_A : DensityMatrix m) (ρ_B : DensityMatrix n) :
    let ρ := kroneckerMap (· * ·) ρ_A.toMatrix ρ_B.toMatrix
    ‖(CHSH_expect
      (kroneckerMap (· * ·) A₀ 1)
      (kroneckerMap (· * ·) A₁ 1)
      (kroneckerMap (· * ·) 1 B₀)
      (kroneckerMap (· * ·) 1 B₁) ρ)‖ ≤ 2 := by
  intro ρ

  -- Step 1: Expand CHSH_expect
  simp only [CHSH_expect, CHSH_op]

  -- Define local expectation values
  let a₀ : ℂ := (A₀ * ρ_A.toMatrix).trace
  let a₁ : ℂ := (A₁ * ρ_A.toMatrix).trace
  let b₀ : ℂ := (B₀ * ρ_B.toMatrix).trace
  let b₁ : ℂ := (B₁ * ρ_B.toMatrix).trace

  -- Step 2: Show CHSH value factors as product of local expectations
  -- Each term like Tr((A₀⊗I)(I⊗B₁)(ρ_A⊗ρ_B)) = Tr(A₀ρ_A) · Tr(B₁ρ_B)

  have factor_01 : ((kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₁) * ρ).trace = a₀ * b₁ := by
    -- (A₀⊗I)(I⊗B₁) = A₀⊗B₁
    have h1 : kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₁ =
              kroneckerMap (· * ·) A₀ B₁ := by
      rw [kronecker_mul_mul]
      simp only [Matrix.mul_one, Matrix.one_mul]
    rw [h1]
    -- Tr((A₀⊗B₁)(ρ_A⊗ρ_B)) = Tr((A₀ρ_A)⊗(B₁ρ_B)) = Tr(A₀ρ_A)·Tr(B₁ρ_B)
    have h2 : kroneckerMap (· * ·) A₀ B₁ * ρ =
              kroneckerMap (· * ·) (A₀ * ρ_A.toMatrix) (B₁ * ρ_B.toMatrix) := by
      rw [kronecker_mul_mul]
    rw [h2, trace_kronecker_mul]

  have factor_00 : ((kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₀) * ρ).trace = a₀ * b₀ := by
    have h1 : kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₀ =
              kroneckerMap (· * ·) A₀ B₀ := by
      rw [kronecker_mul_mul]
      simp only [Matrix.mul_one, Matrix.one_mul]
    rw [h1]
    have h2 : kroneckerMap (· * ·) A₀ B₀ * ρ =
              kroneckerMap (· * ·) (A₀ * ρ_A.toMatrix) (B₀ * ρ_B.toMatrix) := by
      rw [kronecker_mul_mul]
    rw [h2, trace_kronecker_mul]

  have factor_10 : ((kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₀) * ρ).trace = a₁ * b₀ := by
    have h1 : kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₀ =
              kroneckerMap (· * ·) A₁ B₀ := by
      rw [kronecker_mul_mul]
      simp only [Matrix.mul_one, Matrix.one_mul]
    rw [h1]
    have h2 : kroneckerMap (· * ·) A₁ B₀ * ρ =
              kroneckerMap (· * ·) (A₁ * ρ_A.toMatrix) (B₀ * ρ_B.toMatrix) := by
      rw [kronecker_mul_mul]
    rw [h2, trace_kronecker_mul]

  have factor_11 : ((kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₁) * ρ).trace = a₁ * b₁ := by
    have h1 : kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₁ =
              kroneckerMap (· * ·) A₁ B₁ := by
      rw [kronecker_mul_mul]
      simp only [Matrix.mul_one, Matrix.one_mul]
    rw [h1]
    have h2 : kroneckerMap (· * ·) A₁ B₁ * ρ =
              kroneckerMap (· * ·) (A₁ * ρ_A.toMatrix) (B₁ * ρ_B.toMatrix) := by
      rw [kronecker_mul_mul]
    rw [h2, trace_kronecker_mul]

  -- Step 3: Rewrite CHSH in terms of local expectations
  -- Need to handle the matrix algebra: (A-B+C+D)*ρ etc.
  have chsh_factors : ((kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₁ -
                        kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₀ +
                        kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₀ +
                        kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₁) * ρ).trace =
                       a₀ * b₁ - a₀ * b₀ + a₁ * b₀ + a₁ * b₁ := by
    rw [add_mul, add_mul, sub_mul]
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_sub]
    rw [factor_01, factor_00, factor_10, factor_11]

  rw [chsh_factors]

  -- Step 4: Apply expectation bounds
  -- For Hermitian A with A² = I and density matrix ρ, Tr(Aρ) is real and |Tr(Aρ)| ≤ 1

  have ha₀_bound : ‖a₀‖ ≤ 1 := dichotomic_expectation_bound A₀ hA₀ hA₀_sq ρ_A
  have ha₁_bound : ‖a₁‖ ≤ 1 := dichotomic_expectation_bound A₁ hA₁ hA₁_sq ρ_A
  have hb₀_bound : ‖b₀‖ ≤ 1 := dichotomic_expectation_bound B₀ hB₀ hB₀_sq ρ_B
  have hb₁_bound : ‖b₁‖ ≤ 1 := dichotomic_expectation_bound B₁ hB₁ hB₁_sq ρ_B

  -- The expectations are real (Hermitian observable, Hermitian state)
  -- So we can use the real algebraic bound

  -- For now, use a complex version of the algebraic bound
  -- |a₀*b₁ - a₀*b₀ + a₁*b₀ + a₁*b₁| ≤ 2 when |aᵢ|, |bⱼ| ≤ 1

  calc ‖a₀ * b₁ - a₀ * b₀ + a₁ * b₀ + a₁ * b₁‖
      = ‖a₀ * (b₁ - b₀) + a₁ * (b₀ + b₁)‖ := by ring_nf
    _ ≤ ‖a₀ * (b₁ - b₀)‖ + ‖a₁ * (b₀ + b₁)‖ := norm_add_le _ _
    _ = ‖a₀‖ * ‖b₁ - b₀‖ + ‖a₁‖ * ‖b₀ + b₁‖ := by rw [norm_mul, norm_mul]
    _ ≤ 1 * ‖b₁ - b₀‖ + 1 * ‖b₀ + b₁‖ := by
        apply add_le_add
        · exact mul_le_mul ha₀_bound (le_refl _) (norm_nonneg _) zero_le_one
        · exact mul_le_mul ha₁_bound (le_refl _) (norm_nonneg _) zero_le_one
    _ = ‖b₁ - b₀‖ + ‖b₀ + b₁‖ := by ring
    _ ≤ 2 := by
        -- The expectations are real (Hermitian observable + density matrix)
        have hb₀_real := hermitian_expectation_real B₀ hB₀ ρ_B.toMatrix ρ_B.hermitian
        have hb₁_real := hermitian_expectation_real B₁ hB₁ ρ_B.toMatrix ρ_B.hermitian

        -- For real complex numbers: z = z.re when z.im = 0
        have hb₀_eq : b₀ = (b₀.re : ℂ) := Complex.ext rfl hb₀_real
        have hb₁_eq : b₁ = (b₁.re : ℂ) := Complex.ext rfl hb₁_real

        -- Rewrite using real parts
        rw [hb₀_eq, hb₁_eq]
        simp only [← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.norm_real]

        -- Get real bounds from complex bounds
        have hb₀_re_bound : |b₀.re| ≤ 1 := by
          have h : ‖(b₀.re : ℂ)‖ ≤ 1 := hb₀_eq ▸ hb₀_bound
          simpa [Complex.norm_real] using h
        have hb₁_re_bound : |b₁.re| ≤ 1 := by
          have h : ‖(b₁.re : ℂ)‖ ≤ 1 := hb₁_eq ▸ hb₁_bound
          simpa [Complex.norm_real] using h

        -- Same case analysis as chsh_expectation_algebraic_bound
        by_cases h1 : 0 ≤ b₁.re - b₀.re <;> by_cases h2 : 0 ≤ b₀.re + b₁.re
        · -- h1: 0 ≤ b₁.re - b₀.re, h2: 0 ≤ b₀.re + b₁.re
          calc |b₁.re - b₀.re| + |b₀.re + b₁.re|
              = (b₁.re - b₀.re) + (b₀.re + b₁.re) := by
                  rw [abs_of_nonneg h1, abs_of_nonneg h2]
            _ = 2 * b₁.re := by ring
            _ ≤ 2 * 1 := by nlinarith [abs_le.mp hb₁_re_bound]
            _ = 2 := by ring
        · -- h1: 0 ≤ b₁.re - b₀.re, h2: ¬(0 ≤ b₀.re + b₁.re)
          calc |b₁.re - b₀.re| + |b₀.re + b₁.re|
              = (b₁.re - b₀.re) + -(b₀.re + b₁.re) := by
                  rw [abs_of_nonneg h1, abs_of_neg (not_le.mp h2)]
            _ = -2 * b₀.re := by ring
            _ ≤ 2 * 1 := by nlinarith [abs_le.mp hb₀_re_bound]
            _ = 2 := by ring
        · -- h1: ¬(0 ≤ b₁.re - b₀.re), h2: 0 ≤ b₀.re + b₁.re
          calc |b₁.re - b₀.re| + |b₀.re + b₁.re|
              = -(b₁.re - b₀.re) + (b₀.re + b₁.re) := by
                  rw [abs_of_neg (not_le.mp h1), abs_of_nonneg h2]
            _ = 2 * b₀.re := by ring
            _ ≤ 2 * 1 := by nlinarith [abs_le.mp hb₀_re_bound]
            _ = 2 := by ring
        · -- h1: ¬(0 ≤ b₁.re - b₀.re), h2: ¬(0 ≤ b₀.re + b₁.re)
          calc |b₁.re - b₀.re| + |b₀.re + b₁.re|
              = -(b₁.re - b₀.re) + -(b₀.re + b₁.re) := by
                  rw [abs_of_neg (not_le.mp h1), abs_of_neg (not_le.mp h2)]
            _ = -2 * b₁.re := by ring
            _ ≤ 2 * 1 := by nlinarith [abs_le.mp hb₁_re_bound]
            _ = 2 := by ring

end QuantumInfo

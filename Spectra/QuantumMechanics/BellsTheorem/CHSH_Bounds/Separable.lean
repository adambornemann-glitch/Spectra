/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Spectra.QuantumMechanics.BellsTheorem.CHSH_Bounds.CHSH_Basic
/-!
# Product States Cannot Violate CHSH

The CHSH bound for a pure product state `ρ_A ⊗ ρ_B`: expand the CHSH operator on the Kronecker
product, factor each cross term via `trace_kronecker_mul`, bound each local expectation by 1 via
`dichotomic_expectation_bound`, then close with the classical algebraic bound
(`chsh_expectation_algebraic_bound`, `CHSH_Bounds/CHSH_Basic.lean`).

## Main results

* `CHSH_productState_bound` : `‖chshExpect(A₀⊗I, A₁⊗I, I⊗B₀, I⊗B₁, ρ_A⊗ρ_B)‖ ≤ 2`

## Implementation notes

This covers the *product* state `ρ_A ⊗ ρ_B` only, not the full textbook notion of a *separable*
state (a convex mixture `∑ᵢ pᵢ ρ_A^i ⊗ ρ_B^i`). No `IsSeparable`/mixture predicate exists yet
anywhere in `BellsTheorem/`; extending this bound to genuine mixtures would follow by linearity of
the trace over the probability distribution `pᵢ`, but is a separate piece of work, not attempted
here.

## References

* [Echenim, Mhalla, *A formalization of the CHSH inequality and Tsirelson's
  upper-bound in Isabelle/HOL*][echenim2023]

## Tags

chsh, product state, separable state, quantum information
-/
open Matrix Complex

namespace Spectra.QuantumInfo

/-- `X ⊗ I` and `I ⊗ Y` acting on a product state `ρ_A ⊗ ρ_B` factor into a product of local
traces: `Tr((X⊗I)(I⊗Y)(ρ_A⊗ρ_B)) = Tr(Xρ_A) · Tr(Yρ_B)`. The shared step behind all four
cross-term factorizations in `CHSH_productState_bound`. -/
private lemma chsh_local_factor {m n : ℕ} [NeZero m] [NeZero n]
    (X : Matrix (Fin m) (Fin m) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (ρ_A : DensityMatrix m) (ρ_B : DensityMatrix n) :
    ((kroneckerMap (· * ·) X 1 * kroneckerMap (· * ·) 1 Y) *
      kroneckerMap (· * ·) ρ_A.toMatrix ρ_B.toMatrix).trace =
    (X * ρ_A.toMatrix).trace * (Y * ρ_B.toMatrix).trace := by
  have h1 : kroneckerMap (· * ·) X 1 * kroneckerMap (· * ·) 1 Y = kroneckerMap (· * ·) X Y := by
    rw [kronecker_mul_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  rw [h1]
  have h2 : kroneckerMap (· * ·) X Y * kroneckerMap (· * ·) ρ_A.toMatrix ρ_B.toMatrix =
            kroneckerMap (· * ·) (X * ρ_A.toMatrix) (Y * ρ_B.toMatrix) := by
    rw [kronecker_mul_mul]
  rw [h2, trace_kronecker_mul]

/-- The pure product state `ρ_A ⊗ ρ_B` cannot violate the CHSH inequality: `|S| ≤ 2`, the same
bound as the classical (LHV) case. See the module docstring for why this is the product-state
case, not the fully general separable (convex-mixture) one. -/
lemma CHSH_productState_bound {m n : ℕ} [NeZero m] [NeZero n]
    (A₀ A₁ : Matrix (Fin m) (Fin m) ℂ)
    (B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hA₀ : A₀.IsHermitian) (hA₁ : A₁.IsHermitian)
    (hB₀ : B₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (hA₀_sq : A₀ * A₀ = 1) (hA₁_sq : A₁ * A₁ = 1)
    (hB₀_sq : B₀ * B₀ = 1) (hB₁_sq : B₁ * B₁ = 1)
    (ρ_A : DensityMatrix m) (ρ_B : DensityMatrix n) :
    let ρ := kroneckerMap (· * ·) ρ_A.toMatrix ρ_B.toMatrix
    ‖(chshExpect
      (kroneckerMap (· * ·) A₀ 1)
      (kroneckerMap (· * ·) A₁ 1)
      (kroneckerMap (· * ·) 1 B₀)
      (kroneckerMap (· * ·) 1 B₁) ρ)‖ ≤ 2 := by
  intro ρ
  simp only [chshExpect, chshOp]
  -- Local expectation values
  let a₀ : ℂ := (A₀ * ρ_A.toMatrix).trace
  let a₁ : ℂ := (A₁ * ρ_A.toMatrix).trace
  let b₀ : ℂ := (B₀ * ρ_B.toMatrix).trace
  let b₁ : ℂ := (B₁ * ρ_B.toMatrix).trace
  -- Each cross term factors as a product of local expectations
  have factor_01 : ((kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₁) * ρ).trace = a₀ * b₁ :=
    chsh_local_factor A₀ B₁ ρ_A ρ_B
  have factor_00 : ((kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₀) * ρ).trace = a₀ * b₀ :=
    chsh_local_factor A₀ B₀ ρ_A ρ_B
  have factor_10 : ((kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₀) * ρ).trace = a₁ * b₀ :=
    chsh_local_factor A₁ B₀ ρ_A ρ_B
  have factor_11 : ((kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₁) * ρ).trace = a₁ * b₁ :=
    chsh_local_factor A₁ B₁ ρ_A ρ_B
  have chsh_factors : ((kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₁ -
                        kroneckerMap (· * ·) A₀ 1 * kroneckerMap (· * ·) 1 B₀ +
                        kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₀ +
                        kroneckerMap (· * ·) A₁ 1 * kroneckerMap (· * ·) 1 B₁) * ρ).trace =
                       a₀ * b₁ - a₀ * b₀ + a₁ * b₀ + a₁ * b₁ := by
    rw [add_mul, add_mul, sub_mul]
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_sub]
    rw [factor_01, factor_00, factor_10, factor_11]
  rw [chsh_factors]
  -- Local bounds, |Tr(Aᵢρ_A)|, |Tr(Bⱼρ_B)| ≤ 1
  have ha₀_bound : ‖a₀‖ ≤ 1 := dichotomic_expectation_bound A₀ hA₀ hA₀_sq ρ_A
  have ha₁_bound : ‖a₁‖ ≤ 1 := dichotomic_expectation_bound A₁ hA₁ hA₁_sq ρ_A
  have hb₀_bound : ‖b₀‖ ≤ 1 := dichotomic_expectation_bound B₀ hB₀ hB₀_sq ρ_B
  have hb₁_bound : ‖b₁‖ ≤ 1 := dichotomic_expectation_bound B₁ hB₁ hB₁_sq ρ_B
  -- Local expectations are real, so the classical algebraic bound applies directly
  have ha₀_real := hermitian_expectation_real A₀ hA₀ ρ_A.toMatrix ρ_A.hermitian
  have ha₁_real := hermitian_expectation_real A₁ hA₁ ρ_A.toMatrix ρ_A.hermitian
  have hb₀_real := hermitian_expectation_real B₀ hB₀ ρ_B.toMatrix ρ_B.hermitian
  have hb₁_real := hermitian_expectation_real B₁ hB₁ ρ_B.toMatrix ρ_B.hermitian
  have ha₀_eq : a₀ = (a₀.re : ℂ) := Complex.ext rfl ha₀_real
  have ha₁_eq : a₁ = (a₁.re : ℂ) := Complex.ext rfl ha₁_real
  have hb₀_eq : b₀ = (b₀.re : ℂ) := Complex.ext rfl hb₀_real
  have hb₁_eq : b₁ = (b₁.re : ℂ) := Complex.ext rfl hb₁_real
  rw [ha₀_eq, ha₁_eq, hb₀_eq, hb₁_eq]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.norm_real]
  have ha₀_re_bound : |a₀.re| ≤ 1 := by
    have h : ‖(a₀.re : ℂ)‖ ≤ 1 := ha₀_eq ▸ ha₀_bound
    simpa [Complex.norm_real] using h
  have ha₁_re_bound : |a₁.re| ≤ 1 := by
    have h : ‖(a₁.re : ℂ)‖ ≤ 1 := ha₁_eq ▸ ha₁_bound
    simpa [Complex.norm_real] using h
  have hb₀_re_bound : |b₀.re| ≤ 1 := by
    have h : ‖(b₀.re : ℂ)‖ ≤ 1 := hb₀_eq ▸ hb₀_bound
    simpa [Complex.norm_real] using h
  have hb₁_re_bound : |b₁.re| ≤ 1 := by
    have h : ‖(b₁.re : ℂ)‖ ≤ 1 := hb₁_eq ▸ hb₁_bound
    simpa [Complex.norm_real] using h
  exact chsh_expectation_algebraic_bound a₀.re a₁.re b₀.re b₁.re
    ha₀_re_bound ha₁_re_bound hb₀_re_bound hb₁_re_bound

end Spectra.QuantumInfo

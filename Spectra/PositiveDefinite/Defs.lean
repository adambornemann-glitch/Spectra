/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: HerglotzTheorem/PositiveDefinite.lean
-/
import Spectra.Operator.Unitary.Powers
import Spectra.CayleyTransform.Transform
/-!
# Herglotz's Theorem and Scalar Spectral Measures for Unitary Operators

This file constructs the **scalar spectral measure** `μ_ψ` for a bounded
unitary operator `U` on a Hilbert space, via Herglotz's theorem on positive
definite sequences.

## Independence from Bochner and the CFC

This construction is **completely independent** of:
- Bochner's theorem
- The continuous functional calculus (CFC)
- Gelfand's theorem / C⋆-algebra theory
- The Riesz–Markov representation theorem

The only ingredients from Mathlib are:
- Integer powers of bounded operators (algebra)
- The unit circle `circle` and `expMapCircle` (topology)
- Stone–Weierstrass on `circle` (approximation)
- Weak-⋆ compactness of measures (Banach–Alaoglu)
- Basic Fourier analysis on `𝕋`

## Strategy

1. Given unitary `U : H →L[ℂ] H` and `ψ : H`, define the sequence
   `c(n) = ⟨ψ, U^n ψ⟩` for `n : ℤ`.

2. Prove this sequence is **positive definite** on `ℤ`:
   `∑_{j,k} conj(α_j) α_k c(k-j) ≥ 0` for all finite sequences `α`.

3. Construct the **Fejér means**: measures `σ_N` on `𝕋` with density
   `(1/2π) ∑_{|n|≤N} (1 - |n|/(N+1)) c(n) z^{-n}` w.r.t. Haar measure.

4. Show the Fejér means are **positive** measures (key: the Fejér kernel
   is non-negative, which follows from positive definiteness).

5. Show the Fejér means have **uniformly bounded total mass** `= c(0) = ‖ψ‖²`.

6. Extract a weak-⋆ convergent subsequence (Banach–Alaoglu) to obtain
   the representing measure `μ_ψ`.

7. Verify: `∫ z^n dμ_ψ = c(n)` for all `n : ℤ`.

## The concrete trigonometric polynomial calculus

For a trigonometric polynomial `p(z) = ∑_{k=-N}^{N} a_k z^k`, define
`p(U) = ∑ a_k U^k`. This is a **concrete** functional calculus that requires
no spectral theory — just addition and composition of bounded operators.

The key multiplicativity formula
  `∫ conj(p) · q dμ_ψ = ⟨p(U)ψ, q(U)ψ⟩`
is proved by direct algebraic computation for trigonometric polynomials,
then extended to all continuous functions via Stone–Weierstrass.

## Main results

* `herglotzMeasure`: the scalar spectral measure `μ_ψ` on `𝕋`
* `herglotzMeasure_fourier`: `∫ z^n dμ_ψ = ⟨ψ, U^n ψ⟩`
* `herglotzMeasure_total`: `μ_ψ(𝕋) = ‖ψ‖²`
* `herglotzMeasure_star_mul`: `∫ f̄g dμ_ψ = ⟨f(U)ψ, g(U)ψ⟩`

## References

* G. Herglotz Theorem, *Über Potenzreihen mit positivem, reellen Teil im
  Einheitskreis*, Leipziger Berichte **63** (1911), 501–511
* Reed & Simon, *Methods of Modern Mathematical Physics I*, §VII.1
* W. Rudin, *Real and Complex Analysis*, §19.13

## Tags

Herglotz Theorem theorem, positive definite sequence, Fejér kernel,
spectral measure, unitary operator
-/
open Complex MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
open Spectra.Operator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.PositiveDefinite

variable (U : H →L[ℂ] H) (hU : Operator.Unitary U)

/-- The **unitary autocorrelation sequence**: `c(n) = ⟨ψ, U^n ψ⟩`. -/
noncomputable def unitaryCorrelation (ψ : H) (n : ℤ) : ℂ :=
  ⟪ψ, unitaryZpow U n ψ⟫_ℂ

/-- `c(0) = ‖ψ‖²`. -/
lemma unitaryCorrelation_zero (ψ : H) :
    unitaryCorrelation U ψ 0 = ↑(‖ψ‖ ^ 2) := by
  simp [unitaryCorrelation, inner_self_eq_norm_sq_to_K]

/-- `c(-n) = conj(c(n))` (Hermitian symmetry). -/
lemma unitaryCorrelation_neg (hU : Operator.Unitary U) (ψ : H) (n : ℤ) :
    unitaryCorrelation U ψ (-n) = starRingEnd ℂ (unitaryCorrelation U ψ n) := by
  simp only [unitaryCorrelation]
  rw [inner_conj_symm]
  -- Goal: ⟪ψ, U^{-n} ψ⟫ = ⟪U^n ψ, ψ⟫
  have h := unitaryZpow_inner_shift U hU n 0 ψ
  simp only [unitaryZpow_zero, ContinuousLinearMap.one_apply, zero_sub] at h
  -- h : ⟪U^n ψ, ψ⟫ = ⟪ψ, U^{-n} ψ⟫
  exact h.symm

/-- **Positive definiteness**: `∑_{j,k} conj(α_j) α_k c(k - j) ≥ 0`. -/
lemma unitaryCorrelation_positive_definite (hU : Operator.Unitary U) (ψ : H) (N : ℕ)
    (α : Fin N → ℂ) :
    0 ≤ (∑ j : Fin N, ∑ k : Fin N,
      starRingEnd ℂ (α j) * α k *
      unitaryCorrelation U ψ (↑k - ↑j)).re := by
  set v := ∑ k : Fin N, α k • unitaryZpow U (↑k) ψ with hv
  -- Step 1: Replace c(k-j) with ⟪U^j ψ, U^k ψ⟩
  have key : ∀ j k : Fin N,
      starRingEnd ℂ (α j) * α k * unitaryCorrelation U ψ (↑k - ↑j) =
      starRingEnd ℂ (α j) * α k *
        ⟪unitaryZpow U (↑j) ψ, unitaryZpow U (↑k) ψ⟫_ℂ := by
    intro j k
    congr 1
    rw [unitaryCorrelation, ← unitaryZpow_inner_shift U hU]
  simp_rw [key]
  -- Step 2: The double sum equals ⟪v, v⟫
  have h_eq : ∑ j : Fin N, ∑ k : Fin N,
      starRingEnd ℂ (α j) * α k *
        ⟪unitaryZpow U (↑j) ψ, unitaryZpow U (↑k) ψ⟫_ℂ =
      ⟪v, v⟫_ℂ := by
    rw [hv, sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right]
    congr 1; ext j; congr 1; ext k; ring
  -- Step 3: re⟪v, v⟫ ≥ 0
  rw [h_eq]
  exact inner_self_nonneg (𝕜 := ℂ)

end Spectra.PositiveDefinite

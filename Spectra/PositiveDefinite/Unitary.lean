/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.Unitary.Powers
/-!
# The unitary autocorrelation sequence and its positive-definiteness

This file defines the **unitary autocorrelation sequence** `c(n) = ⟨ψ, Uⁿψ⟩` for `U : H →L[ℂ] H`
and `ψ : H`, and proves the two structural facts about it that the Herglotz construction below
needs to get off the ground: Hermitian symmetry and positive-definiteness of the associated
double sum.

## Main results

* `unitaryCorrelation`: the sequence `c(n) = ⟨ψ, Uⁿψ⟩`.
* `unitaryCorrelation_zero`: `c(0) = ‖ψ‖²`.
* `unitaryCorrelation_neg`: `c(-n) = conj(c(n))` (Hermitian symmetry).
* `unitaryCorrelation_positive_definite`: `∑_{j,k} conj(α_j) α_k c(k-j) ≥ 0` for all finite `α`.

## The Herglotz construction (multi-file project; not complete)

`unitaryCorrelation`'s positive-definiteness is step 1–2 of a longer, **in-progress** program that
aims to construct, for unitary `U` and `ψ : H`, a scalar spectral measure `μ_ψ` on the circle `𝕋`
with `∫ z^n dμ_ψ = c(n)` — Herglotz's theorem on positive-definite sequences, independently of
Bochner's theorem, the continuous functional calculus, Gelfand's theorem, and the Riesz–Markov
representation theorem. The planned steps, and where each currently lives:

1. Define `c(n) = ⟨ψ, Uⁿψ⟩` and prove it positive-definite. **Done — this file.**
2. Construct the Fejér means `σ_N` on `𝕋` from `c`, and show they carry total mass `‖ψ‖²`.
   **Done —** `Herglotz/FejerMeans.lean`, `Herglotz/FejerMeasure.lean`
   (`fejerMeasure`, `fejerMeasure_total`).
3. Package `σ_N`'s CDF and stage it for a Helly-selection argument. **Done —**
   `Herglotz/Stieltjes/CumulativeDistFun.lean` (`fejerCDF`).
4. Extract a Helly-convergent subsequence to obtain the representing measure `μ_ψ`.
   **Not done.** The generic selection theorem exists and is sorry-free
   (`Herglotz/Stieltjes/Hellys.lean`, `helly_selection`), but it has not yet been applied to
   `fejerCDF`.
5. Verify `∫ z^n dμ_ψ = c(n)` and the multiplicativity formula
   `∫ conj(p) · q dμ_ψ = ⟨p(U)ψ, q(U)ψ⟩` for trigonometric polynomials `p`, `q` — via direct
   algebraic computation, then extended to continuous functions by Stone–Weierstrass.
   **Not done.**

`herglotzMeasure`, `herglotzMeasure_fourier`, `herglotzMeasure_total`, and
`herglotzMeasure_star_mul` do **not** exist anywhere in the repository yet: they name the target
of steps 4–5, not a result this file (or any file so far) delivers.

## References

* G. Herglotz, *Über Potenzreihen mit positivem, reellen Teil im
  Einheitskreis*, Leipziger Berichte **63** (1911), 501–511
* Reed & Simon, *Methods of Modern Mathematical Physics I*, §VII.1
* W. Rudin, *Real and Complex Analysis*, §19.13

## Tags

Herglotz theorem, positive definite sequence, Fejér kernel,
spectral measure, unitary operator
-/
open scoped InnerProductSpace
open Spectra.Operator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.PositiveDefinite

variable (U : H →L[ℂ] H)

/-- The **unitary autocorrelation sequence**: `c(n) = ⟨ψ, U^n ψ⟩`. -/
noncomputable def unitaryCorrelation (ψ : H) (n : ℤ) : ℂ :=
  ⟪ψ, unitaryZpow U n ψ⟫_ℂ

/-- `c(0) = ‖ψ‖²`. -/
lemma unitaryCorrelation_zero (ψ : H) :
    unitaryCorrelation U ψ 0 = ↑(‖ψ‖ ^ 2) := by
  simp [unitaryCorrelation, inner_self_eq_norm_sq_to_K]

/-- `c(-n) = conj(c(n))` (Hermitian symmetry). Unlike `unitaryCorrelation_zero`, which holds for
any `U`, this direction genuinely needs unitarity of `U` to relate `c(-n)` and `c(n)` via
`unitaryZpow_inner_shift`. -/
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

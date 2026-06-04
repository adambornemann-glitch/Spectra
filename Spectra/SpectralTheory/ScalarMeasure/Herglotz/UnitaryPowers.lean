/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: SpectralTheory/Herglotz/UnitaryPowers.lean
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Spectra.SpectralTheory.CayleyTransform.Unitary
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

* G. Herglotz, *Über Potenzreihen mit positivem, reellen Teil im
  Einheitskreis*, Leipziger Berichte **63** (1911), 501–511
* Reed & Simon, *Methods of Modern Mathematical Physics I*, §VII.1
* W. Rudin, *Real and Complex Analysis*, §19.13

## Tags

Herglotz theorem, positive definite sequence, Fejér kernel,
spectral measure, unitary operator
-/

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace QuantumMechanics.SpectralTheory

/-! ### §1. Integer powers of unitary operators -/

section UnitaryPowers

variable (U : H →L[ℂ] H)

/-- Integer powers of a unitary operator: `U^n` for `n ≥ 0`,
`(U*)^|n|` for `n < 0`. The definition only uses the adjoint and
does not require unitarity; the algebraic laws do. -/
noncomputable def unitaryZpow : ℤ → (H →L[ℂ] H)
  | (n : ℕ)          => U ^ n
  | (Int.negSucc n)   => U.adjoint ^ (n + 1)

@[simp]
lemma unitaryZpow_zero : unitaryZpow U 0 = 1 := by
  simp [unitaryZpow]

@[simp]
lemma unitaryZpow_one : unitaryZpow U 1 = U := by
  simp [unitaryZpow, pow_one]

@[simp]
lemma unitaryZpow_neg_one : unitaryZpow U (-1) = U.adjoint := by
  simp [unitaryZpow]
  abel

variable (hU : Cayley.Unitary U)

/-- `U^{-n} = (U*)^n` for unitary `U`. -/
lemma unitaryZpow_neg (n : ℕ) (hn : 0 < n) :
    unitaryZpow U (-↑n) = U.adjoint ^ n := by
  cases n with
  | zero => omega
  | succ m => rfl

/-- The inverse of the unit corresponding to U is U.adjoint. -/
private lemma unit_inv_val :
    ((hU.isUnit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = U.adjoint := by
  set u := hU.isUnit.unit
  have hval : (u : H →L[ℂ] H) = U := hU.isUnit.unit_spec
  have hmul : (u : H →L[ℂ] H) * ↑(u⁻¹) = 1 := u.val_inv
  rw [hval] at hmul
  calc ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)
      = U.adjoint * U * ↑(u⁻¹) := by rw [hU.1, one_mul]
    _ = U.adjoint * (U * ↑(u⁻¹)) := by rw [mul_assoc]
    _ = U.adjoint := by rw [hmul, mul_one]

/-- `unitaryZpow` agrees with `zpow` on the unit. -/
private lemma unitaryZpow_eq_unit_zpow (k : ℤ) :
    unitaryZpow U k = ↑(hU.isUnit.unit ^ k) := by
  cases k with
  | ofNat a =>
    simp [unitaryZpow, zpow_natCast, Units.val_pow_eq_pow_val]
  | negSucc a =>
    simp only [unitaryZpow, zpow_negSucc]
    congr 1
    exact Eq.symm (unit_inv_val U hU)

/-- `U^{m+n} = U^m · U^n` for unitary `U`. -/
lemma unitaryZpow_add (hU : Cayley.Unitary U) (m n : ℤ) :
    unitaryZpow U (m + n) =
    (unitaryZpow U m).comp (unitaryZpow U n) := by
  rw [unitaryZpow_eq_unit_zpow U hU, unitaryZpow_eq_unit_zpow U hU,
      unitaryZpow_eq_unit_zpow U hU, zpow_add, Units.val_mul]
  rfl


/-- Natural powers of a unitary preserve inner products. -/
private lemma pow_unitary_inner (V : H →L[ℂ] H) (hV : Cayley.Unitary V)
    (a : ℕ) (x y : H) :
    ⟪(V ^ a) x, (V ^ a) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction a generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply]
    erw [ih (V x) (V y)]
    exact hV.inner_map_map x y

/-- Integer powers of a unitary preserve inner products. -/
private lemma unitaryZpow_inner_map_map (hU : Cayley.Unitary U) (k : ℤ)
    (x y : H) :
    ⟪unitaryZpow U k x, unitaryZpow U k y⟫_ℂ = ⟪x, y⟫_ℂ := by
  cases k with
  | ofNat a => exact pow_unitary_inner U hU a x y
  | negSucc a =>
    have hU_adj : Cayley.Unitary U.adjoint :=
      ⟨by rw [ContinuousLinearMap.adjoint_adjoint]; exact hU.2,
       by rw [ContinuousLinearMap.adjoint_adjoint]; exact hU.1⟩
    exact pow_unitary_inner U.adjoint hU_adj (a + 1) x y

/-- `⟨U^m ψ, U^n ψ⟩ = ⟨ψ, U^{n-m} ψ⟩`. -/
lemma unitaryZpow_inner_shift (hU : Cayley.Unitary U) (m n : ℤ) (ψ : H) :
    ⟪unitaryZpow U m ψ, unitaryZpow U n ψ⟫_ℂ =
    ⟪ψ, unitaryZpow U (n - m) ψ⟫_ℂ := by
  have hfact : unitaryZpow U n = (unitaryZpow U m).comp (unitaryZpow U (n - m)) := by
    rw [← unitaryZpow_add U hU]; congr 1; omega
  rw [hfact, ContinuousLinearMap.comp_apply,
      unitaryZpow_inner_map_map U hU m ψ (unitaryZpow U (n - m) ψ)]


end UnitaryPowers

end QuantumMechanics.SpectralTheory

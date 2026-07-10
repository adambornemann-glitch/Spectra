/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Uncertainty.SchrodingerRobertson

/-!
# The Heisenberg Uncertainty Relation

This module specializes the Robertson inequality to a pair of observables
satisfying the **canonical commutation relation** (CCR) `[A,B]ψ = iℏ·ψ`, yielding
Heisenberg's original bound in its familiar form:

$$\sigma_A \, \sigma_B \;\geq\; \frac{\hbar}{2}.$$

## Main definitions

* `SatisfiesCCR`: the canonical commutation relation `[A,B]ψ = iℏ·ψ` on the
  relevant domain

## Main results

* `norm_inner_commutator_of_ccr`: under the CCR (and `‖ψ‖ = 1`),
  `‖⟨ψ, [A,B]ψ⟩‖ = ℏ`
* `heisenberg_uncertainty`: `σ_A σ_B ≥ ℏ/2` (standard-deviation form)
* `heisenberg_variance`: `Var(A) Var(B) ≥ ℏ²/4` (variance form)

## What this module *does* and *does not* establish

This is the **conditional** Heisenberg relation: it shows that *any* two
self-adjoint observables whose commutator acts as `iℏ` on the state `ψ` obey the
ℏ/2 bound. The proof is purely algebraic — it plugs the CCR into Robertson's
inequality and computes `‖⟨ψ, iℏ·ψ⟩‖ = ℏ` (using `‖ψ‖ = 1`). This is the content
usually meant by "the uncertainty principle follows from the commutation
relation".

It does **not** construct the position and momentum operators, nor prove that
they realize the CCR. On `L²(ℝ)` the canonical pair is `X = (mult. by x)` and
`P = -iℏ d/dx`, essentially self-adjoint on the Schwartz space `𝒮(ℝ)`, with
`[X,P] = iℏ` on that domain. Building these as `SelfAdjointOperator`s and
discharging their self-adjointness (via the Fourier transform conjugating `P` to
`X`, deficiency-index analysis, etc.) is a substantial separate development and
is left as future work; the relevant Sobolev/self-adjointness infrastructure is
only partially available in Mathlib. Once such `X P : SelfAdjointOperator (Lp ℂ 2)`
and a proof of `SatisfiesCCR X P ψ h ℏ` exist, `heisenberg_uncertainty` applies
verbatim to give `σ_X σ_P ≥ ℏ/2`.

## References

* [Heisenberg, "Über den anschaulichen Inhalt..."][heisenberg1927]
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapter 12 (the CCR and
  its uniqueness, Stone–von Neumann)

## Tags

uncertainty principle, Heisenberg, canonical commutation relation, position, momentum
-/
namespace Spectra.QuantumMechanics.Heisenberg

open Operator SymmetricOperator Schrodinger
open scoped ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **canonical commutation relation** at `ψ`: the commutator `[A,B]ψ` acts as
multiplication by `iℏ`, i.e. `[A,B]ψ = (iℏ)·ψ`. -/
def SatisfiesCCR (A B : SelfAdjointOperator H) (ψ : H)
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) (ℏ : ℝ) : Prop :=
  commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions
    = (Complex.I * (ℏ : ℂ)) • ψ

/-- Under the canonical commutation relation, the expectation of the commutator has
norm `ℏ`: `‖⟨ψ, [A,B]ψ⟩‖ = ℏ`. (Uses normalization `‖ψ‖ = 1`, carried by `h`.) -/
lemma norm_inner_commutator_of_ccr (A B : SelfAdjointOperator H) (ψ : H)
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ)
    (ℏ : ℝ) (hℏ : 0 ≤ ℏ)
    (hccr : commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions
            = (Complex.I * (ℏ : ℂ)) • ψ) :
    ‖⟪ψ, commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ h.toDomainConditions⟫_ℂ‖
    = ℏ := by
  have hself : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, h.h_norm]; simp
  rw [hccr, inner_smul_right, hself, mul_one, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hℏ]

/-- **Heisenberg uncertainty relation** (standard-deviation form). For self-adjoint
observables `A`, `B` whose commutator acts as `iℏ` on a normalized state `ψ`,
`σ_A σ_B ≥ ℏ/2`. -/
theorem heisenberg_uncertainty (A B : SelfAdjointOperator H) (ψ : H)
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ)
    (ℏ : ℝ) (hℏ : 0 ≤ ℏ) (hccr : SatisfiesCCR A B ψ h ℏ) :
    A.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_A *
        B.toSymmetricOperator.stdDev ψ h.h_norm h.hψ_B ≥ ℏ / 2 := by
  have hrob := observable_robertson_stddev A B ψ h
  rw [norm_inner_commutator_of_ccr A B ψ h ℏ hℏ hccr] at hrob
  linarith

/-- **Heisenberg uncertainty relation** (variance form): `Var(A) Var(B) ≥ ℏ²/4`. -/
theorem heisenberg_variance (A B : SelfAdjointOperator H) (ψ : H)
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ)
    (ℏ : ℝ) (hℏ : 0 ≤ ℏ) (hccr : SatisfiesCCR A B ψ h ℏ) :
    A.toSymmetricOperator.variance ψ h.h_norm h.hψ_A *
        B.toSymmetricOperator.variance ψ h.h_norm h.hψ_B ≥ ℏ^2 / 4 := by
  have hrob := observable_robertson_uncertainty A B ψ h
  rw [norm_inner_commutator_of_ccr A B ψ h ℏ hℏ hccr] at hrob
  linarith


end Spectra.QuantumMechanics.Heisenberg

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Uncertainty.SchrodingerRobertson
import Spectra.QuantumMechanics.BornRule.Observable

open scoped InnerProductSpace
open Spectra.Operator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.BornRule
namespace Uncertainty
open PVM Moments

/-! ## §4  Uncertainty, as a Born-rule statement

The Robertson / Schrödinger inequalities are already proved on `SymmetricOperator`
(`Spectra.QuantumMechanics.Uncertainty.SchrodingerRobertson`).  `bornVariance_eq_central_moment`
identifies `bornVariance` with the variance those theorems bound, so the uncertainty relation
*is* a statement about Born variances — composed, not reproved. -/

/-- `[done]` **Born variance = operator variance.**  The second central moment of the Born
outcome distribution is exactly the Robertson variance `‖(A − ⟨A⟩)ψ‖²` of the underlying
self-adjoint operator, for a unit state in the domain.  This is the bridge that lets the
operator-level Schrödinger / Robertson inequalities be read as statements about Born
variances: it composes `bornVariance_eq_central_moment` (variance as a squared norm) with
`bornExpectation_eq_inner` (mean as the matrix element `⟪ψ, Aψ⟫`), after which both sides are
the *same* squared norm `‖Aψ − ⟨A⟩ψ‖²` definitionally. -/
lemma bornVariance_eq_variance (A : SelfAdjointOperator H) {ψ : H}
    (hψ_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) :
    bornVariance A.spectralPVM ψ = A.toSymmetricOperator.variance ψ hψ_norm hψ := by
  rw [Observable.bornVariance_eq_central_moment A hψ,
      Observable.bornExpectation_eq_inner A hψ]
  rfl

/-- `[done]` **The uncertainty relation in Born form** (Robertson shape).  The product of the
outcome-distribution variances of two observables is bounded below by their commutator term:

  `(Δ_ψ A)² · (Δ_ψ B)² ≥ ¼ ‖⟪ψ, [A,B]ψ⟫‖²`.

The hypothesis is bundled as `ShiftedDomainConditions A B ψ` — exactly the data
(`‖ψ‖ = 1`, `ψ ∈ Dom A ∩ Dom B`, and `Bψ ∈ Dom A`, `Aψ ∈ Dom B`) that makes the commutator
`[A,B]ψ` well-defined — matching the operator-level `Schrodinger.observable_robertson_uncertainty`
verbatim.  Proof: rewrite each Born variance as the operator variance via
`bornVariance_eq_variance`, then apply Robertson. -/
theorem bornVariance_uncertainty (A B : SelfAdjointOperator H) {ψ : H}
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) :
    bornVariance A.spectralPVM ψ * bornVariance B.spectralPVM ψ
      ≥ (1 / 4) * ‖⟪ψ, SymmetricOperator.commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ
          h.toDomainConditions⟫_ℂ‖ ^ 2 := by
  rw [bornVariance_eq_variance A h.h_norm h.hψ_A,
      bornVariance_eq_variance B h.h_norm h.hψ_B]
  exact Schrodinger.observable_robertson_uncertainty A B ψ h

/-! ## §5  Dynamical consistency (already proven, here recontextualized)

`Conservation.probability_conserved` (in this same `BornRule` namespace) is **not** the Born
rule; it is the corollary `(Born rule) + (unitary evolution) ⟹ total probability preserved`.
Aliased here under a name that says so, so the Dirac result reads as what it is. -/

/-- `[done]` **Conservation of total Born probability under Dirac evolution.**  The
normalization-preservation that the Born interpretation must satisfy; a consequence of
unitarity, not the assignment of probabilities itself.  Alias of `probability_conserved`. -/
alias total_born_probability_conserved := probability_conserved

end Uncertainty
end Spectra.QuantumMechanics.BornRule

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Uncertainty.SchrodingerRobertson
import Spectra.QuantumMechanics.BornRule.Observable

/-!
# Uncertainty, as a Born-rule statement

The Robertson and Schrödinger uncertainty inequalities are already proved at the operator level on
`SymmetricOperator` (`Spectra.QuantumMechanics.Uncertainty.SchrodingerRobertson`).  This file does
**not** reprove them.  Instead it identifies the second central moment of the Born outcome
distribution, `bornVariance A.spectralPVM ψ`, with the operator variance `‖(A − ⟨A⟩)ψ‖²` that those
theorems bound, and then reads the operator-level inequality off as a statement about Born
variances.  The uncertainty relation therefore *is* a theorem about the outcome-distribution
variances predicted by the Born rule — obtained by composition, not by a second proof.

## Main results

* `bornVariance_eq_operatorVariance` — the bridge identity: the Born second central moment equals
  the Robertson operator variance, for a unit state in the operator's domain.
* `bornVariance_uncertainty` — the Robertson uncertainty relation in Born form,
  `(Δ_ψ A)² · (Δ_ψ B)² ≥ ¼ ‖⟪ψ, [A,B]ψ⟫‖²`, for the outcome distributions of two observables.

## Implementation notes

The design is *composition, not reproof*.  `bornVariance_eq_operatorVariance` closes by two rewrites
(`bornVariance_eq_central_moment`, `bornExpectation_eq_inner`) followed by `rfl`, because both sides
unfold to the same squared norm `‖Aψ − ⟨A⟩ψ‖²`; `bornVariance_uncertainty` then rewrites both Born
variances into operator variances and applies `Schrodinger.observable_robertson_uncertainty`.  The
hypothesis bundle `ShiftedDomainConditions` is taken verbatim from that operator-level theorem so
the Born-form statement carries exactly the domain data needed to make the commutator well-defined.

§5 recontextualizes an unrelated conservation corollary living in the same `BornRule` namespace; see
its docstring for why it is aliased here.

## References

* H. P. Robertson, *The uncertainty principle*, Phys. Rev. **34** (1929), 163–164 (the general
  Robertson inequality for two observables).
* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*], §VIII
  (self-adjoint operators and their spectral/variance calculus).
-/

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
lemma bornVariance_eq_operatorVariance (A : SelfAdjointOperator H) {ψ : H}
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
`bornVariance_eq_operatorVariance`, then apply Robertson. -/
theorem bornVariance_uncertainty (A B : SelfAdjointOperator H) {ψ : H}
    (h : ShiftedDomainConditions A.toSymmetricOperator B.toSymmetricOperator ψ) :
    bornVariance A.spectralPVM ψ * bornVariance B.spectralPVM ψ
      ≥ (1 / 4) * ‖⟪ψ, SymmetricOperator.commutatorAt A.toSymmetricOperator B.toSymmetricOperator ψ
          h.toDomainConditions⟫_ℂ‖ ^ 2 := by
  rw [bornVariance_eq_operatorVariance A h.h_norm h.hψ_A,
      bornVariance_eq_operatorVariance B h.h_norm h.hψ_B]
  exact Schrodinger.observable_robertson_uncertainty A B ψ h

/-! ## §5  Dynamical consistency (already proven, here recontextualized)

`probability_conserved` (in this same `BornRule` namespace, from `Unitarity/Basic.lean`) is **not**
the Born rule; it is the corollary that `(Born rule) + (unitary evolution)` preserves total
probability.  Aliased here under a name that says so, so the Dirac result reads as what it is.  The
topic (Dirac current conservation) is unrelated to variance; whether this alias should instead live
beside `probability_conserved` in `Unitarity/Basic.lean`, or in a dedicated `BornRule/Consistency`,
is an open architecture question. -/

/-- `[done]` **Conservation of total Born probability under Dirac evolution.**  The
normalization-preservation that the Born interpretation must satisfy; a consequence of
unitarity, not the assignment of probabilities itself.  Alias of `probability_conserved`.

The inherited hypothesis bundle is exactly that of `probability_conserved`: the spinor solves the
Dirac equation, the density is differentiable, and its measurability / integrability plus a
dominating `L¹` bound license differentiation under the integral; the spatial current is
divergence-integrable and decays to `0` at spatial infinity so the boundary term vanishes. -/
alias total_born_probability_conserved := probability_conserved

end Uncertainty
end Spectra.QuantumMechanics.BornRule

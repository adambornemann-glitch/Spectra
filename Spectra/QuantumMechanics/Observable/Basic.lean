/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Observable/Basic.lean
-/
import Spectra.Operator.Symmetric
/-!
# Unbounded Observables (self-adjoint operators)

This module refines `SymmetricOperator` to the genuine physical notion of a
quantum observable: a *self-adjoint* unbounded operator. Where the symmetric
layer assumes only formal self-adjointness (`⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫` on the domain),
an observable additionally satisfies the domain equality `Dom(A) = Dom(A†)`,
encoded here as `IsSelfAdjoint A` for the `LinearPMap` star structure (`A† = A`).

## Design philosophy

Self-adjointness is the *single* primitive assumption. Both facts the symmetric
layer takes as hypotheses — dense domain and symmetry — are **derived** here as
lemmas:

* density comes from `IsSelfAdjoint.dense_domain`;
* symmetry (`IsFormalAdjoint A A`) comes from `adjoint_isFormalAdjoint` composed
  with `A† = A`.

Consequently `UnboundedObservable` stores no redundant data: just the underlying
`LinearPMap` and a proof that it is self-adjoint. The coercion
`toSymmetricOperator` reconstructs the weaker structure, so every result proved
for `SymmetricOperator` — in particular the Robertson and Schrödinger uncertainty
inequalities — applies to observables via `A.toSymmetricOperator` (or the `Coe`).

Why keep the uncertainty lemmas on `SymmetricOperator` rather than restating
them here for observables? Because they never use the domain equality: their true
hypothesis is symmetry, and stating them at that generality is the mathematically
honest level (a symmetric-but-not-self-adjoint operator still obeys Robertson).
The observable layer is the *physics* object; the symmetric layer is the *minimal
hypothesis* for the inequality. This file connects the two without conflating them.

## Main definitions

* `UnboundedObservable`: a self-adjoint (unbounded) operator on `H`
* `UnboundedObservable.toSymmetricOperator`: the underlying symmetric operator,
  with density and symmetry derived from self-adjointness

## Main results

* `isFormalAdjoint_self_of_isSelfAdjoint`: self-adjoint ⟹ formally self-adjoint
* `UnboundedObservable.adjoint_eq`: `A† = A`

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapters 9–10

## Tags

unbounded operator, self-adjoint operator, observable, adjoint
-/
open Spectra.Operator
open InnerProductSpace
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.Observable

/-- A self-adjoint `LinearPMap` is formally self-adjoint (symmetric): on its
domain, `⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫`.

The proof is the canonical one: the adjoint is always a formal adjoint of a
densely-defined operator (`adjoint_isFormalAdjoint`), and self-adjointness
identifies `A†` with `A`. -/
lemma isFormalAdjoint_self_of_isSelfAdjoint {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) : A.IsFormalAdjoint A := by
  have hadj : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have h := A.adjoint_isFormalAdjoint hA.dense_domain
  rwa [hadj] at h

/-- A **quantum observable**: a self-adjoint (possibly unbounded) operator on the
Hilbert space `H`. The single field beyond the operator itself is the proof of
self-adjointness `A† = A`; density and symmetry are derived (see
`toSymmetricOperator`). -/
structure UnboundedObservable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying partially-defined linear map. -/
  toLinearPMap : H →ₗ.[ℂ] H
  /-- The operator is self-adjoint: `A† = A`, including the domain equality. -/
  selfAdjoint : IsSelfAdjoint toLinearPMap

namespace UnboundedObservable

/-- The (dense) domain of the observable. -/
def domain (A : UnboundedObservable H) : Submodule ℂ H :=
  A.toLinearPMap.domain

/-- The domain is dense (derived from self-adjointness). -/
lemma dense (A : UnboundedObservable H) : Dense (A.domain : Set H) :=
  A.selfAdjoint.dense_domain

/-- The adjoint equals the operator. -/
lemma adjoint_eq (A : UnboundedObservable H) : A.toLinearPMap.adjoint = A.toLinearPMap :=
  LinearPMap.isSelfAdjoint_def.mp A.selfAdjoint

/-- Every observable is, in particular, a symmetric operator. Its density and
symmetry are *derived* from self-adjointness rather than separately assumed. -/
def toSymmetricOperator (A : UnboundedObservable H) : SymmetricOperator H where
  toLinearPMap := A.toLinearPMap
  dense := A.selfAdjoint.dense_domain
  symmetric := isFormalAdjoint_self_of_isSelfAdjoint A.selfAdjoint

instance : Coe (UnboundedObservable H) (SymmetricOperator H) where
  coe := toSymmetricOperator

@[simp] lemma toSymmetricOperator_toLinearPMap (A : UnboundedObservable H) :
    A.toSymmetricOperator.toLinearPMap = A.toLinearPMap := rfl

@[simp] lemma toSymmetricOperator_domain (A : UnboundedObservable H) :
    A.toSymmetricOperator.domain = A.domain := rfl

/-- Symmetry with explicit domain proofs, inherited from the symmetric layer:
`⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫`. -/
lemma symmetric' (A : UnboundedObservable H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    ⟪A.toSymmetricOperator ⬝ ψ ⊢ hψ, φ⟫_ℂ = ⟪ψ, A.toSymmetricOperator ⬝ φ ⊢ hφ⟫_ℂ :=
  A.toSymmetricOperator.symmetric' hψ hφ

end UnboundedObservable
end Spectra.QuantumMechanics.Observable

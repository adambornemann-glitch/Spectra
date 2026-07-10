/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.Symmetric
/-!
# Self-Adjoint Operators

This module refines `SymmetricOperator` to genuine self-adjointness. Where the
symmetric layer assumes only formal self-adjointness (`⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫` on the
domain), a `SelfAdjointOperator` additionally satisfies the domain equality
`Dom(A) = Dom(A†)`, encoded here as `IsSelfAdjoint A` for the `LinearPMap` star
structure (`A† = A`).

Self-adjointness is a property of the operator, not of its domain: nothing here
requires `domain ≠ ⊤`, so a `SelfAdjointOperator` may be bounded or unbounded —
"unbounded" is a fact about particular instances (position, momentum), never a
hypothesis of the type itself. This file is pure operator theory; it carries no
physics content. The physics-facing *observable* layer built on top of it —
Stone's theorem in observable form, Schrödinger evolution, the Born rule — lives
in `Spectra/QuantumMechanics/Generator/Basic.lean` and
`Spectra/QuantumMechanics/BornRule/Observable.lean`, which extend this
namespace from outside.

## Design philosophy

Self-adjointness is the *single* primitive assumption. Both facts the symmetric
layer takes as hypotheses — dense domain and symmetry — are **derived** here as
lemmas:

* density comes from `IsSelfAdjoint.dense_domain`;
* symmetry (`IsFormalAdjoint A A`) comes from `adjoint_isFormalAdjoint` composed
  with `A† = A`.

Consequently `SelfAdjointOperator` stores no redundant data: just the underlying
`LinearPMap` and a proof that it is self-adjoint. The coercion
`toSymmetricOperator` reconstructs the weaker structure, so every result proved
for `SymmetricOperator` — in particular the Robertson and Schrödinger uncertainty
inequalities — applies here via `A.toSymmetricOperator` (or the `Coe`).

Why keep the uncertainty lemmas on `SymmetricOperator` rather than restating
them here? Because they never use the domain equality: their true hypothesis is
symmetry, and stating them at that generality is the mathematically honest level
(a symmetric-but-not-self-adjoint operator still obeys Robertson).

## Main definitions

* `SelfAdjointOperator`: a self-adjoint (possibly unbounded) operator on `H`
* `SelfAdjointOperator.toSymmetricOperator`: the underlying symmetric operator,
  with density and symmetry derived from self-adjointness

## Main results

* `isFormalAdjoint_self_of_isSelfAdjoint`: self-adjoint ⟹ formally self-adjoint
* `SelfAdjointOperator.adjoint_eq`: `A† = A`
* `SelfAdjointOperator.ext`: two self-adjoint operators with the same
  underlying `LinearPMap` are equal (the `selfAdjoint` field is a `Prop`)

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapters 9–10

## Tags

self-adjoint operator, unbounded operator, adjoint, observable
-/
open InnerProductSpace
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Operator

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

/-- A **self-adjoint operator**: a self-adjoint (possibly unbounded) operator on
the Hilbert space `H`. The single field beyond the operator itself is the proof
of self-adjointness `A† = A`; density and symmetry are derived (see
`toSymmetricOperator`). -/
structure SelfAdjointOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying partially-defined linear map. -/
  toLinearPMap : H →ₗ.[ℂ] H
  /-- The operator is self-adjoint: `A† = A`, including the domain equality. -/
  selfAdjoint : IsSelfAdjoint toLinearPMap

namespace SelfAdjointOperator

/-- Two self-adjoint operators with the same underlying `LinearPMap` are equal.
The `selfAdjoint` field is a `Prop`, so this is proof irrelevance. -/
@[ext] lemma ext {A B : SelfAdjointOperator H}
    (h : A.toLinearPMap = B.toLinearPMap) : A = B := by
  cases A; cases B; cases h; rfl

/-- The (dense) domain of the operator. -/
def domain (A : SelfAdjointOperator H) : Submodule ℂ H :=
  A.toLinearPMap.domain

/-- The domain is dense (derived from self-adjointness). -/
lemma dense (A : SelfAdjointOperator H) : Dense (A.domain : Set H) :=
  A.selfAdjoint.dense_domain

/-- The adjoint equals the operator. -/
lemma adjoint_eq (A : SelfAdjointOperator H) : A.toLinearPMap.adjoint = A.toLinearPMap :=
  LinearPMap.isSelfAdjoint_def.mp A.selfAdjoint

/-- Every self-adjoint operator is, in particular, a symmetric operator. Its
density and symmetry are *derived* from self-adjointness rather than
separately assumed. -/
def toSymmetricOperator (A : SelfAdjointOperator H) : SymmetricOperator H where
  toLinearPMap := A.toLinearPMap
  dense := A.selfAdjoint.dense_domain
  symmetric := isFormalAdjoint_self_of_isSelfAdjoint A.selfAdjoint

instance : Coe (SelfAdjointOperator H) (SymmetricOperator H) where
  coe := toSymmetricOperator

@[simp] lemma toSymmetricOperator_toLinearPMap (A : SelfAdjointOperator H) :
    A.toSymmetricOperator.toLinearPMap = A.toLinearPMap := rfl

@[simp] lemma toSymmetricOperator_domain (A : SelfAdjointOperator H) :
    A.toSymmetricOperator.domain = A.domain := rfl

/-- Symmetry with explicit domain proofs, inherited from the symmetric layer:
`⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫`. -/
lemma symmetric' (A : SelfAdjointOperator H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    ⟪A.toSymmetricOperator ⬝ ψ ⊢ hψ, φ⟫_ℂ = ⟪ψ, A.toSymmetricOperator ⬝ φ ⊢ hφ⟫_ℂ :=
  A.toSymmetricOperator.symmetric' hψ hφ

end SelfAdjointOperator
end Spectra.Operator

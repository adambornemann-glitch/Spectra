/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic
/-!
# Symmetric Operators

This module provides the type-theoretic foundation for (possibly unbounded)
symmetric operators in quantum mechanics. The key design decision is that
unbounded operators are modeled as genuinely partial functions: the type system
enforces that you cannot apply an operator without proving membership in its
domain.

Concretely, a `SymmetricOperator` *bundles* a Mathlib `LinearPMap` (`H →ₗ.[ℂ] H`,
the library's partially-defined linear map) together with proofs of dense domain
and formal self-adjointness. Building on `LinearPMap` rather than a bespoke
`domain →ₗ[ℂ] H` field means the genuine unbounded adjoint `toLinearPMap.adjoint`
and the real `IsSelfAdjoint` predicate are available to downstream refinements
(see `Operator/SelfAdjoint.lean`), instead of having to be re-derived by hand.

## Main definitions

* `SymmetricOperator`: A symmetric operator with dense domain, backed by `LinearPMap`
* `DomainConditions`: Bundled proof that [A,B]ψ is well-defined
* `commutatorAt`: The commutator [A,B]ψ = ABψ - BAψ
* `anticommutatorAt`: The anticommutator {A,B}ψ = ABψ + BAψ
* `expectation`: ⟨A⟩_ψ = Re⟨ψ, Aψ⟩
* `variance`: Var(A)_ψ = ‖(A - ⟨A⟩)ψ‖²
* `stdDev`: σ_A = √Var(A)

## Main statements

* `symmetric'`: ⟨Aψ, φ⟩ = ⟨ψ, Aφ⟩ for ψ, φ in the domain
* `inner_self_im_eq_zero`: Expectation values are real
* `commutator_re_eq_zero`: ⟨ψ, [A,B]ψ⟩ is purely imaginary
* `anticommutator_im_eq_zero`: ⟨ψ, {A,B}ψ⟩ is purely real
* `shifted_symmetric`: The shifted operator A - ⟨A⟩I is symmetric

## Design notes

We use `Submodule ℂ H` for domains (via `LinearPMap.domain`), ensuring closure
under linear combinations. The notation `A ⬝ ψ ⊢ hψ` makes domain proofs explicit
at the call site. The `symmetric` field is the formal self-adjointness condition
`T.IsFormalAdjoint T`, which unfolds to `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.

Note that symmetric ≠ self-adjoint for unbounded operators. Self-adjointness
requires additionally that Dom(A) = Dom(A*). This module only assumes symmetry,
which is the natural hypothesis for the Robertson/Schrödinger uncertainty
inequalities (they never use the domain equality). The self-adjoint refinement
lives in `Operator/SelfAdjoint.lean`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapter 9

## Tags

unbounded operator, symmetric operator, observable, commutator, uncertainty
-/
namespace Spectra.Operator

open InnerProductSpace
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A symmetric operator with dense domain.

It is backed by a Mathlib `LinearPMap` (`H →ₗ.[ℂ] H`); the `symmetric` field is
formal self-adjointness, `toLinearPMap.IsFormalAdjoint toLinearPMap`. -/
structure SymmetricOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying partially-defined linear map. -/
  toLinearPMap : H →ₗ.[ℂ] H
  /-- The domain is dense. -/
  dense : Dense (toLinearPMap.domain : Set H)
  /-- Formal self-adjointness: `∀ ψ φ ∈ domain, ⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫`. -/
  symmetric : toLinearPMap.IsFormalAdjoint toLinearPMap

namespace SymmetricOperator

/-- The (dense) domain of the operator. -/
def domain (A : SymmetricOperator H) : Submodule ℂ H :=
  A.toLinearPMap.domain

/-- Apply `A` to `ψ` given a proof `hψ : ψ ∈ A.domain`. -/
@[inline]
def apply (A : SymmetricOperator H) (ψ : H) (hψ : ψ ∈ A.domain) : H :=
  A.toLinearPMap ⟨ψ, hψ⟩

/-- Notation `A ⬝ ψ ⊢ hψ` for applying an unbounded operator with explicit domain proof. -/
notation:max A " ⬝ " ψ " ⊢ " hψ => SymmetricOperator.apply A ψ hψ

/-- Coerce a `SymmetricOperator` to a function `A.domain → H` via its `LinearPMap`. -/
instance : CoeFun (SymmetricOperator H) (fun A => A.domain → H) where
  coe A x := A.toLinearPMap x

/-- Coerce `ψ : H` with `hψ : ψ ∈ A.domain` to an element of `A.domain`. (Currently unused.) -/
@[inline]
def toDomainElt (A : SymmetricOperator H) (ψ : H) (hψ : ψ ∈ A.domain) : A.domain :=
  ⟨ψ, hψ⟩

/-- Symmetry with explicit domain proofs: `⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫`. -/
lemma symmetric' (A : SymmetricOperator H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    ⟪A ⬝ ψ ⊢ hψ, φ⟫_ℂ = ⟪ψ, A ⬝ φ ⊢ hφ⟫_ℂ :=
  A.symmetric ⟨ψ, hψ⟩ ⟨φ, hφ⟩

/-- Expectation values are real: `⟪ψ, Aψ⟫` has zero imaginary part. -/
lemma inner_self_im_eq_zero (A : SymmetricOperator H) {ψ : H} (hψ : ψ ∈ A.domain) :
    (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).im = 0 := by
  have h := A.symmetric' hψ hψ
  rw [← inner_conj_symm] at h
  have := congr_arg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- `⟪ψ, Aψ⟫` equals its real part. -/
lemma inner_self_eq_re (A : SymmetricOperator H) {ψ : H} (hψ : ψ ∈ A.domain) :
    ⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ = (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).re := by
  simp [Complex.ext_iff, A.inner_self_im_eq_zero hψ]

/-- `A` respects addition. (Currently unused.) -/
lemma apply_add (A : SymmetricOperator H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    A.apply (ψ + φ) (A.domain.add_mem hψ hφ) = A.apply ψ hψ + A.apply φ hφ :=
  A.toLinearPMap.map_add ⟨ψ, hψ⟩ ⟨φ, hφ⟩

/-- `A` respects scalar multiplication. -/
lemma apply_smul (A : SymmetricOperator H) {ψ : H} (c : ℂ) (hψ : ψ ∈ A.domain) :
    A.apply (c • ψ) (A.domain.smul_mem c hψ) = c • A.apply ψ hψ :=
  A.toLinearPMap.map_smul c ⟨ψ, hψ⟩

/-- `A` respects subtraction. -/
lemma apply_sub (A : SymmetricOperator H) {ψ φ : H}
    (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) :
    A.apply (ψ - φ) (A.domain.sub_mem hψ hφ) = A.apply ψ hψ - A.apply φ hφ :=
  A.toLinearPMap.map_sub ⟨ψ, hψ⟩ ⟨φ, hφ⟩

/-- `A` respects real scalar multiplication. (Currently unused.) -/
lemma apply_smul_real (A : SymmetricOperator H) {ψ : H} (r : ℝ) (hψ : ψ ∈ A.domain) :
    A.apply ((r : ℂ) • ψ) (A.domain.smul_mem (r : ℂ) hψ) = (r : ℂ) • A.apply ψ hψ :=
  apply_smul A (r : ℂ) hψ

/-- Bundled proof that `[A,B]ψ` is well-defined: `ψ ∈ Dom(A) ∩ Dom(B)`,
    `Bψ ∈ Dom(A)`, and `Aψ ∈ Dom(B)`. -/
structure DomainConditions (A B : SymmetricOperator H) (ψ : H) where
  hψ_A : ψ ∈ A.domain
  hψ_B : ψ ∈ B.domain
  hBψ_A : B.apply ψ hψ_B ∈ A.domain
  hAψ_B : A.apply ψ hψ_A ∈ B.domain

namespace DomainConditions

variable {A B : SymmetricOperator H} {ψ : H}

/-- `Aψ` given domain conditions for `[A,B]ψ`. -/
def Aψ (h : DomainConditions A B ψ) : H := A ⬝ ψ ⊢ h.hψ_A

/-- `Bψ` given domain conditions for `[A,B]ψ`. -/
def Bψ (h : DomainConditions A B ψ) : H := B ⬝ ψ ⊢ h.hψ_B

/-- `ABψ` given domain conditions for `[A,B]ψ`. -/
def ABψ (h : DomainConditions A B ψ) : H := A ⬝ (B ⬝ ψ ⊢ h.hψ_B) ⊢ h.hBψ_A

/-- `BAψ` given domain conditions for `[A,B]ψ`. -/
def BAψ (h : DomainConditions A B ψ) : H := B ⬝ (A ⬝ ψ ⊢ h.hψ_A) ⊢ h.hAψ_B

end DomainConditions

/-- The commutator `[A,B]ψ = ABψ - BAψ`. -/
def commutatorAt (A B : SymmetricOperator H) (ψ : H) (h : DomainConditions A B ψ) : H :=
  h.ABψ - h.BAψ

/-- The anticommutator `{A,B}ψ = ABψ + BAψ`. -/
def anticommutatorAt (A B : SymmetricOperator H) (ψ : H) (h : DomainConditions A B ψ) : H :=
  h.ABψ + h.BAψ

/-- `⟪ψ, [A,B]ψ⟫` is purely imaginary. -/
lemma commutator_re_eq_zero (A B : SymmetricOperator H) (ψ : H)
    (h : DomainConditions A B ψ) :
    (⟪ψ, commutatorAt A B ψ h⟫_ℂ).re = 0 := by
  unfold commutatorAt DomainConditions.ABψ DomainConditions.BAψ
  simp only [inner_sub_right]
  have h1 : ⟪ψ, A ⬝ (B ⬝ ψ ⊢ h.hψ_B) ⊢ h.hBψ_A⟫_ℂ =
            ⟪A ⬝ ψ ⊢ h.hψ_A, B ⬝ ψ ⊢ h.hψ_B⟫_ℂ := by
    exact Eq.symm (symmetric' A h.hψ_A h.hBψ_A)
  have h2 : ⟪ψ, B ⬝ (A ⬝ ψ ⊢ h.hψ_A) ⊢ h.hAψ_B⟫_ℂ =
            ⟪B ⬝ ψ ⊢ h.hψ_B, A ⬝ ψ ⊢ h.hψ_A⟫_ℂ := by
    exact Eq.symm (symmetric' B h.hψ_B h.hAψ_B)
  rw [h1, h2, ← inner_conj_symm (B ⬝ ψ ⊢ h.hψ_B) (A ⬝ ψ ⊢ h.hψ_A)]
  simp only [Complex.sub_re, Complex.conj_re]
  ring

/-- `⟪ψ, {A,B}ψ⟫` is purely real. -/
lemma anticommutator_im_eq_zero (A B : SymmetricOperator H) (ψ : H)
    (h : DomainConditions A B ψ) :
    (⟪ψ, anticommutatorAt A B ψ h⟫_ℂ).im = 0 := by
  unfold anticommutatorAt DomainConditions.ABψ DomainConditions.BAψ
  simp only [inner_add_right]
  have h1 : ⟪ψ, A ⬝ (B ⬝ ψ ⊢ h.hψ_B) ⊢ h.hBψ_A⟫_ℂ =
            ⟪A ⬝ ψ ⊢ h.hψ_A, B ⬝ ψ ⊢ h.hψ_B⟫_ℂ := by
    exact Eq.symm (symmetric' A h.hψ_A h.hBψ_A)
  have h2 : ⟪ψ, B ⬝ (A ⬝ ψ ⊢ h.hψ_A) ⊢ h.hAψ_B⟫_ℂ =
            ⟪B ⬝ ψ ⊢ h.hψ_B, A ⬝ ψ ⊢ h.hψ_A⟫_ℂ := by
    exact Eq.symm (symmetric' B h.hψ_B h.hAψ_B)
  rw [h1, h2, ← inner_conj_symm (B ⬝ ψ ⊢ h.hψ_B) (A ⬝ ψ ⊢ h.hψ_A)]
  simp only [Complex.add_im, Complex.conj_im]
  ring

/-- The expectation value `⟨A⟩_ψ = Re⟨ψ, Aψ⟩` for a normalized state. -/
noncomputable def expectation (A : SymmetricOperator H) (ψ : H)
    (_ : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  (⟪ψ, A ⬝ ψ ⊢ hψ⟫_ℂ).re

/-- The shifted operator `(A - ⟨A⟩_ψ)φ` applied to `φ`. -/
noncomputable def shiftedApply (A : SymmetricOperator H) (ψ : H) (φ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) (hφ : φ ∈ A.domain) : H :=
  (A ⬝ φ ⊢ hφ) - (A.expectation ψ h_norm hψ : ℂ) • φ

/-- The shifted operator `A - ⟨A⟩I` is symmetric. -/
lemma shifted_symmetric (A : SymmetricOperator H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ_dom : ψ ∈ A.domain)
    {φ₁ φ₂ : H} (hφ₁ : φ₁ ∈ A.domain) (hφ₂ : φ₂ ∈ A.domain) :
    ⟪A.shiftedApply ψ φ₁ h_norm hψ_dom hφ₁, φ₂⟫_ℂ =
    ⟪φ₁, A.shiftedApply ψ φ₂ h_norm hψ_dom hφ₂⟫_ℂ := by
  unfold shiftedApply
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [A.symmetric' hφ₁ hφ₂]
  simp only [Complex.conj_ofReal]

/-- The variance `Var(A)_ψ = ‖(A - ⟨A⟩)ψ‖²`. -/
noncomputable def variance (A : SymmetricOperator H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  ‖A.shiftedApply ψ ψ h_norm hψ hψ‖^2

/-- The standard deviation `σ_A = √Var(A)`. -/
noncomputable def stdDev (A : SymmetricOperator H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) : ℝ :=
  Real.sqrt (A.variance ψ h_norm hψ)

/-- Variance is nonnegative. -/
lemma variance_nonneg (A : SymmetricOperator H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) :
    0 ≤ A.variance ψ h_norm hψ :=
  sq_nonneg _

/-- Standard deviation is nonnegative. (Currently unused.) -/
lemma stdDev_nonneg (A : SymmetricOperator H) (ψ : H)
    (h_norm : ‖ψ‖ = 1) (hψ : ψ ∈ A.domain) :
    0 ≤ A.stdDev ψ h_norm hψ :=
  Real.sqrt_nonneg _

end SymmetricOperator

open SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Domain conditions for `[A,B]ψ` together with normalization `‖ψ‖ = 1`. -/
structure ShiftedDomainConditions (A B : SymmetricOperator H) (ψ : H) extends
    DomainConditions A B ψ where
  h_norm : ‖ψ‖ = 1

namespace ShiftedDomainConditions

variable {A B : SymmetricOperator H} {ψ : H}

/-- The shifted operator `(A - ⟨A⟩)ψ`. -/
noncomputable def A'ψ (h : ShiftedDomainConditions A B ψ) : H :=
  A.shiftedApply ψ ψ h.h_norm h.hψ_A h.hψ_A

/-- The shifted operator `(B - ⟨B⟩)ψ`. -/
noncomputable def B'ψ (h : ShiftedDomainConditions A B ψ) : H :=
  B.shiftedApply ψ ψ h.h_norm h.hψ_B h.hψ_B

/-- `(B - ⟨B⟩)ψ ∈ Dom(A)`. -/
lemma B'ψ_in_A_domain (h : ShiftedDomainConditions A B ψ) : h.B'ψ ∈ A.domain := by
  unfold B'ψ shiftedApply
  exact A.domain.sub_mem h.hBψ_A (A.domain.smul_mem _ h.hψ_A)

/-- `(A - ⟨A⟩)ψ ∈ Dom(B)`. -/
lemma A'ψ_in_B_domain (h : ShiftedDomainConditions A B ψ) : h.A'ψ ∈ B.domain := by
  unfold A'ψ shiftedApply
  exact B.domain.sub_mem h.hAψ_B (B.domain.smul_mem _ h.hψ_B)

end ShiftedDomainConditions
end Spectra.Operator

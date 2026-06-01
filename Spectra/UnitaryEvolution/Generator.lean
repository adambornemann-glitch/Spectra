/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvo/Generator.lean
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Complete
/-
# Infinitesimal Generators of One-Parameter Unitary Groups

This file develops the theory of strongly continuous one-parameter unitary groups
on complex Hilbert spaces and their infinitesimal generators.

## Main definitions

* `OneParameterUnitaryGroup`: A family `U : ℝ → (H →L[ℂ] H)` satisfying unitarity,
  the group law `U(s+t) = U(s) ∘ U(t)`, and strong continuity.
* `Generator`: The infinitesimal generator of a one-parameter unitary group, defined
  as the (generally unbounded) operator `A` satisfying `Aψ = lim_{t→0} (U(t)ψ - ψ)/(it)`
  on its natural domain.
* `Generator.IsSelfAdjoint`: Self-adjointness of a generator, characterized by
  surjectivity of `A ± iI` (equivalently, vanishing deficiency indices).

## Main statements

* `inverse_eq_adjoint`: For a one-parameter unitary group, `U(-t) = U(t)*`.
* `norm_preserving`: Unitary evolution preserves norms: `‖U(t)ψ‖ = ‖ψ‖`.
* `norm_one`: The operator norm satisfies `‖U(t)‖ = 1`.
* `selfAdjoint_generators_domain_eq`: Self-adjoint generators of the same unitary
  group have equal domains.
* `generator_op_eq_on_domain`: Generators of the same group agree on common domain elements.

## Physics interpretation

In quantum mechanics, `U(t) = exp(-itH/ℏ)` describes time evolution under a
Hamiltonian `H`. The generator `A = H/ℏ` is the observable corresponding to
energy (up to scaling). Self-adjointness of the generator is equivalent to
unitarity of time evolution, reflecting conservation of probability.

## Implementation notes

* Generators are necessarily unbounded operators for nontrivial time evolution,
  hence we work with a dense `Submodule ℂ H` as the domain rather than defining
  a total operator.
* The domain is characterized as maximal: `ψ ∈ domain` iff the defining limit exists.
* We use `𝓝[≠] 0` (punctured neighborhood) for the generator limit to avoid
  division by zero at `t = 0`.
* Self-adjointness uses the criterion `ran(A ± iI) = H` rather than equality of
  operator and adjoint, which is better suited to unbounded operators.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reed1980]
* [Hall, *Quantum Theory for Mathematicians*][hall2013]
* Stone's theorem: a one-parameter unitary group has a unique self-adjoint generator,
  and conversely every self-adjoint operator generates a unique one-parameter unitary group.
-/
namespace QuantumMechanics.Generators

open InnerProductSpace MeasureTheory Complex Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure OneParameterUnitaryGroup [CompleteSpace H] where
  U : ℝ → (H →L[ℂ] H)
  unitary : ∀ (t : ℝ) (ψ φ : H), ⟪U t ψ, U t φ⟫_ℂ = ⟪ψ, φ⟫_ℂ
  group_law : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  identity : U 0 = ContinuousLinearMap.id ℂ H
  strong_continuous : ∀ ψ : H, Continuous (fun t : ℝ => U t ψ)

lemma inverse_eq_adjoint [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    U_grp.U (-t) = (U_grp.U t).adjoint := by
  have h_inv : ∀ x : H, U_grp.U t (U_grp.U (-t) x) = x := fun x => by
    have h := U_grp.group_law t (-t)
    rw [show t + (-t) = 0 by ring, U_grp.identity] at h
    simpa using DFunLike.congr_fun h.symm x
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← U_grp.unitary t (U_grp.U (-t) x) y, h_inv x]


lemma norm_preserving [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) (ψ : H) :
    ‖U_grp.U t ψ‖ = ‖ψ‖ :=
  (LinearMap.norm_map_iff_inner_map_map (U_grp.U t)).mpr (U_grp.unitary t) ψ

lemma norm_one [Nontrivial H] [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H)) (t : ℝ) :
    ‖U_grp.U t‖ = 1 := by
  refine le_antisymm ?_ ?_
  · -- U t is norm-preserving ⇒ ‖U t‖ ≤ 1
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => le_of_eq ?_
    rw [norm_preserving, one_mul]
  · -- evaluate at any nonzero vector ⇒ 1 ≤ ‖U t‖
    obtain ⟨ψ, hψ⟩ := exists_ne (0 : H)
    have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
    have hle := (U_grp.U t).le_opNorm ψ
    rw [norm_preserving] at hle
    nlinarith [hle, hpos]

structure Generator [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H)) where
  domain : Submodule ℂ H
  op : domain →ₗ[ℂ] H
  dense_domain : Dense (domain : Set H)
  generator_formula : ∀ (ψ : domain),
    Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t (ψ : H) - (ψ : H)))
          (𝓝[≠] 0)
          (𝓝 (op ψ))
  domain_invariant : ∀ (t : ℝ) (ψ : H), ψ ∈ domain → U_grp.U t ψ ∈ domain
  symmetric : ∀ (ψ φ : domain), ⟪op ψ, (φ : H)⟫_ℂ = ⟪(ψ : H), op φ⟫_ℂ
  domain_maximal : ∀ ψ : H, (∃ η : H,
    Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ)) (𝓝[≠] 0) (𝓝 η)) → ψ ∈ domain


def Generator.IsSelfAdjoint [CompleteSpace H]
  {U_grp : OneParameterUnitaryGroup (H := H)}
    (gen : Generator U_grp) : Prop :=
  (∀ φ : H, ∃ (ψ : H) (hψ : ψ ∈ gen.domain),
    gen.op ⟨ψ, hψ⟩ + (I : ℂ) • ψ = φ) ∧
  (∀ φ : H, ∃ (ψ : H) (hψ : ψ ∈ gen.domain),
    gen.op ⟨ψ, hψ⟩ - (I : ℂ) • ψ = φ)


lemma generator_domain_char [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp) (ψ : H) :
    ψ ∈ gen.domain ↔
    ∃ (η : H), Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ))
                       (𝓝[≠] 0) (𝓝 η) := by
  constructor
  · intro hψ
    exact ⟨gen.op ⟨ψ, hψ⟩, gen.generator_formula ⟨ψ, hψ⟩⟩
  · intro ⟨η, hη⟩
    exact gen.domain_maximal ψ ⟨η, hη⟩


lemma selfAdjoint_domain_maximal [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H))
    (gen : Generator U_grp) (_hsa : gen.IsSelfAdjoint) (ψ : H)
    (η : H) (hη : Tendsto (fun t : ℝ => ((I : ℂ) * (t : ℂ))⁻¹ • (U_grp.U t ψ - ψ))
                          (𝓝[≠] 0) (𝓝 η)) :
    ψ ∈ gen.domain := gen.domain_maximal ψ ⟨η, hη⟩


lemma selfAdjoint_generators_domain_eq [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (hsa₁ : gen₁.IsSelfAdjoint) (hsa₂ : gen₂.IsSelfAdjoint) :
    gen₁.domain = gen₂.domain := by
  ext ψ
  constructor
  · intro hψ₁
    have h_lim := gen₁.generator_formula (⟨ψ, hψ₁⟩ : gen₁.domain)
    exact selfAdjoint_domain_maximal U_grp gen₂ hsa₂ ψ (gen₁.op (⟨ψ, hψ₁⟩ : gen₁.domain)) h_lim
  · intro hψ₂
    have h_lim := gen₂.generator_formula (⟨ψ, hψ₂⟩ : gen₂.domain)
    exact selfAdjoint_domain_maximal U_grp gen₁ hsa₁ ψ (gen₂.op (⟨ψ, hψ₂⟩ : gen₂.domain)) h_lim


lemma generator_op_eq_on_domain [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp) (ψ : H)
    (hψ₁ : ψ ∈ gen₁.domain) (hψ₂ : ψ ∈ gen₂.domain) :
    gen₁.op (⟨ψ, hψ₁⟩ : gen₁.domain) = gen₂.op (⟨ψ, hψ₂⟩ : gen₂.domain) := by
  have h₁ := gen₁.generator_formula (⟨ψ, hψ₁⟩ : gen₁.domain)
  have h₂ := gen₂.generator_formula (⟨ψ, hψ₂⟩ : gen₂.domain)
  exact tendsto_nhds_unique h₁ h₂


lemma LinearMap.heq_of_eq_domain {R M N : Type*}
  [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {D₁ D₂ : Submodule R M}
    (h_dom : D₁ = D₂) (f : D₁ →ₗ[R] N) (g : D₂ →ₗ[R] N)
    (h_eq : ∀ (x : M) (hx₁ : x ∈ D₁) (hx₂ : x ∈ D₂), f ⟨x, hx₁⟩ = g ⟨x, hx₂⟩) :
    HEq f g := by
  subst h_dom
  exact heq_of_eq (LinearMap.ext fun ⟨x, hx⟩ => h_eq x hx hx)


lemma generator_op_ext_of_eq_on_domain [CompleteSpace H]
  (U_grp : OneParameterUnitaryGroup (H := H))
    (gen₁ gen₂ : Generator U_grp)
    (h_dom : gen₁.domain = gen₂.domain)
    (h_eq : ∀ (ψ : H) (hψ₁ : ψ ∈ gen₁.domain) (hψ₂ : ψ ∈ gen₂.domain),
            gen₁.op ⟨ψ, hψ₁⟩ = gen₂.op ⟨ψ, hψ₂⟩) :
    HEq gen₁.op gen₂.op :=
  LinearMap.heq_of_eq_domain h_dom gen₁.op gen₂.op h_eq


end QuantumMechanics.Generators

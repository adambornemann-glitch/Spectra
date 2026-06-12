/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CrossedProducts/TypeII.lean
-/
import Spectra.CrossedProducts.DualWeight

/-!
# Type II Classification of the Modular Crossed Product

This file states the punchline of the entire crossed product project: when
`α = σ^φ` is the modular automorphism group of a faithful normal weight `φ`
on a Type III factor `M`, the crossed product `M ⋊_{σ^φ} ℝ` is a **Type II_∞
factor**.

## The Theorem

For `M` a properly infinite von Neumann algebra and `φ` a faithful normal
semifinite weight, the dual weight `φ̂` on `M ⋊_{σ^φ} ℝ` is a faithful normal
semifinite trace (Takesaki, 1970 — bundled as `TakesakiTrace` in
`DualWeight.lean`). The existence of such a trace is precisely the condition
that the crossed product is **semifinite**. Combined with the absence of
minimal projections (which follows from the same data, although we bundle
it), the crossed product is **Type II_∞**.

The original `M`, by contrast, has no faithful normal semifinite trace at
all — that is what "Type III" means. The crossed product manufactures a
trace by adjoining the modular flow as inner automorphisms; the trace
emerges because what was once "outer" (and untraceable) is now "inner"
(and traceable).

## Why This Matters

Type III algebras have no trace, and therefore no formula `S = -Tr(ρ log ρ)`.
Type II algebras have a faithful normal semifinite trace. So:

      `M ⋊_{σ^φ} ℝ`  carries a well-defined entropy,
      up to an additive constant (because the trace is only semifinite).

In quantum gravity, the gravitational constraints force the crossed product,
and the additive constant becomes the area term:

      `S_gen = A / (4 G_N)  +  S_out`.

This is the operator-algebraic origin of the Bekenstein–Hawking entropy.

## Type II_∞ vs. Type II_1

* **Type II_∞** is what we get from the basic crossed product of a Type III
  factor by its modular flow. The trace is faithful, normal, *semifinite*
  but not finite — there is no canonical normalization. This is the
  AdS/CFT setup (Witten, 2021).

* **Type II_1** appears when an additional constraint is imposed: the
  observer's clock is identified with the modular generator, projecting
  the II_∞ algebra down to one with a *finite* normalized trace. This is
  the de Sitter case (Chandrasekaran–Longo–Penington–Witten, 2022).

This file establishes only the II_∞ case. The II_1 case requires constructing
an "observer's algebra" with an additional Hamiltonian constraint, which is
a separate enterprise.

## Design

* `HasSemifiniteTrace` — the property of admitting a faithful normal
  semifinite trace. This is the dividing line between Type II / I and
  Type III.

* `NoMinimalProjections`, `ProperlyInfinite` — bundled hypotheses on the
  crossed product, ultimately derived from `M` being Type III but not
  reproved here.

* `IsTypeII_inf` — the combination of these properties characterizing a
  Type II_∞ factor.

* `crossedProduct_isTypeII_inf` — the **main theorem**: given the bundled
  inputs from `DualWeight.lean`, the modular crossed product is Type II_∞.

## References

* M. Takesaki, *Tomita's Theory of Modular Hilbert Algebras*, Springer (1970).
* A. Connes, *Une classification des facteurs de type III*,
  Ann. Sci. ENS 6 (1973), 133–252.
* E. Witten, *Gravity and the Crossed Product*, JHEP 10 (2022) 008.
* V. Chandrasekaran, R. Longo, G. Penington, E. Witten,
  *An algebra of observables for de Sitter space*, JHEP 02 (2023) 082.

## Tags

Type II factor, semifinite trace, Murray–von Neumann classification,
generalized entropy
-/
open Complex ContinuousLinearMap ENNReal NNReal
open Spectra.QuantumMechanics.ModularTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.CrossedProduct
variable {M : VNAlgebraWithVector H} {α : RDynamics M}

/-! ## Section 1: Semifiniteness

A von Neumann algebra is **semifinite** if it admits a faithful normal
semifinite trace. This is exactly the dividing line of the Murray–von Neumann
classification: Type I and II are semifinite; Type III is not.

For the crossed product, semifiniteness is provided by `TakesakiTrace`:
the dual weight is a trace.
-/

/-- The crossed product is **semifinite**: there exists a faithful normal
    semifinite trace on it.

    Concretely, this is witnessed by a `CrossedWeight` that satisfies the
    `IsTrace` property. The dual weight construction in `DualWeight.lean`
    provides exactly this in the modular case. -/
structure HasSemifiniteTrace {α : RDynamics M} (R : CovariantRep α) where
  /-- The trace as a `CrossedWeight`. -/
  trace : CrossedWeight R
  /-- The cyclic property. -/
  isTrace : trace.IsTrace

/-- The semifinite trace on the crossed product, packaged from `DualWeightData`
    and `TakesakiTrace`. This is the constructor showing that the modular
    crossed product is semifinite. -/
def HasSemifiniteTrace.ofTakesakiTrace
    {α : RDynamics M} {R : CovariantRep α} {D : DualActionData R}
    {φ : Weight M} (W : DualWeightData R D φ)
    {md : ModularData H M}
    {hTT : TomitaTheorem H M md}
    {hα : ∀ t a, α.α t a = modularAutomorphism md t a}
    (hTakesaki : TakesakiTrace R D φ W md hTT hα) :
    HasSemifiniteTrace R where
  trace := W.dualWeight
  isTrace := hTakesaki.isTrace

/-! ## Section 2: Murray–von Neumann Type Properties

The remaining defining features of a Type II_∞ factor: no minimal projections
(diffuseness) and proper infiniteness (no finite identity).

Both follow from `M` being a Type III factor, but proving this in Lean from
first principles would require substantial additional machinery (the theory
of projections, the comparison theorem). We bundle them as hypotheses on the
crossed product. The user supplies them; the architecture allows them to be
discharged later when projection theory is built out.
-/

/-- The crossed product has **no minimal projections**.

    A minimal projection is a nonzero projection `p` such that `p · A · p`
    is one-dimensional. For a factor, having no minimal projections is
    equivalent to being **diffuse**.

    For the crossed product `M ⋊_{σ^φ} ℝ` with `M` Type III, this property
    follows from the fact that the translations `U(t)` "spread out" any
    putative minimal projection — but the proof requires projection theory
    we have not built out. -/
structure NoMinimalProjections {α : RDynamics M} (R : CovariantRep α) where
  /-- For every nonzero projection `p` in the crossed product, there exists
      a strictly smaller nonzero subprojection. -/
  no_minimal : ∀ p : CrossedSpace H →L[ℂ] CrossedSpace H,
    p ∈ crossedProduct α R → p ≠ 0 →
    star p = p → p * p = p →
    ∃ q : CrossedSpace H →L[ℂ] CrossedSpace H,
      q ∈ crossedProduct α R ∧ q ≠ 0 ∧ q ≠ p ∧
      star q = q ∧ q * q = q ∧ q * p = q

/-- The crossed product is **properly infinite**.

    Equivalently: the identity is the supremum of an infinite orthogonal
    family of projections, each equivalent to 1. For `M ⋊_{σ^φ} ℝ` with `M`
    Type III, this is automatic — Type III factors are themselves properly
    infinite, and crossed products preserve this. We bundle. -/
structure ProperlyInfinite {α : RDynamics M} (R : CovariantRep α) where
  /-- The identity element is "infinite": there exists a proper projection
      `p ≠ 1` in the crossed product equivalent to `1`.

      Stated abstractly to avoid committing to a specific notion of
      "equivalent". A concrete formulation would invoke the Murray–von
      Neumann equivalence relation `p ~ q` (existence of a partial isometry
      `v` with `v* v = p`, `v v* = q`). -/
  exists_proper_equiv_unit :
    ∃ (p : CrossedSpace H →L[ℂ] CrossedSpace H) (v : CrossedSpace H →L[ℂ] CrossedSpace H),
      p ∈ crossedProduct α R ∧ v ∈ crossedProduct α R ∧
      star p = p ∧ p * p = p ∧ p ≠ 1 ∧
      adjoint v * v = p ∧ v * adjoint v = 1

/-! ## Section 3: Type II_∞

A factor is **Type II_∞** if it is semifinite, has no minimal projections,
and is properly infinite. We bundle these conditions.
-/

/-- A factor is **Type II_∞** if it is semifinite, has no minimal
    projections, and is properly infinite.

    For the crossed product `M ⋊_{σ^φ} ℝ` with `M` of Type III, all three
    conditions hold: semifiniteness from the dual weight (Takesaki), no
    minimal projections from `M` being diffuse, and proper infiniteness
    from `M` being properly infinite (which Type III factors automatically
    are). -/
structure IsTypeII_inf {α : RDynamics M} (R : CovariantRep α) where
  /-- Semifinite: admits a faithful normal semifinite trace. -/
  semifinite : HasSemifiniteTrace R
  /-- No minimal projections (diffuseness). -/
  diffuse : NoMinimalProjections R
  /-- Properly infinite (no finite identity). -/
  properlyInfinite : ProperlyInfinite R

/-! ## Section 4: The Main Theorem

The classification: given all the bundled inputs (Takesaki's trace theorem,
no minimal projections, proper infiniteness), the modular crossed product is
Type II_∞.

This is a "packaging" theorem — every nontrivial input is bundled — but it
is exactly the right packaging. Each ingredient has a clear mathematical
status: which results are proven (the trace property is a theorem of
Takesaki), and which are assumptions on `M` (proper infiniteness).
-/

/-- **The main classification theorem.**

    Given:
    * The dual weight data `W` on `M ⋊_{σ^φ} ℝ`,
    * Takesaki's trace theorem `hTakesaki`,
    * The crossed product has no minimal projections (`hNoMin`),
    * The crossed product is properly infinite (`hProp`),

    the crossed product is **Type II_∞**.

    The first ingredient is the substantive analytic theorem (Takesaki,
    1970). The remaining two are properties of the input algebra `M`
    propagated through the crossed product construction; they reflect that
    `M` is Type III, and as such has no minimal projections and is properly
    infinite.

    With this theorem in hand, the crossed product carries a well-defined
    entropy `S = -Tr_{φ̂}(ρ log ρ)`, up to an additive constant. -/
def crossedProduct_isTypeII_inf
    {R : CovariantRep α} {D : DualActionData R}
    {φ : Weight M} (W : DualWeightData R D φ)
    {md : ModularData H M}
    {hTT : TomitaTheorem H M md}
    {hα : ∀ t a, α.α t a = modularAutomorphism md t a}
    (hTakesaki : TakesakiTrace R D φ W md hTT hα)
    (hNoMin : NoMinimalProjections R)
    (hProp : ProperlyInfinite R) :
    IsTypeII_inf R :=
  ⟨HasSemifiniteTrace.ofTakesakiTrace W hTakesaki, hNoMin, hProp⟩


/-! ## Section 5: The Entropy Functional

A brief signpost. Once the crossed product is Type II_∞, the semifinite
trace `φ̂` allows the definition of an entropy functional on density-matrix-
like elements:

      `S(ρ) := -φ̂(ρ · log(ρ))`,

well-defined up to an additive constant (the additive constant comes from
the lack of a canonical normalization for a *semi*finite trace, in contrast
to the finite case where one fixes `Tr(1) = 1`).

We do not define `log` of a positive operator here — that is spectral
calculus and lives in the functional calculus modules. This section exists
to mark the entry point: once you reach this point, entropy makes sense.

In gravitational settings, the additive constant is fixed by the area term:

      `S_gen(ρ) = A / (4 G_N)  +  S_out(ρ)`,

where `S_out` is the von Neumann entropy of the exterior matter (the part
of the state captured by `ρ`), and `A / (4 G_N)` is the leading semiclassical
contribution from the horizon area.
-/

/-- The signature that an entropy functional on the crossed product would
    have. We do not provide a definition; this is a placeholder for the
    spectral-calculus development that would supply `log`.

    A concrete entropy functional `S : (CrossedSpace H →L[ℂ] CrossedSpace H) → ℝ`
    would satisfy:
    * `S(ρ) = -φ̂(ρ · log ρ)` on positive elements of the trace ideal.
    * Invariance under unitary conjugation by elements of `M ⋊_α ℝ`.
    * Subadditivity for direct sums.
    * Concavity (Wehrl, Lieb–Ruskai, etc.).

    These are the standard properties one would want from von Neumann
    entropy on a semifinite factor. We do not formalize them here. -/
structure EntropyFunctional
    {α : RDynamics M} {R : CovariantRep α} (T : IsTypeII_inf R) where
  /-- The entropy. Codomain is `ℝ ∪ {±∞}` in general; we use `ℝ` as a
      placeholder. -/
  S : (CrossedSpace H →L[ℂ] CrossedSpace H) → ℝ
  /-- The defining relation `S(ρ) = -φ̂(ρ log ρ)` is left abstract here. -/
  defining_relation : True

end Spectra.CrossedProduct

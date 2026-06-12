/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CrossedProducts/TakesakiDuality.lean
-/
import Spectra.CrossedProducts.DualWeight

/-!
# Takesaki Duality

This file states the two principal theorems of Takesaki duality for the
crossed product `M ⋊_α ℝ`:

1. **The Fixed-Point Theorem**: The fixed-point algebra of the dual action
   `α̂` on `M ⋊_α ℝ` is precisely the image of `M` under the diagonal
   representation:
        `Fix(α̂) = π(M)`.

2. **The Bidual Isomorphism**: The iterated crossed product, taking `M ⋊_α ℝ`
   and crossed-producting again by the dual action `α̂`, reproduces `M` up to
   tensoring with a Type I factor:
        `(M ⋊_α ℝ) ⋊_{α̂} ℝ̂ ≅ M ⊗ B(L²(ℝ))`.

These are the operator-algebraic analogues of Pontryagin duality for locally
compact abelian groups. The proof in the original setting [Takesaki 1973]
proceeds via Fourier analysis on `ℝ`, identifying the dual action with the
Fourier transform of the original action.

## Why This Matters

The fixed-point theorem expresses that the crossed product *remembers* `M` —
the original algebra is recoverable as the part of `M ⋊_α ℝ` that is
invisible to the dual action. The easy direction (`π(M) ⊆ Fix(α̂)`) is
immediate from the fact that `V(s)` commutes with `π(a)` (proved in
`DualAction.lean`). The hard direction (`Fix(α̂) ⊆ π(M)`) is the analytic
theorem: it says that any operator on `L²(ℝ, H)` commuting with all the
character multiplications `V(s)` must in fact act pointwise — i.e., be of
the form `π(a)`. This is a Plancherel-style statement.

The bidual isomorphism encodes the Pontryagin self-duality of `ℝ`. Its
operational use is to establish that taking a crossed product is, up to
stabilization, an involution. Combined with the trace theorem from
`DualWeight.lean`, it explains structurally why `III × σ → II_∞`:
the modular automorphism is "absorbed" into the inner automorphisms by
the crossed product, and the bidual reveals the trace.

## Physics

In holographic duality and de Sitter quantum gravity, Takesaki duality is
the algebraic statement that an observer's algebra is recoverable from the
crossed product by their modular Hamiltonian. The dual action measures the
observer's energy; the fixed-point algebra is the part of physics invariant
under energy shifts of the observer. This is `M`.

See: V. Chandrasekaran, R. Longo, G. Penington, E. Witten,
"An algebra of observables for de Sitter space", JHEP 02 (2023) 082, §3–4.

## Design

* `FixedPoint` — the fixed-point algebra of the dual action.
* `FixedPointTheorem` — the bundled theorem `Fix(α̂) = π(M)`.
* `TakesakiBidual` — the bundled bidual isomorphism (very abstract; no
  explicit construction is attempted).

The fixed-point theorem has a clean algebraic statement; we use it directly.
The bidual is stated for structural completeness but is not used downstream.

## References

* M. Takesaki, *Duality for crossed products and the structure of von Neumann
  algebras of type III*, Acta Math. 131 (1973), 249–310.
* M. Takesaki, *Theory of Operator Algebras II*, Ch. X.
* A. Connes, *Noncommutative Geometry*, App. V.B.

## Tags

Takesaki duality, fixed-point algebra, Plancherel, Pontryagin duality, bidual
-/
open Complex ContinuousLinearMap ENNReal NNReal
open Spectra.QuantumMechanics.ModularTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.CrossedProduct
variable {M : VNAlgebraWithVector H} {α : RDynamics M}

/-! ## Section 1: The Fixed-Point Algebra

The set of elements of `M ⋊_α ℝ` left invariant by the dual action `α̂`.
By the easy direction of Takesaki duality (proved in `DualAction.lean`),
this contains `π(M)`. By the hard direction (bundled below), this *equals*
`π(M)`.
-/

/-- The fixed-point set of the dual action: elements `x ∈ M ⋊_α ℝ` with
    `α̂_s(x) = x` for all `s ∈ ℝ`. -/
def FixedPoint {R : CovariantRep α} (D : DualActionData R) :
    Set (CrossedSpace H →L[ℂ] CrossedSpace H) :=
  { x | x ∈ crossedProduct α R ∧ ∀ s : ℝ, D.act s x = x }

/-- The image of `M` under `π` lies in the fixed-point algebra. This is the
    easy direction, immediate from `dualAction_fixes_diag`. -/
lemma diag_image_subset_FixedPoint {R : CovariantRep α} (D : DualActionData R)
    {a : H →L[ℂ] H} (ha : a ∈ M.algebra) :
    R.diag.π a ∈ FixedPoint D := by
  refine ⟨diag_mem_crossedProduct α R ha, ?_⟩
  intro s
  exact dualAction_fixes_diag R D.unitary D.implements s ha

/-! ## Section 2: The Fixed-Point Theorem

The hard direction. Every element of the fixed-point algebra is of the form
`π(a)` for some `a ∈ M`.

The proof requires showing that an operator on `L²(ℝ, H)` commuting with all
the multiplication operators `V(s)` must act "diagonally" — i.e., as a
multiplication operator by an operator-valued function `s ↦ α_{-s}(a)`. This
is the operator-algebraic Plancherel theorem; we bundle it.
-/

/-- **The Fixed-Point Theorem.**

    Every element of `M ⋊_α ℝ` fixed by every `α̂_s` is of the form `π(a)`
    for some `a ∈ M`. Equivalently, `Fix(α̂) ⊆ π(M.algebra)`.

    Combined with the easy direction (`diag_image_subset_FixedPoint`), this
    gives `Fix(α̂) = π(M)`.

    The proof is the Plancherel-style argument: a bounded operator on
    `L²(ℝ, H)` commuting with multiplication by every character `e^{is·}`
    is a multiplication operator. We bundle this as data. -/
structure FixedPointTheorem {R : CovariantRep α} (D : DualActionData R) where
  /-- For every fixed point `x`, there exists `a ∈ M` with `x = π(a)`. -/
  recover : ∀ x ∈ FixedPoint D,
    ∃ a : H →L[ℂ] H, a ∈ M.algebra ∧ x = R.diag.π a

/-! ## Section 3: The Two Halves Combined

The clean theorem statement. Given the bundled hard direction, we obtain the
full identification of the fixed-point algebra. -/

/-- **Takesaki's fixed-point identification.** Given the bundled hard direction
    `FixedPointTheorem`, the fixed-point algebra of `α̂` is exactly the image
    of `M.algebra` under `π`:

        `x ∈ Fix(α̂)  ↔  ∃ a ∈ M.algebra, x = π(a)`. -/
theorem FixedPoint_eq_diag_image {R : CovariantRep α} (D : DualActionData R)
    (hT : FixedPointTheorem D)
    (x : CrossedSpace H →L[ℂ] CrossedSpace H) :
    x ∈ FixedPoint D ↔ ∃ a : H →L[ℂ] H, a ∈ M.algebra ∧ x = R.diag.π a := by
  constructor
  · intro hx
    exact hT.recover x hx
  · rintro ⟨a, ha, rfl⟩
    exact diag_image_subset_FixedPoint D ha

/-- An immediate corollary: the fixed-point algebra is closed under the
    von Neumann algebra operations, since it equals the image of an algebra
    under a *-homomorphism.

    (Stated as a sanity check rather than for downstream use.) -/
lemma FixedPoint_mul_mem {R : CovariantRep α} (D : DualActionData R)
    (hT : FixedPointTheorem D)
    {x y : CrossedSpace H →L[ℂ] CrossedSpace H}
    (hx : x ∈ FixedPoint D) (hy : y ∈ FixedPoint D) :
    x * y ∈ FixedPoint D := by
  obtain ⟨a, ha, rfl⟩ := (FixedPoint_eq_diag_image D hT x).mp hx
  obtain ⟨b, hb, rfl⟩ := (FixedPoint_eq_diag_image D hT y).mp hy
  refine ⟨?_, ?_⟩
  · -- π(a) · π(b) ∈ crossedProduct: products of generators stay in the algebra
    have hab : R.diag.π a * R.diag.π b = R.diag.π (a * b) :=
      (R.diag.map_mul a b ha hb).symm
    rw [hab]
    exact diag_mem_crossedProduct α R (M.algebra.mul_mem ha hb)
  · intro s
    -- α̂_s fixes π(a) and π(b), hence fixes their product (multiplicativity)
    have hab : R.diag.π a * R.diag.π b = R.diag.π (a * b) :=
      (R.diag.map_mul a b ha hb).symm
    rw [hab]
    exact dualAction_fixes_diag R D.unitary D.implements s
      (M.algebra.mul_mem ha hb)

/-! ## Section 4: The Bidual Isomorphism

The structural form of Takesaki duality. We state it abstractly: there is a
*-isomorphism between the iterated crossed product `(M ⋊_α ℝ) ⋊_{α̂} ℝ̂` and
`M ⊗ B(L²(ℝ))`.

A proper Lean formulation requires:
* The bidual crossed product as a `StarSubalgebra` of operators on
  `L²(ℝ, L²(ℝ, H))`.
* The von Neumann tensor product `M ⊗ B(L²(ℝ))`.
* A *-isomorphism between them.

Each of these is substantial infrastructure. We bundle only the abstract
existence of the isomorphism, with no claim to use it operationally. The
purpose is to make explicit what would be needed to complete the formal
picture. -/

/-- **Takesaki Bidual Isomorphism**, stated abstractly.

    There exists a *-isomorphism

          `(M ⋊_α ℝ) ⋊_{α̂} ℝ̂ ≅ M ⊗ B(L²(ℝ))`,

    intertwining: the diagonal embedding of `M` on both sides; the action `α`
    on the left with `α ⊗ id` on the right; and the double dual action
    `α̂̂` on the left with `id ⊗ Ad(λ)` on the right.

    A full Lean statement requires the bidual crossed product, the von
    Neumann tensor product `M ⊗ B(L²(ℝ))`, and the construction of the
    isomorphism via the Fourier transform on `ℝ`. We bundle the conclusion
    as opaque data; the type signature documents what would be needed
    operationally. -/
structure TakesakiBidual {R : CovariantRep α} (D : DualActionData R) where
  /-- The data of the isomorphism is left opaque here. A future expansion
      would carry:
        * A type for the bidual algebra.
        * A type for `M ⊗ B(L²(ℝ))`.
        * A *-isomorphism between them.
        * Intertwining properties.
      For now this structure exists only to mark the place where the deep
      theorem belongs. -/
  exists_iso : True

/-! ## Section 5: Consequences

What Takesaki duality buys us, in compact form. -/

/- **The state-independence corollary.** If `α` is the modular automorphism
    group of a weight `φ`, then the outer class `[α_t] ∈ Out(M)` is intrinsic
    to `M` — it does not depend on the choice of `φ`.

    This is established (without using Takesaki duality) in your
    `Cocycle.lean` via the Connes cocycle. We state it here as the
    corollary it appears to be in the Takesaki picture: in the bidual,
    different choices of `φ` give isomorphic crossed products that differ
    only by an inner automorphism of `M ⊗ B(L²(ℝ))`. -/
-- The actual statement lives in Cocycle.lean as `modular_flow_state_independent`.
-- We do not duplicate it here; the comment marks its conceptual home.

/- **The trace existence corollary.** If `α = σ^φ` and the dual weight `ω`
    is a trace (Takesaki's trace theorem from `DualWeight.lean`), then the
    crossed product `M ⋊_{σ^φ} ℝ` carries a faithful normal semifinite
    trace, hence is **semifinite**.

    Combined with `M` being properly infinite (which is the case for any
    Type III factor), this gives that `M ⋊_{σ^φ} ℝ` is Type II_∞.

    The semifinite case is the content of `TypeII.lean`. -/
-- Statement to live in TypeII.lean.

end Spectra.CrossedProduct

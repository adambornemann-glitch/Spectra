/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CrossedProducts/DualAction.lean
-/
import Spectra.CrossedProducts.Definition

/-!
# The Dual Action on `M ⋊_α ℝ`

This file constructs the dual action `α̂ : ℝ → Aut(M ⋊_α ℝ)`. The `ℝ` in the
target plays the role of the Pontryagin dual `ℝ̂` of the original `ℝ` (time);
the two are canonically isomorphic via the pairing `⟨s, t⟩ = e^{i s t}`, so
we use the same Lean type for both. Conceptually: original `ℝ` = time, dual
`ℝ` = energy.

## The Construction

On `K = L²(ℝ, H)`, the **dual implementing unitary** is multiplication by a
character:
      `(V(s) ξ)(r) := e^{i s r} · ξ(r)`.

Two algebraic relations follow:

* **`V` commutes with `π(M)`**: since `π(a)` acts pointwise on `ξ(r)` (by
  the operator `α_{-r}(a)`), it commutes with multiplication by the scalar
  `e^{i s r}`. Hence `V(s) π(a) V(s)* = π(a)`.

* **`V` twists `U(t)`**: a direct calculation gives
        `V(s) U(t) V(s)* = e^{i s t} · U(t)`.
  Explicitly: `(V(s) U(t) V(s)* ξ)(r) = e^{i s r} · (V(s)* ξ)(r-t)`
            `                        = e^{i s r} · e^{-i s (r-t)} · ξ(r-t)`
            `                        = e^{i s t} · ξ(r-t)`
            `                        = e^{i s t} · (U(t) ξ)(r)`.

The **dual action** is then conjugation by `V(s)`:
      `α̂_s(x) := V(s) · x · V(s)*`,
and the two relations above show it preserves the crossed product
`M ⋊_α ℝ`, since it sends generators to generators (up to the scalar
factor `e^{i s t}`, which stays in the algebra).

## Key Properties

* `α̂` is a strongly continuous one-parameter group of *-automorphisms.
* `π(M) ⊆ Fix(α̂)`: every diagonal element is fixed.
* `Fix(α̂) = π(M)`: this is half of **Takesaki duality** and is deferred to
  `TakesakiDuality.lean`. It is the substantive content of the dual action.

## Physics

When `α = σ^φ`, the original `ℝ` is the time of the modular flow and the
dual `ℝ` is the energy conjugate to it. The dual action `α̂_s` is then a
shift in energy. In the next file we construct the dual weight by integrating
against the Boltzmann factor `e^{-s}` over the dual `ℝ`, and Takesaki's
theorem will tell us this dual weight is a *trace* — Type II is born.

## Design

* `DualUnitaryRep` — bundled data for the implementing unitary `V`.
* `DualImplements` — the algebraic compatibility with `(π, U)`.
* `dualAction` — the *-automorphism `α̂_s` as a function on `B(K)`.
* Algebraic lemmas: `dualAction_add`, `dualAction_zero`, `dualAction_mul`,
  `dualAction_star`.
* Action on generators: `dualAction_fixes_diag`, `dualAction_twist_trans`.
* `DualActionPreservesAlgebra` — the bundled statement that conjugation by
  `V(s)` restricts to a *-automorphism of `crossedProduct α R`.

## References

* M. Takesaki, *Theory of Operator Algebras II*, Ch. X, §2.
* A. Connes, *Noncommutative Geometry*, App. V.B.

## Tags

dual action, Pontryagin duality, energy shift, fixed-point algebra
-/
open MeasureTheory Complex ContinuousLinearMap
open Spectra.QuantumMechanics.ModularTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.CrossedProduct

/-! ## Section 1: The Dual Implementing Unitary `V(s)`

`V(s)` is multiplication on `L²(ℝ, H)` by the character `r ↦ e^{i s r}`.
Being multiplication by a unitary scalar, it is itself unitary; the group
law `V(s+t) = V(s) V(t)` is `e^{i(s+t)r} = e^{isr} e^{itr}`.

We bundle existence because constructing `V(s)` as a `ContinuousLinearMap`
on `Lp H 2 volume` requires the L∞-multiplier infrastructure (multiplication
of `Lp` by a bounded measurable scalar function). The algebraic identities
hold once existence is granted.
-/

/-- Bundled data for the dual implementing unitary `V : ℝ → U(K)`. -/
structure DualUnitaryRep (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The implementing unitary `V(s)`. -/
  V : ℝ → CrossedSpace H →L[ℂ] CrossedSpace H
  /-- Group homomorphism: `V(s + t) = V(s) · V(t)`. -/
  map_add : ∀ s t, V (s + t) = V s * V t
  /-- `V(0) = 1`. -/
  at_zero : V 0 = 1
  /-- Each `V(s)` is unitary. -/
  isUnitary : ∀ s, V s * adjoint (V s) = 1 ∧ adjoint (V s) * V s = 1
  /-- Strong continuity. -/
  strongly_continuous : ∀ ξ : CrossedSpace H, Continuous (fun s => V s ξ)

/-- The adjoint of `V(s)` is `V(-s)`. Identical argument to
    `TranslationRep.adjoint_eq`. -/
lemma DualUnitaryRep.adjoint_eq (V : DualUnitaryRep H) (s : ℝ) :
    adjoint (V.V s) = V.V (-s) := by
  have h_grp : V.V s * V.V (-s) = 1 := by
    rw [← V.map_add, add_neg_cancel, V.at_zero]
  have h_adj_left : adjoint (V.V s) * V.V s = 1 := (V.isUnitary s).2
  calc adjoint (V.V s)
      = adjoint (V.V s) * 1 := (mul_one _).symm
    _ = adjoint (V.V s) * (V.V s * V.V (-s)) := by rw [h_grp]
    _ = (adjoint (V.V s) * V.V s) * V.V (-s) := by rw [mul_assoc]
    _ = 1 * V.V (-s) := by rw [h_adj_left]
    _ = V.V (-s) := one_mul _

/-! ## Section 2: Compatibility with the Covariant Representation

The two defining relations of the dual action, packaged as a structure tying
the dual unitary `V` to the covariant representation `(π, U)`. The first says
`V` is invisible to the diagonal piece; the second says `V` twists each
translation by a character. Together they will imply that conjugation by `V`
preserves the crossed product.
-/

variable {M : VNAlgebraWithVector H} {α : RDynamics M}

/-- The compatibility data: `V` commutes with `π(M)` and twists `U(t)` by
    the character `e^{i s t}`. -/
structure DualImplements (R : CovariantRep α) (V : DualUnitaryRep H) where
  /-- `V(s) · π(a) = π(a) · V(s)` for `a ∈ M`. -/
  commute_diag : ∀ (s : ℝ) (a : H →L[ℂ] H), a ∈ M.algebra →
    V.V s * R.diag.π a = R.diag.π a * V.V s
  /-- `V(s) · U(t) · V(s)* = e^{i s t} · U(t)`. -/
  twist_trans : ∀ (s t : ℝ),
    V.V s * R.trans.U t * adjoint (V.V s) =
      (Complex.exp (s * t * Complex.I)) • R.trans.U t

/-! ## Section 3: The Dual Action `α̂_s` -/

/-- **The dual action** `α̂_s : B(K) → B(K)` defined as conjugation by `V(s)`.

    Defined globally on `B(K)`; its restriction to the crossed product is a
    *-automorphism, as established by `DualActionPreservesAlgebra`. -/
noncomputable def dualAction (V : DualUnitaryRep H) (s : ℝ) :
    (CrossedSpace H →L[ℂ] CrossedSpace H) →
    (CrossedSpace H →L[ℂ] CrossedSpace H) :=
  fun x => V.V s * x * adjoint (V.V s)

/-! ### Algebraic properties

These all follow from conjugation by a unitary being a *-automorphism of
`B(K)`. They hold globally — not just on the crossed product. -/

/-- `α̂_0 = id`. -/
lemma dualAction_zero (V : DualUnitaryRep H) (x : CrossedSpace H →L[ℂ] CrossedSpace H) :
    dualAction V 0 x = x := by
  simp only [dualAction]
  rw [V.adjoint_eq, neg_zero, V.at_zero]
  simp

/-- Group law: `α̂_{s+t} = α̂_s ∘ α̂_t`. -/
lemma dualAction_add (V : DualUnitaryRep H) (s t : ℝ)
    (x : CrossedSpace H →L[ℂ] CrossedSpace H) :
    dualAction V (s + t) x = dualAction V s (dualAction V t x) := by
  simp only [dualAction, V.map_add s t]
  have hadj : adjoint (V.V s * V.V t) = adjoint (V.V t) * adjoint (V.V s) := by
    change star (V.V s * V.V t) = star (V.V t) * star (V.V s)
    exact star_mul _ _
  rw [hadj]
  -- Both sides equal V(s) * V(t) * x * adjoint V(t) * adjoint V(s) by associativity.
  simp only [mul_assoc]

/-- Multiplicativity: `α̂_s(xy) = α̂_s(x) α̂_s(y)`. The key step is inserting
    `V(s)* V(s) = 1` between `x` and `y`. -/
lemma dualAction_mul (V : DualUnitaryRep H) (s : ℝ)
    (x y : CrossedSpace H →L[ℂ] CrossedSpace H) :
    dualAction V s (x * y) = dualAction V s x * dualAction V s y := by
  simp only [dualAction]
  have h_inv : adjoint (V.V s) * V.V s = 1 := (V.isUnitary s).2
  calc V.V s * (x * y) * adjoint (V.V s)
      = V.V s * x * y * adjoint (V.V s) := by rw [← mul_assoc, mul_assoc (V.V s)]
    _ = V.V s * x * (adjoint (V.V s) * V.V s) * y * adjoint (V.V s) := by rw [h_inv]; simp
    _ = (V.V s * x * adjoint (V.V s)) * (V.V s * y * adjoint (V.V s)) := by
        simp only [mul_assoc]

/-- *-preservation: `α̂_s(x*) = α̂_s(x)*`. -/
lemma dualAction_star (V : DualUnitaryRep H) (s : ℝ)
    (x : CrossedSpace H →L[ℂ] CrossedSpace H) :
    star (dualAction V s x) = dualAction V s (star x) := by
  -- star (V(s) · x · V(s)*) = (V(s)*)* · star(x) · V(s)* = V(s) · star(x) · V(s)*
  simp only [dualAction]
  change star (V.V s * x * star (V.V s)) = V.V s * star x * star (V.V s)
  rw [star_mul, star_mul, star_star, mul_assoc]

/-- `α̂_s(1) = 1`. -/
lemma dualAction_one (V : DualUnitaryRep H) (s : ℝ) :
    dualAction V s 1 = 1 := by
  simp only [dualAction, mul_one]
  exact (V.isUnitary s).1

/-! ## Section 4: Action on Generators

The two key calculations: `α̂` fixes `π(M)` and twists `U(t)`.
These are immediate from `DualImplements`. -/

/-- `α̂_s` fixes every diagonal element `π(a)` for `a ∈ M`. -/
lemma dualAction_fixes_diag (R : CovariantRep α) (V : DualUnitaryRep H)
    (D : DualImplements R V) (s : ℝ) {a : H →L[ℂ] H} (ha : a ∈ M.algebra) :
    dualAction V s (R.diag.π a) = R.diag.π a := by
  simp only [dualAction]
  rw [D.commute_diag s a ha]
  rw [mul_assoc, (V.isUnitary s).1, mul_one]

/-- `α̂_s(U(t)) = e^{i s t} · U(t)`. -/
lemma dualAction_twist_trans (R : CovariantRep α) (V : DualUnitaryRep H)
    (D : DualImplements R V) (s t : ℝ) :
    dualAction V s (R.trans.U t) = (Complex.exp (s * t * Complex.I)) • R.trans.U t :=
  D.twist_trans s t

/-! ## Section 5: Preservation of the Crossed Product

The two preceding lemmas show that `dualAction V s` sends each generator
of `M ⋊_α ℝ` back into the algebra. Since `dualAction` is also multiplicative,
*-preserving, and ℂ-linear, it preserves the *-subalgebra generated by those
generators — i.e., the crossed product.

Proving this preservation rigorously requires an induction over the
`StarAlgebra.adjoin` construction, which we bundle as `DualActionPreservesAlgebra`.
The proof is conceptually straightforward but uses the universal property of
star-algebra adjoin in a way Mathlib does not yet expose conveniently.
-/

/-- The dual action restricts to a self-map of the crossed product.

    Bundled as a hypothesis: a rigorous proof requires induction over the
    star-algebra adjoin, using `dualAction_fixes_diag`, `dualAction_twist_trans`,
    `dualAction_mul`, `dualAction_add` (linearity), and `dualAction_star`. -/
structure DualActionPreservesAlgebra
    (R : CovariantRep α) (V : DualUnitaryRep H) (D : DualImplements R V) where
  preserves : ∀ (s : ℝ) (x : CrossedSpace H →L[ℂ] CrossedSpace H),
    x ∈ crossedProduct α R → dualAction V s x ∈ crossedProduct α R

/-! ## Section 6: Bundling the Dual Action as a One-Parameter Group

The collection `{α̂_s}_{s ∈ ℝ}` forms a strongly continuous one-parameter group
of *-automorphisms of `M ⋊_α ℝ`. We bundle this for use by downstream files
(the dual weight, Takesaki duality, the Type II classification).
-/

/-- The full dual action data: implementing unitary, compatibility with the
    covariant representation, and preservation of the crossed product. The
    output is a strongly continuous one-parameter group of *-automorphisms
    of `crossedProduct α R`. -/
structure DualActionData (R : CovariantRep α) where
  /-- The implementing unitary. -/
  unitary : DualUnitaryRep H
  /-- Compatibility with `(π, U)`. -/
  implements : DualImplements R unitary
  /-- The dual action preserves the crossed product. -/
  preserves : DualActionPreservesAlgebra R unitary implements

/-- Convenience accessor: the dual action `α̂_s` as a self-map of `B(K)`. -/
noncomputable def DualActionData.act {R : CovariantRep α} (D : DualActionData R) (s : ℝ) :
    (CrossedSpace H →L[ℂ] CrossedSpace H) →
    (CrossedSpace H →L[ℂ] CrossedSpace H) :=
  dualAction D.unitary s

/-- The dual action restricted to the crossed product. -/
lemma DualActionData.act_mem {R : CovariantRep α} (D : DualActionData R) (s : ℝ)
    {x : CrossedSpace H →L[ℂ] CrossedSpace H} (hx : x ∈ crossedProduct α R) :
    D.act s x ∈ crossedProduct α R :=
  D.preserves.preserves s x hx

/-! ## Section 7: Fixed Points

The fixed-point algebra of `α̂` is the substantive content of Takesaki
duality. One direction — that `π(M)` is contained in the fixed points — is
trivial from `dualAction_fixes_diag`. The other direction — that the fixed
points are *exactly* `π(M)` — is deferred to `TakesakiDuality.lean`.
-/

/-- `π(M)` is contained in the fixed-point algebra of `α̂`. -/
theorem diag_subset_fixed {R : CovariantRep α} (D : DualActionData R)
    (s : ℝ) {a : H →L[ℂ] H} (ha : a ∈ M.algebra) :
    D.act s (R.diag.π a) = R.diag.π a :=
  dualAction_fixes_diag R D.unitary D.implements s ha

end Spectra.CrossedProduct

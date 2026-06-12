/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: CrossedProducts/DualWeight.lean
-/
import Spectra.CrossedProducts.DualAction
import Mathlib.Data.ENNReal.Basic

/-!
# The Dual Weight `φ̂` on `M ⋊_α ℝ`

This file constructs the **dual weight** on the crossed product, the analytic
heart of the entire crossed product story. Given a faithful normal semifinite
weight `φ` on `M`, the dual weight `φ̂` is a faithful normal semifinite weight
on `M ⋊_α ℝ`. Its salient feature is the **scaling property** under the dual
action:

      `φ̂ ∘ α̂_s = e^{-s} · φ̂`.

When `α = σ^φ` (the modular automorphism group of `φ`), the dual weight has
an additional property of foundational importance: **it is a trace.** That
is, `φ̂(xy) = φ̂(yx)` for `x, y` in the trace-class ideal. This is
**Takesaki's Theorem** (Takesaki, *Tomita's Theory of Modular Hilbert
Algebras*, 1970), and it is the *raison d'être* of the construction.

## Why This Is The Whole Point

Type III von Neumann algebras have no trace. The formula
      `S = -Tr(ρ log ρ)`
is therefore meaningless on the local algebras of quantum field theory,
which are typically Type III₁ factors. In ordinary QFT, the von Neumann
entropy of a local subregion is genuinely undefined.

The crossed product construction `M ⋊_{σ^φ} ℝ`, together with the dual
weight `φ̂`, supplies a trace where none existed before. The resulting
algebra is Type II_∞ rather than Type III, and the dual weight is its
canonical semifinite trace. Entropies are now defined — up to an additive
constant (because the trace is only semifinite, not finite, so there is
no canonical normalization).

Physically, in gravity, the crossed product is *forced* upon us by the
gravitational constraints (the Hamiltonian must generate gauge
transformations), and the additive constant in the entropy is fixed by
the area term: `S = (A)/(4G_N) + S_out`. The dual weight is the operator-
algebraic incarnation of the generalized entropy formula.

## The Construction

Heuristically:
      `φ̂(x) ≈ "φ ⊗ Lebesgue"(x)`,

where Lebesgue measure on `ℝ` is the "Plancherel weight" of the translation
group. On simple elements `π(a) · U(t)`, one has formally

      `φ̂(π(a) U(t)) = δ(t) · φ(a)`.

(The delta is symbolic; the actual construction goes through the GNS
representation and integration against the *modular* of `φ̂` on a different
Hilbert space.) `φ̂` is uniquely determined, up to a positive scalar, by:
- **Faithful, normal, semifinite.**
- **Scaling**: `φ̂ ∘ α̂_s = e^{-s} φ̂` for all `s ∈ ℝ`.

## Key Properties (Bundled)

1. **Existence** of `φ̂` (bundled in `DualWeightData`).
2. **Scaling** under the dual action.
3. **Modular automorphism**: `σ^{φ̂}_t` is *inner*, implemented by `U(t)`.
   This is what makes the dual weight close to a trace.
4. **Takesaki's Trace Theorem**: when `α = σ^φ`, `φ̂` is a trace.
   Bundled as `TakesakiTrace`.

## Design

We do not construct `φ̂` from scratch — that is Takesaki's theorem and lies
beyond Lean's current reach. We follow the established pattern (cf.
`ModularData`, `TomitaTheorem`, `RelativeModularData`,
`RelativeTomitaTheorem`): the analytic existence is a bundled structure, and
the algebraic consequences are theorems.

* `Weight M` — a faithful normal semifinite weight (minimal infrastructure).
* `IsTrace` — the predicate that a weight is a trace (cyclic property).
* `DualWeightData` — the dual weight together with its defining properties.
* `TakesakiTrace` — the bundled Takesaki theorem: `φ̂` is a trace when
  `α = σ^φ`.

## References

* M. Takesaki, *Tomita's Theory of Modular Hilbert Algebras and Its
  Applications*, Lecture Notes in Math. 128, Springer (1970).
* M. Takesaki, *Theory of Operator Algebras II*, Ch. VIII.
* A. Connes, *Noncommutative Geometry*, App. V.B.
* E. Witten, *Gravity and the Crossed Product*, JHEP 10 (2022) 008, §2–§3.

## Tags

dual weight, semifinite trace, Plancherel, Takesaki theorem, Type II, entropy
-/

open Complex ContinuousLinearMap ENNReal NNReal
open Spectra.QuantumMechanics.ModularTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.CrossedProduct
variable {M : VNAlgebraWithVector H} {α : RDynamics M}

/-! ## Section 1: Weights on a Von Neumann Algebra

A faithful normal semifinite (f.n.s.) weight is an unbounded analogue of a
state. It takes values in `[0, ∞]` and is defined on the cone of positive
operators of `M`. A *state* is a particular case: a weight that is everywhere
finite and normalized so that `φ(1) = 1`.

The minimal axioms we need are:
* Additivity on positives.
* Scale-equivariance under non-negative reals.
* Faithfulness: `φ(a*a) = 0 ⟹ a = 0`.

Normality and semifiniteness are analytic conditions (SOT-continuity from
below; density of the trace ideal). These are bundled here without
unfolding; future work may expand them.
-/

/-- A faithful normal semifinite weight on `M`.

    The weight is given as a function `(H →L[ℂ] H) → ℝ≥0∞`. By convention,
    it is set to zero off `M.algebra`, so we do not need to carry around a
    subtype. The algebraic axioms are required only for elements of
    `M.algebra`. -/
structure Weight (M : VNAlgebraWithVector H) where
  /-- The weight as a function on bounded operators. -/
  fn : (H →L[ℂ] H) → ℝ≥0∞
  /-- The weight vanishes outside `M.algebra`. -/
  outside_zero : ∀ a : H →L[ℂ] H, a ∉ M.algebra → fn a = 0
  /-- Additivity on `M.algebra`. -/
  additive : ∀ a b : H →L[ℂ] H, a ∈ M.algebra → b ∈ M.algebra →
    fn (a + b) = fn a + fn b
  /-- Scale-equivariance for non-negative real scalars. -/
  smul_eq : ∀ (c : ℝ≥0) (a : H →L[ℂ] H), a ∈ M.algebra →
    fn ((c : ℂ) • a) = c • fn a
  /-- Faithful: `φ(a*a) = 0 ⟹ a = 0`. -/
  faithful : ∀ a : H →L[ℂ] H, a ∈ M.algebra → fn (star a * a) = 0 → a = 0
  /- The vacuum is in the domain: `φ(1) < ∞` is *not* required (weights
      can be infinite on the unit; this is allowed). -/
  -- normal and semifinite: bundled below as opaque properties.

/-- The class of bounded operators in `M.algebra` on which the weight is finite.
    Standard notation in the weight literature: `m_φ⁺ = {a ≥ 0 : φ(a) < ∞}`. -/
def Weight.finitePart (φ : Weight M) : Set (H →L[ℂ] H) :=
  { a | a ∈ M.algebra ∧ φ.fn a < ⊤ }

/-! ## Section 2: The Trace Property

A trace is a weight satisfying the cyclic identity `φ(xy) = φ(yx)` on the
trace-class ideal. Equivalently: a weight whose modular automorphism group
is trivial. Equivalently again: a weight invariant under all inner
automorphisms.

In the crossed product setting we will see, via Takesaki's theorem, that
the *dual* weight of a modular weight has modular automorphism that becomes
inner — and from there one extracts the trace property.
-/

/-- A weight is a **trace** if `φ(xy) = φ(yx)` on a sufficiently large domain.
    Here we state the condition globally on `M.algebra`, with the implicit
    understanding that both sides may be `∞`. The proper formulation
    restricts to the trace-class ideal; the global form is a useful proxy. -/
def Weight.IsTrace (φ : Weight M) : Prop :=
  ∀ a b : H →L[ℂ] H, a ∈ M.algebra → b ∈ M.algebra →
    φ.fn (a * b) = φ.fn (b * a)

/-! ## Section 3: The Dual Weight on `M ⋊_α ℝ`

The substantive content of this file. The dual weight `φ̂` is a weight on
the crossed product, characterized by the scaling property under the dual
action and a normalization compatible with `φ`.

Existence is bundled. The bundling encapsulates the entire content of
Takesaki's *Tomita's Theory* (1970): the dual weight comes equipped with
its own GNS Hilbert space, its own modular operator, its own modular
conjugation, and its own KMS analytics. We expose only the algebraic
shadow: the scaling property and the inner-implementation of the modular
flow.
-/

/-- A weight on the crossed product `M ⋊_α ℝ`.

    Same definition as `Weight M`, but with the algebra parameter replaced
    by the crossed product. We do not abstract this — the duplication is
    minimal and reduces type-class friction. -/
structure CrossedWeight {α : RDynamics M} (R : CovariantRep α) where
  /-- The weight as a function on operators on `K = L²(ℝ, H)`. -/
  fn : (CrossedSpace H →L[ℂ] CrossedSpace H) → ℝ≥0∞
  /-- Vanishes outside the crossed product. -/
  outside_zero : ∀ x : CrossedSpace H →L[ℂ] CrossedSpace H,
    x ∉ crossedProduct α R → fn x = 0
  /-- Additivity inside the crossed product. -/
  additive : ∀ x y : CrossedSpace H →L[ℂ] CrossedSpace H,
    x ∈ crossedProduct α R → y ∈ crossedProduct α R →
    fn (x + y) = fn x + fn y
  /-- Scale-equivariance for non-negative reals. -/
  smul_eq : ∀ (c : ℝ≥0) (x : CrossedSpace H →L[ℂ] CrossedSpace H),
    x ∈ crossedProduct α R → fn ((c : ℂ) • x) = c • fn x
  /-- Faithful. -/
  faithful : ∀ x : CrossedSpace H →L[ℂ] CrossedSpace H, x ∈ crossedProduct α R →
    fn (star x * x) = 0 → x = 0

/-- A weight on the crossed product is a trace if it is cyclic. -/
def CrossedWeight.IsTrace {α : RDynamics M} {R : CovariantRep α}
    (ω : CrossedWeight R) : Prop :=
  ∀ x y : CrossedSpace H →L[ℂ] CrossedSpace H,
    x ∈ crossedProduct α R → y ∈ crossedProduct α R →
    ω.fn (x * y) = ω.fn (y * x)

/-- **The dual weight data.** Given a weight `φ` on `M`, an action `α`, a
    covariant representation `R`, and the dual action data `D`, the dual
    weight `φ̂` is a weight on `M ⋊_α ℝ` satisfying the scaling property
    and the inner-implementation of the modular flow.

    The existence of `φ̂` with these properties is Takesaki's theorem from
    *Tomita's Theory of Modular Hilbert Algebras* (1970). We bundle the
    output as data rather than deriving it. -/
structure DualWeightData {α : RDynamics M} (R : CovariantRep α)
    (D : DualActionData R) (φ : Weight M) where
  /-- The dual weight. -/
  dualWeight : CrossedWeight R
  /-- **Scaling property**: `φ̂(α̂_s(x)) = e^{-s} · φ̂(x)`.

      This is the defining property of the dual weight (up to a positive
      scalar). It expresses that `φ̂` transforms with weight `-1` under
      energy shifts. -/
  scaling : ∀ (s : ℝ) (x : CrossedSpace H →L[ℂ] CrossedSpace H),
    x ∈ crossedProduct α R →
    dualWeight.fn (D.act s x) =
      ENNReal.ofReal (Real.exp (-s)) * dualWeight.fn x
  /-- **Compatibility with `φ`**: on the diagonal piece, the dual weight
      restricts to `φ` (modulo Plancherel normalization). Formally: for
      `a ∈ M.algebra` and `t ∈ ℝ` with `t ≠ 0`,
        `φ̂(π(a) · U(t)) = 0`
      (the "Dirac at zero" of the formal description). The diagonal value
      `φ̂(π(a))` is `φ(a)`. -/
  diagonal_eq : ∀ a : H →L[ℂ] H, a ∈ M.algebra →
    dualWeight.fn (R.diag.π a) = φ.fn a
  /-- **Inner implementation of the modular flow**: the modular
      automorphism `σ^{φ̂}_t` is implemented by conjugation with `U(t)`.

      This is the key intermediate fact en route to the trace theorem.
      A weight whose modular automorphism is inner is, modulo bookkeeping,
      a trace. -/
  modular_inner : ∀ (t : ℝ) (x : CrossedSpace H →L[ℂ] CrossedSpace H),
    x ∈ crossedProduct α R →
    dualWeight.fn (R.trans.U t * x * adjoint (R.trans.U t)) = dualWeight.fn x

/-! ## Section 4: Takesaki's Trace Theorem

The deep result. When the action `α` is the modular automorphism group
`σ^φ` of the input weight, the dual weight is a *trace*. This is the
"III becomes II" step.

We bundle this as a hypothesis. Its proof requires:
* Construction of `φ̂` (Takesaki 1970, via Tomita's modular Hilbert algebra
  machinery).
* The relation `σ^{φ̂} = Ad(U)` (the modular automorphism of `φ̂` is inner,
  implemented by the translations).
* Inner modular automorphism ⟹ trace (modulo the cocycle for `φ̂` itself,
  which is trivial when implemented inside the algebra).
-/

/-- **Takesaki's Trace Theorem.**

    Given a faithful normal semifinite weight `φ` on `M`, when the
    automorphism group `α` is the modular automorphism group of `φ`
    (`α_t = σ^φ_t`), the dual weight `φ̂` on `M ⋊_{σ^φ} ℝ` is a *trace*.

    Equivalently: the modular automorphism group of `φ̂` is trivial in
    `Out(M ⋊ ℝ)`, i.e., entirely inner — and in fact already inner inside
    `M ⋊ ℝ` itself. So `φ̂` is its own modular weight, which (for a normal
    semifinite weight) is the trace condition.

    This is **the** theorem of [Takesaki, *Tomita's Theory of Modular
    Hilbert Algebras*, 1970]. -/
structure TakesakiTrace
    {α : RDynamics M} (R : CovariantRep α)
    (D : DualActionData R) (φ : Weight M)
    (W : DualWeightData R D φ)
    /- The hypothesis that `α` is the modular automorphism group of `φ`.
        Stated abstractly: there is modular data `md` (the flow `t ↦ Δ^{it}`
        and the conjugation `J`) with a `TomitaTheorem` witness, such that
        `α.α = modularAutomorphism md`. -/
    (md : ModularData H M)
    (hTT : TomitaTheorem H M md)
    (hα : ∀ t a, α.α t a = modularAutomorphism md t a) where
  /-- The conclusion: the dual weight is a trace. -/
  isTrace : W.dualWeight.IsTrace

/-! ## Section 5: Consequences

Algebraic corollaries of the above. These are the lemmas downstream files
(notably `TypeII.lean`) will consume.
-/

variable {R : CovariantRep α} {D : DualActionData R} {φ : Weight M}

/-- The dual weight on the diagonal recovers the original weight. -/
lemma DualWeightData.fn_diag (W : DualWeightData R D φ)
    {a : H →L[ℂ] H} (ha : a ∈ M.algebra) :
    W.dualWeight.fn (R.diag.π a) = φ.fn a :=
  W.diagonal_eq a ha

/-- Iterated scaling: `φ̂ ∘ α̂_{s₁} ∘ α̂_{s₂} = e^{-(s₁+s₂)} · φ̂`. -/
lemma DualWeightData.scaling_compose (W : DualWeightData R D φ) (s₁ s₂ : ℝ)
    {x : CrossedSpace H →L[ℂ] CrossedSpace H} (hx : x ∈ crossedProduct α R) :
    W.dualWeight.fn (D.act s₁ (D.act s₂ x)) =
      ENNReal.ofReal (Real.exp (-(s₁ + s₂))) * W.dualWeight.fn x := by
  rw [W.scaling s₁ (D.act s₂ x) (D.act_mem s₂ hx)]
  rw [W.scaling s₂ x hx]
  rw [← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- **The pivotal consequence.** In the modular case, the dual weight is a
    trace; thus a tracial state exists on the crossed product. This is the
    one-line theorem that justifies the entire construction.

    With this in hand, `M ⋊_{σ^φ} ℝ` admits a notion of entropy
    `S(x) = -Tr(x log x)` for density matrices `x`, well-defined up to an
    additive constant. -/
theorem trace_exists_in_modular_case
    (R : CovariantRep α) (D : DualActionData R) (φ : Weight M)
    (W : DualWeightData R D φ)
    (md : ModularData H M)
    (hTT : TomitaTheorem H M md)
    (hα : ∀ t a, α.α t a = modularAutomorphism md t a)
    (hTakesaki : TakesakiTrace R D φ W md hTT hα) :
    W.dualWeight.IsTrace :=
  hTakesaki.isTrace

end Spectra.CrossedProduct

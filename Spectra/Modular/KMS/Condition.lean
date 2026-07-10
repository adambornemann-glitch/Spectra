/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.PeriodicStrip.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
-- For the conjugate-reflection of holomorphic functions (`DifferentiableAt.conj_conj`)
import Mathlib.Analysis.Calculus.Deriv.Star
-- The C*-algebra class itself
import Mathlib.Analysis.CStarAlgebra.Classes
-- For the C*-identity, norm properties, star properties
import Mathlib.Analysis.CStarAlgebra.Basic
-- For *-homomorphism contractivity (GNS boundedness for free)
import Mathlib.Analysis.CStarAlgebra.Spectrum
-- For the order `0 ≤ z` on ℂ (positivity of states)
import Mathlib.Analysis.Complex.Order
/-!
# The Kubo-Martin-Schwinger (KMS) Condition

This file defines the KMS condition for states on C*-algebras with dynamics.

## The Physics

The KMS condition characterizes thermal equilibrium states in quantum statistical mechanics.
It was introduced by Kubo (1957) and Martin-Schwinger (1959), and given its modern
operator-algebraic form by Haag-Hugenholtz-Winnink (1967).

## The Mathematics

Given:
- A C*-algebra `A` (the observables)
- A one-parameter automorphism group `α : ℝ → Aut(A)` (time evolution)
- A state `ω : A → ℂ` (expectation values)
- Inverse temperature `β > 0`

The state ω satisfies the **KMS condition at inverse temperature β** if:
for all a, b ∈ A, there exists a function F : ℂ → ℂ such that:

1. F is holomorphic on the open strip S_β = {z : 0 < Im(z) < β}
2. F is bounded and continuous on the closed strip S̄_β = {z : 0 ≤ Im(z) ≤ β}
3. F(t) = ω(a · α_t(b)) for all t ∈ ℝ (lower boundary)
4. F(t + iβ) = ω(α_t(b) · a) for all t ∈ ℝ (upper boundary)

The "twist" between the two boundaries encodes the non-commutativity of quantum
observables and the thermal nature of the state.

## Main Definitions

- `Strip β`: The horizontal strip {z ∈ ℂ : 0 < Im(z) < β}
- `ClosedStrip β`: The closed strip {z ∈ ℂ : 0 ≤ Im(z) ≤ β}
- `KMSFunction`: A function satisfying the analyticity/boundary conditions
- `IsKMSState`: The predicate that a state satisfies the KMS condition

## References

* R. Kubo, "Statistical-Mechanical Theory of Irreversible Processes", J. Phys. Soc. Japan 12 (1957)
* P.C. Martin, J. Schwinger, "Theory of Many-Particle Systems. I", Phys. Rev. 115 (1959)
* R. Haag, N. Hugenholtz, M. Winnink, "On the Equilibrium States in Quantum Statistical Mechanics",
  Comm. Math. Phys. 5 (1967)
* O. Bratteli, D.W. Robinson, "Operator Algebras and Quantum Statistical Mechanics 2" (1997)

-/
open Complex Set Filter Topology Convex
open Spectra.PeriodicHolomorphic
open ComplexConjugate
open scoped ComplexOrder

namespace Spectra.KMS

/-! ## The Strip in the Complex Plane -/

/-- The lower boundary of the strip (the real line) -/
def LowerBoundary : Set ℂ :=
  {z : ℂ | z.im = 0}

/-- The upper boundary of the strip at height β -/
def UpperBoundary (β : ℝ) : Set ℂ :=
  {z : ℂ | z.im = β}

-- Basic lemmas about strips
/-- The open strip is contained in the closed strip. -/
lemma Strip_subset_ClosedStrip {β : ℝ} (_hβ : 0 < β) : Strip β ⊆ ClosedStrip β := by
  intro z ⟨h1, h2⟩
  exact ⟨le_of_lt h1, le_of_lt h2⟩

/-- The lower boundary `{Im z = 0}` is contained in the closed strip when `0 ≤ β`. -/
lemma LowerBoundary_subset_ClosedStrip {β : ℝ} (hβ : 0 ≤ β) : LowerBoundary ⊆ ClosedStrip β := by
  intro z hz
  simp only [LowerBoundary, ClosedStrip, mem_setOf_eq] at *
  exact ⟨le_of_eq hz.symm, by linarith⟩

/-- The upper boundary `{Im z = β}` is contained in the closed strip when `0 ≤ β`.
(Currently unused.) -/
lemma UpperBoundary_subset_ClosedStrip {β : ℝ} (hβ : 0 ≤ β) : UpperBoundary β ⊆ ClosedStrip β := by
  intro z hz
  simp only [UpperBoundary, ClosedStrip, mem_setOf_eq] at *
  exact ⟨by linarith, le_of_eq hz⟩

/-- The point `realToLower t` has imaginary part `0`. -/
lemma realToLower_im (t : ℝ) : (realToLower t).im = 0 := by
  simp [realToLower]

/-- The point `realToUpper β t` has imaginary part `β`. -/
lemma realToUpper_im (β t : ℝ) : (realToUpper β t).im = β := by
  simp [realToUpper]

/-- `realToLower t` lies on the lower boundary. -/
lemma realToLower_mem_LowerBoundary (t : ℝ) : realToLower t ∈ LowerBoundary :=
  realToLower_im t

/-- `realToUpper β t` lies on the upper boundary at height `β`. (Currently unused.) -/
lemma realToUpper_mem_UpperBoundary (β t : ℝ) : realToUpper β t ∈ UpperBoundary β :=
  realToUpper_im β t

/-! ## Axiomatized Structures

We axiomatize the structures we need. These will be replaced with proper
definitions as we build out the library.
-/

/-- A one-parameter *-automorphism group on a C*-algebra.

Mathematically: A strongly continuous group homomorphism α : ℝ → Aut(A),
where Aut(A) is the group of *-automorphisms of A.

This represents time evolution: α_t(a) is the observable a evolved by time t.
-/
structure Dynamics (A : Type*) [CStarAlgebra A] where
  /-- The automorphism at time t. A `*`-automorphism is **ℂ-linear** (not conjugate-linear):
  `α_t (c • a) = c • α_t a`. Using the conjugate-linear `A →ₗ⋆[ℂ] A` here would be inconsistent
  with `evolve_zero` (it would force `c • a = conj c • a`, making `Dynamics A` uninhabited for
  every nontrivial `A`). -/
  evolve : ℝ → A →ₗ[ℂ] A
  /-- Each α_t is multiplicative -/
  map_mul : ∀ t a b, evolve t (a * b) = evolve t a * evolve t b
  /-- Each α_t preserves the unit (if it exists) -/
  map_one : ∀ t, evolve t 1 = 1
  /-- Each α_t preserves the star -/
  map_star : ∀ t a, evolve t (star a) = star (evolve t a)
  /-- Group property: α_{s+t} = α_s ∘ α_t -/
  evolve_add : ∀ s t a, evolve (s + t) a = evolve s (evolve t a)
  /-- Identity at t = 0 -/
  evolve_zero : ∀ a, evolve 0 a = a
  /-- Strong continuity: t ↦ α_t(a) is continuous for each a -/
  continuous_evolve : ∀ a, Continuous (fun t => evolve t a)

-- Notation for dynamics
notation:max "α[" τ "]" => Dynamics.evolve τ

/-- The **trivial dynamics**: time evolution is the identity `α_t = id` at every `t`.

This is a genuine `Dynamics A` for every C*-algebra `A`, witnessing that the structure is
**inhabited**. It is the sanity check guaranteeing the development is not vacuous: the
conjugate-linear (`A →ₗ⋆[ℂ] A`) alternative for `evolve` would have made `Dynamics A`
uninhabited for every nontrivial `A` (it contradicts `evolve_zero`), so every KMS theorem
would have rested on an unsatisfiable hypothesis. -/
noncomputable def Dynamics.trivial (A : Type*) [CStarAlgebra A] : Dynamics A where
  evolve := fun _ => LinearMap.id
  map_mul := fun _ _ _ => rfl
  map_one := fun _ => rfl
  map_star := fun _ _ => rfl
  evolve_add := fun _ _ _ => rfl
  evolve_zero := fun _ => rfl
  continuous_evolve := fun _ => continuous_const

/-- `Dynamics A` is inhabited, witnessed by the trivial dynamics. -/
instance (A : Type*) [CStarAlgebra A] : Nonempty (Dynamics A) := ⟨Dynamics.trivial A⟩

/-- A state on a C*-algebra.

Mathematically: A positive linear functional of norm 1.
Physically: An expectation value functional ω(a) = ⟨ψ|a|ψ⟩.
-/
structure State (A : Type*) [CStarAlgebra A] where
  /-- The underlying linear functional -/
  toFun : A →ₗ[ℂ] ℂ
  /-- Positivity: `ω(a⋆a)` is a nonnegative real (using the `ComplexOrder` partial order
  `0 ≤ z ↔ 0 ≤ z.re ∧ z.im = 0`). This is the full positivity of a state, including that the
  value is real — not merely that its real part is nonnegative. -/
  nonneg : ∀ a, 0 ≤ toFun (star a * a)
  /-- Normalization: ω(1) = 1 -/
  normalized : toFun 1 = 1
  /-- Continuity -/
  continuous : Continuous toFun

-- Coercion to function
/-- A `State A` coerces to its underlying function `A → ℂ`. -/
noncomputable instance (A : Type*) [CStarAlgebra A] : CoeFun (State A) (fun _ => A → ℂ) :=
  ⟨fun ω => ω.toFun⟩

/-- The convex mixture `t·ω₁ + (1-t)·ω₂` of two states, for `0 ≤ t ≤ 1`.
Positivity and normalization are preserved because `t` and `1-t` are nonnegative
and sum to one. -/
noncomputable def State.mix {A : Type*} [CStarAlgebra A]
    (ω₁ ω₂ : State A) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : State A where
  toFun := (t : ℂ) • ω₁.toFun + (1 - (t : ℂ)) • ω₂.toFun
  nonneg := fun a => by
    obtain ⟨h1re, h1im⟩ := Complex.nonneg_iff.mp (ω₁.nonneg a)
    obtain ⟨h2re, h2im⟩ := Complex.nonneg_iff.mp (ω₂.nonneg a)
    have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
    rw [Complex.nonneg_iff]
    refine ⟨?_, ?_⟩
    · have hre : (((t : ℂ) • ω₁.toFun + (1 - (t : ℂ)) • ω₂.toFun) (star a * a)).re
          = t * (ω₁.toFun (star a * a)).re + (1 - t) * (ω₂.toFun (star a * a)).re := by
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Complex.add_re,
          Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.sub_im,
          Complex.one_im, Complex.ofReal_im]
        ring
      rw [hre]
      exact add_nonneg (mul_nonneg ht₀ h1re) (mul_nonneg ht1' h2re)
    · have him : (((t : ℂ) • ω₁.toFun + (1 - (t : ℂ)) • ω₂.toFun) (star a * a)).im
          = t * (ω₁.toFun (star a * a)).im + (1 - t) * (ω₂.toFun (star a * a)).im := by
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Complex.add_im,
          Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.sub_im,
          Complex.one_im, Complex.ofReal_im]
        ring
      rw [him, ← h1im, ← h2im]; ring
  normalized := by
    show ((t : ℂ) • ω₁.toFun + (1 - (t : ℂ)) • ω₂.toFun) 1 = 1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, ω₁.normalized, ω₂.normalized,
      smul_eq_mul, mul_one]
    ring
  continuous := by
    have hcoe : ⇑((t : ℂ) • ω₁.toFun + (1 - (t : ℂ)) • ω₂.toFun)
        = fun a => (t : ℂ) • ω₁.toFun a + (1 - (t : ℂ)) • ω₂.toFun a := rfl
    rw [hcoe]
    exact (ω₁.continuous.const_smul (t : ℂ)).add (ω₂.continuous.const_smul (1 - (t : ℂ)))

/-- Evaluation of a mixture: `(t·ω₁ + (1-t)·ω₂)(a) = t·ω₁(a) + (1-t)·ω₂(a)`. -/
@[simp]
lemma State.mix_apply {A : Type*} [CStarAlgebra A]
    (ω₁ ω₂ : State A) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (a : A) :
    State.mix ω₁ ω₂ t ht₀ ht₁ a = t * ω₁ a + (1 - t) * ω₂ a := by
  change ((t : ℂ) • ω₁.toFun + (1 - (t : ℂ)) • ω₂.toFun) a = _
  simp [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-! ## Hermiticity of States

A state is a *positive* functional, and positivity forces conjugate-symmetry of the
associated sesquilinear form `(b, c) ↦ ω (star b * c)` — and hence hermiticity
`ω (star a) = star (ω a)`. These would be **false** under the old real-part-only
`nonneg` axiom; they need the genuine positivity now carried by `State.nonneg`.
-/

/-- **Conjugate symmetry of the GNS form.** For a state `ω`, the sesquilinear form
`(b, c) ↦ ω (star b * c)` is conjugate-symmetric:
`ω (star b * c) = star (ω (star c * b))`. Proof by the polarization identity, using that
the diagonal `ω (star x * x)` is a nonnegative real. -/
lemma State.inner_conj {A : Type*} [CStarAlgebra A] (ω : State A) (b c : A) :
    ω (star b * c) = star (ω (star c * b)) := by
  -- The diagonal `ω (star x * x)` of the form is real.
  have hr : ∀ x : A, (ω.toFun (star x * x)).im = 0 :=
    fun x => (Complex.nonneg_iff.mp (ω.nonneg x)).2.symm
  change ω.toFun (star b * c) = star (ω.toFun (star c * b))
  -- Polarization at `x = b + c`.
  have e1 : ω.toFun (star (b + c) * (b + c))
      = ω.toFun (star b * b) + ω.toFun (star b * c)
        + ω.toFun (star c * b) + ω.toFun (star c * c) := by
    rw [star_add,
      show (star b + star c) * (b + c)
        = star b * b + star b * c + star c * b + star c * c from by noncomm_ring]
    simp only [map_add]
  -- Polarization at `x = b + I•c`.
  have e2 : ω.toFun (star (b + I • c) * (b + I • c))
      = ω.toFun (star b * b) + I * ω.toFun (star b * c)
        - I * ω.toFun (star c * b) + ω.toFun (star c * c) := by
    have expand : star (b + I • c) * (b + I • c)
        = star b * b + (I • (star b * c)
            + ((-I) • (star c * b) + ((-I) * I) • (star c * c))) := by
      rw [star_add, star_smul, show star (I : ℂ) = -I from by simp,
        add_mul, mul_add, mul_add, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
        mul_smul_comm, smul_smul]
      abel
    rw [expand, map_add, map_add, map_add, map_smul, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul,
      show (-I : ℂ) * I = 1 from by rw [neg_mul, Complex.I_mul_I, neg_neg]]
    ring
  -- Imaginary parts are opposite (from `e1`).
  have hI : (ω.toFun (star b * c)).im = -(ω.toFun (star c * b)).im := by
    have h := congrArg Complex.im e1
    rw [hr (b + c)] at h
    simp only [Complex.add_im] at h
    rw [hr b, hr c] at h
    linarith
  -- Real parts are equal (from `e2`, whose value is real).
  have hR : (ω.toFun (star b * c)).re = (ω.toFun (star c * b)).re := by
    have h := congrArg Complex.im e2
    rw [hr (b + I • c)] at h
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add] at h
    rw [hr b, hr c] at h
    linarith
  apply Complex.ext
  · rw [hR]; simp
  · rw [hI]; simp

/-- **States are hermitian (self-adjoint).** `ω (star a) = star (ω a)` for any state `ω`
(the outer `star` is complex conjugation). The special case `b = 1` of `State.inner_conj`. -/
lemma State.star_apply {A : Type*} [CStarAlgebra A] (ω : State A) (a : A) :
    ω (star a) = star (ω a) := by
  have h := ω.inner_conj 1 a
  simp only [star_one, one_mul, mul_one] at h
  rw [h, star_star]

/-- **Conjugation symmetry of two-point correlations.** Using hermiticity of `ω` and the
fact that the dynamics is a `*`-automorphism, the correlation `ω (a · α_t b)` is the complex
conjugate of the reversed, starred correlation. (Holds for any state and any dynamics.) -/
lemma kms_correlation_conj {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) (t : ℝ) (a b : A) :
    ω (a * α.evolve t b) = star (ω (α.evolve t (star b) * star a)) := by
  have hstar : α.evolve t (star b) * star a = star (a * α.evolve t b) := by
    rw [star_mul, ← α.map_star]
  rw [hstar, ω.star_apply, star_star]

/-! ## The KMS Condition -/

/-- A KMS function for elements a, b at inverse temperature β.

This encapsulates a function F : ℂ → ℂ satisfying:
1. Holomorphic on the open strip S_β
2. Bounded and continuous on the closed strip
3. Correct boundary values relating ω(a·α_t(b)) and ω(α_t(b)·a)
-/
structure KMSFunction {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) (β : ℝ) (a b : A) where
  /-- The underlying function -/
  toFun : ℂ → ℂ
  /-- Holomorphic on the open strip -/
  holomorphic : DifferentiableOn ℂ toFun (Strip β)
  /-- Continuous on the closed strip -/
  continuousOn : ContinuousOn toFun (ClosedStrip β)
  /-- Bounded on the closed strip -/
  bounded : BddAbove (norm '' (toFun '' ClosedStrip β))
  /-- Lower boundary condition: F(t) = ω(a · α_t(b)) -/
  lower_boundary : ∀ t : ℝ, toFun (realToLower t) = ω (a * α.evolve t b)
  /-- Upper boundary condition: F(t + iβ) = ω(α_t(b) · a) -/
  upper_boundary : ∀ t : ℝ, toFun (realToUpper β t) = ω (α.evolve t b * a)

/-- A state ω is a KMS state at inverse temperature β with respect to dynamics α
if for every pair of elements a, b ∈ A, there exists a KMS function. -/
def IsKMSState {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) (β : ℝ) : Prop :=
  ∀ a b : A, Nonempty (KMSFunction ω α β a b)

/-! ## Important Special Cases -/

/-- A state is a ground state (KMS at β = +∞) if for every pair `a, b` the two-point
function `t ↦ ω (a · α_t b)` extends to a **bounded** function that is holomorphic on the
open upper half-plane and continuous on its closure.

The boundedness clause is what makes the half-plane an effective domain: it is the β → ∞
limit of the KMS boundedness on the strip, and it is exactly the hypothesis the half-plane
Phragmén–Lindelöf / Liouville arguments require (a one-sided analyticity condition with no
growth control is too weak — e.g. `e^{iz}` is bounded and holomorphic on the UHP but its
real-line values are not constant). -/
def IsGroundState {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) : Prop :=
  ∀ a b : A, ∃ F : ℂ → ℂ,
    DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
    ContinuousOn F {z : ℂ | 0 ≤ z.im} ∧
    BddAbove (norm '' (F '' {z : ℂ | 0 ≤ z.im})) ∧
    (∀ t : ℝ, F t = ω (a * α.evolve t b))

/-- A state is α-invariant if ω ∘ α_t = ω for all t. -/
def IsInvariant {A : Type*} [CStarAlgebra A]
    (ω : State A) (α : Dynamics A) : Prop :=
  ∀ t a, ω (α.evolve t a) = ω a

/-! ## Basic Properties -/


variable {A : Type*} [CStarAlgebra A]

/-! ## The Convex Combination of KMS Functions -/

/-- Given KMS functions F₁, F₂ for states ω₁, ω₂, construct the convex combination. -/
def KMSFunction.convexCombination
    {ω₁ ω₂ ω : State A} {α : Dynamics A} {β : ℝ} {a b : A}
    (F₁ : KMSFunction ω₁ α β a b)
    (F₂ : KMSFunction ω₂ α β a b)
    (t : ℝ)
    (hω : ∀ x, ω x = t * ω₁ x + (1 - t) * ω₂ x) :
    KMSFunction ω α β a b where
  -- The underlying function is the convex combination
  toFun := fun z => t * F₁.toFun z + (1 - t) * F₂.toFun z
  -- Holomorphic: sum of holomorphic functions is holomorphic
  holomorphic := by
    refine DifferentiableOn.add ?_ ?_
    · convert F₁.holomorphic.const_smul (t : ℂ) using 1
    · convert F₂.holomorphic.const_smul ((1 - t) : ℂ) using 1

  -- Continuous: sum of continuous functions is continuous
  continuousOn := by
    refine ContinuousOn.add ?_ ?_
    · exact (continuousOn_const).mul F₁.continuousOn
    · exact (continuousOn_const).mul F₂.continuousOn
  -- Bounded: follows from F₁, F₂ bounded via triangle inequality
  bounded := by
    -- Get bounds for F₁ and F₂
    obtain ⟨M₁, hM₁⟩ := F₁.bounded
    obtain ⟨M₂, hM₂⟩ := F₂.bounded
    -- The combination is bounded by |t|*M₁ + |1-t|*M₂
    use |t| * M₁ + |1 - t| * M₂
    intro y hy
    -- y is in the image of norms
    simp only [mem_image] at hy
    obtain ⟨w, ⟨z, hz, rfl⟩, rfl⟩ := hy
    -- Use triangle inequality: ‖a + b‖ ≤ ‖a‖ + ‖b‖
    calc ‖t * F₁.toFun z + (1 - t) * F₂.toFun z‖
        ≤ ‖t * F₁.toFun z‖ + ‖(1 - t) * F₂.toFun z‖ := norm_add_le _ _
      _ = |t| * ‖F₁.toFun z‖ + |1 - t| * ‖F₂.toFun z‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real]
          rw [show (1 - t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
          rw [Complex.norm_real]
          rfl
      _ ≤ |t| * M₁ + |1 - t| * M₂ := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
            apply hM₁
            simp only [mem_image, exists_exists_and_eq_and]
            exact ⟨z, hz, rfl⟩
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg (1 - t))
            apply hM₂
            simp only [mem_image, exists_exists_and_eq_and]
            exact ⟨z, hz, rfl⟩
  -- Lower boundary: F(t) = ω(a · α_t(b))
  lower_boundary := by
    intro s
    -- F(s) = t * F₁(s) + (1-t) * F₂(s)
    --      = t * ω₁(a * α_s(b)) + (1-t) * ω₂(a * α_s(b))
    --      = ω(a * α_s(b))
    rw [F₁.lower_boundary, F₂.lower_boundary]
    rw [hω]
  -- Upper boundary: F(t + iβ) = ω(α_t(b) · a)
  upper_boundary := by
    intro s
    rw [F₁.upper_boundary, F₂.upper_boundary]
    rw [hω]

/-! ## The Main Theorem -/

/-- The set of KMS states at fixed β is convex.

If ω₁ and ω₂ are both KMS at β, then so is λω₁ + (1-λ)ω₂ for 0 ≤ λ ≤ 1.
This reflects that mixtures of equilibrium states at the same temperature
are still equilibrium states.
-/
lemma kms_states_convex_combination
    (α : Dynamics A) (β : ℝ) (ω₁ ω₂ : State A)
    (h₁ : IsKMSState ω₁ α β) (h₂ : IsKMSState ω₂ α β)
    (t : ℝ) (_ht₀ : 0 ≤ t) (_ht₁ : t ≤ 1)
    (ω : State A)
    (hω : ∀ a, ω a = t * ω₁ a + (1 - t) * ω₂ a) :
    IsKMSState ω α β := by
  -- We need to show: for all a b, there exists a KMS function
  intro a b
  -- Get the KMS functions for ω₁ and ω₂
  obtain ⟨F₁⟩ := h₁ a b
  obtain ⟨F₂⟩ := h₂ a b
  -- The convex combination works!
  exact ⟨KMSFunction.convexCombination F₁ F₂ t hω⟩

/-- **The set of KMS states at fixed β is convex** (constructive form).

If `ω₁` and `ω₂` are KMS at `β`, then so is the mixture `State.mix ω₁ ω₂ t` for
`0 ≤ t ≤ 1`. Unlike `kms_states_convex_combination`, this builds the mixed state
rather than taking it (plus a defining equation) as a hypothesis. -/
lemma IsKMSState.mix
    {α : Dynamics A} {β : ℝ} {ω₁ ω₂ : State A}
    (h₁ : IsKMSState ω₁ α β) (h₂ : IsKMSState ω₂ α β)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsKMSState (State.mix ω₁ ω₂ t ht₀ ht₁) α β := by
  intro a b
  obtain ⟨F₁⟩ := h₁ a b
  obtain ⟨F₂⟩ := h₂ a b
  exact ⟨KMSFunction.convexCombination F₁ F₂ t
    (fun x => State.mix_apply ω₁ ω₂ t ht₀ ht₁ x)⟩


/-! ## Uniqueness of the KMS Function -/

/-- **The KMS function is unique.** For a fixed pair `(a, b)` any two KMS functions
agree on the closed strip: they share both boundary values, and a bounded
holomorphic function on the strip is determined by its boundary data (Hadamard
three-lines). Thus `F_{a,b}` is *the* analytic continuation of the correlation
`t ↦ ω(a · α_t b)`. -/
lemma KMSFunction.unique
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β) {a b : A}
    (F G : KMSFunction ω α β a b) :
    Set.EqOn F.toFun G.toFun (ClosedStrip β) :=
  eqOn_closedStrip_of_boundary_eq F.toFun G.toFun hβ
    F.holomorphic G.holomorphic F.continuousOn G.continuousOn F.bounded G.bounded
    (fun t => by rw [F.lower_boundary, G.lower_boundary])
    (fun t => by rw [F.upper_boundary, G.upper_boundary])

/-! ## Bilinearity of the Two-Point Function

The analytic two-point function `F_{a,b}` is **bilinear** in the pair `(a, b)`: the boundary
correlations `t ↦ ω(a · α_t b)` (lower) and `t ↦ ω(α_t b · a)` (upper) are ℂ-linear in each of
`a` and `b`. This uses that `ω` is ℂ-linear, that multiplication is ℂ-bilinear, and — crucially
— that the dynamics `α_t` is **ℂ-linear** (the right-slot scalar would carry a complex conjugate
under the inconsistent conjugate-linear `evolve`).

Each combinator builds the KMS function for the combined pair *pointwise* from the pieces;
`KMSFunction.unique` then shows the canonical analytic continuation inherits the same bilinearity.

(Note: this is **not** the GNS sesquilinear form `(b, c) ↦ ω(star b * c)`, which is
conjugate-symmetric — see `State.inner_conj`. The two-point function carries no `star` on `a`,
so it is genuinely linear, not conjugate-linear, in the left slot.)
-/

/-- **Sum in the right slot.** `F_{a,b₁} + F_{a,b₂}` is a KMS function for `(a, b₁ + b₂)`. -/
def KMSFunction.add {ω : State A} {α : Dynamics A} {β : ℝ} {a b₁ b₂ : A}
    (F₁ : KMSFunction ω α β a b₁) (F₂ : KMSFunction ω α β a b₂) :
    KMSFunction ω α β a (b₁ + b₂) where
  toFun := fun z => F₁.toFun z + F₂.toFun z
  holomorphic := F₁.holomorphic.add F₂.holomorphic
  continuousOn := F₁.continuousOn.add F₂.continuousOn
  bounded := by
    obtain ⟨M₁, hM₁⟩ := F₁.bounded
    obtain ⟨M₂, hM₂⟩ := F₂.bounded
    refine ⟨M₁ + M₂, ?_⟩
    rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add
      (hM₁ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hz)))
      (hM₂ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hz))))
  lower_boundary := fun t => by
    show F₁.toFun (realToLower t) + F₂.toFun (realToLower t) = ω (a * α.evolve t (b₁ + b₂))
    rw [F₁.lower_boundary, F₂.lower_boundary, map_add (α.evolve t), mul_add, map_add]
  upper_boundary := fun t => by
    show F₁.toFun (realToUpper β t) + F₂.toFun (realToUpper β t) = ω (α.evolve t (b₁ + b₂) * a)
    rw [F₁.upper_boundary, F₂.upper_boundary, map_add (α.evolve t), add_mul, map_add]

/-- **Scalar in the right slot.** `c • F_{a,b}` is a KMS function for `(a, c • b)`. -/
def KMSFunction.smul {ω : State A} {α : Dynamics A} {β : ℝ} {a b : A}
    (c : ℂ) (F : KMSFunction ω α β a b) :
    KMSFunction ω α β a (c • b) where
  toFun := fun z => c • F.toFun z
  holomorphic := F.holomorphic.const_smul c
  continuousOn := F.continuousOn.const_smul c
  bounded := by
    obtain ⟨M, hM⟩ := F.bounded
    refine ⟨‖c‖ * M, ?_⟩
    rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    change ‖c • F.toFun z‖ ≤ ‖c‖ * M
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hM (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hz))) (norm_nonneg c)
  lower_boundary := fun t => by
    show c • F.toFun (realToLower t) = ω (a * α.evolve t (c • b))
    rw [F.lower_boundary, map_smul, mul_smul_comm, map_smul]
  upper_boundary := fun t => by
    show c • F.toFun (realToUpper β t) = ω (α.evolve t (c • b) * a)
    rw [F.upper_boundary, map_smul, smul_mul_assoc, map_smul]

/-- **Sum in the left slot.** `F_{a₁,b} + F_{a₂,b}` is a KMS function for `(a₁ + a₂, b)`. -/
def KMSFunction.addLeft {ω : State A} {α : Dynamics A} {β : ℝ} {a₁ a₂ b : A}
    (F₁ : KMSFunction ω α β a₁ b) (F₂ : KMSFunction ω α β a₂ b) :
    KMSFunction ω α β (a₁ + a₂) b where
  toFun := fun z => F₁.toFun z + F₂.toFun z
  holomorphic := F₁.holomorphic.add F₂.holomorphic
  continuousOn := F₁.continuousOn.add F₂.continuousOn
  bounded := by
    obtain ⟨M₁, hM₁⟩ := F₁.bounded
    obtain ⟨M₂, hM₂⟩ := F₂.bounded
    refine ⟨M₁ + M₂, ?_⟩
    rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add
      (hM₁ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hz)))
      (hM₂ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hz))))
  lower_boundary := fun t => by
    show F₁.toFun (realToLower t) + F₂.toFun (realToLower t) = ω ((a₁ + a₂) * α.evolve t b)
    rw [F₁.lower_boundary, F₂.lower_boundary, add_mul, map_add]
  upper_boundary := fun t => by
    show F₁.toFun (realToUpper β t) + F₂.toFun (realToUpper β t) = ω (α.evolve t b * (a₁ + a₂))
    rw [F₁.upper_boundary, F₂.upper_boundary, mul_add, map_add]

/-- **Scalar in the left slot.** `c • F_{a,b}` is a KMS function for `(c • a, b)`. -/
def KMSFunction.smulLeft {ω : State A} {α : Dynamics A} {β : ℝ} {a b : A}
    (c : ℂ) (F : KMSFunction ω α β a b) :
    KMSFunction ω α β (c • a) b where
  toFun := fun z => c • F.toFun z
  holomorphic := F.holomorphic.const_smul c
  continuousOn := F.continuousOn.const_smul c
  bounded := by
    obtain ⟨M, hM⟩ := F.bounded
    refine ⟨‖c‖ * M, ?_⟩
    rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    change ‖c • F.toFun z‖ ≤ ‖c‖ * M
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hM (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hz))) (norm_nonneg c)
  lower_boundary := fun t => by
    show c • F.toFun (realToLower t) = ω ((c • a) * α.evolve t b)
    rw [F.lower_boundary, smul_mul_assoc, map_smul]
  upper_boundary := fun t => by
    show c • F.toFun (realToUpper β t) = ω (α.evolve t b * (c • a))
    rw [F.upper_boundary, mul_smul_comm, map_smul]

/-- The canonical two-point continuation is **additive in the right slot**: any KMS function for
`(a, b₁ + b₂)` agrees on the closed strip with the sum of those for `(a, b₁)` and `(a, b₂)`. -/
lemma KMSFunction.eqOn_add_right {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    {a b₁ b₂ : A} (F₁ : KMSFunction ω α β a b₁) (F₂ : KMSFunction ω α β a b₂)
    (H : KMSFunction ω α β a (b₁ + b₂)) :
    Set.EqOn H.toFun (fun z => F₁.toFun z + F₂.toFun z) (ClosedStrip β) :=
  KMSFunction.unique hβ H (F₁.add F₂)

/-- The canonical two-point continuation is **homogeneous in the right slot**: any KMS function
for `(a, c • b)` agrees on the closed strip with `c •` the one for `(a, b)`. -/
lemma KMSFunction.eqOn_smul_right {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    {a b : A} (c : ℂ) (F : KMSFunction ω α β a b) (H : KMSFunction ω α β a (c • b)) :
    Set.EqOn H.toFun (fun z => c • F.toFun z) (ClosedStrip β) :=
  KMSFunction.unique hβ H (F.smul c)

/-- The canonical two-point continuation is **additive in the left slot**. -/
lemma KMSFunction.eqOn_add_left {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    {a₁ a₂ b : A} (F₁ : KMSFunction ω α β a₁ b) (F₂ : KMSFunction ω α β a₂ b)
    (H : KMSFunction ω α β (a₁ + a₂) b) :
    Set.EqOn H.toFun (fun z => F₁.toFun z + F₂.toFun z) (ClosedStrip β) :=
  KMSFunction.unique hβ H (F₁.addLeft F₂)

/-- The canonical two-point continuation is **homogeneous in the left slot**. -/
lemma KMSFunction.eqOn_smul_left {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    {a b : A} (c : ℂ) (F : KMSFunction ω α β a b) (H : KMSFunction ω α β (c • a) b) :
    Set.EqOn H.toFun (fun z => c • F.toFun z) (ClosedStrip β) :=
  KMSFunction.unique hβ H (F.smulLeft c)

/-! ## Conjugation Symmetry of the Two-Point Function

The KMS function of `(a, b)` is the *conjugate reflection* of the KMS function of
`(star a, star b)`. The reflection `z ↦ conj z + iβ` is the strip's boundary-swapping
antiholomorphic involution; conjugating its pullback turns the upper boundary of `(star a, star b)`
into the lower boundary of `(a, b)` and vice versa, using hermiticity of `ω` (`State.star_apply`)
and that `α_t` is a `*`-automorphism (`kms_correlation_conj`).
-/

/-- The imaginary part of the boundary-swapping reflection `z ↦ conj z + iβ`. -/
private lemma reflect_im (β : ℝ) (z : ℂ) : (conj z + (β : ℂ) * I).im = β - z.im := by
  simp only [Complex.add_im, Complex.conj_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  ring

/-- The open strip is open. -/
private lemma isOpen_Strip (β : ℝ) : IsOpen (Strip β) :=
  (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)

/-- **Conjugate reflection of a KMS function.** Given a KMS function `H` for the pair
`(star a, star b)`, the function `z ↦ conj (H (conj z + iβ))` is a KMS function for `(a, b)`.
The reflection `z ↦ conj z + iβ` maps the strip to itself, swapping its two boundary lines. -/
noncomputable def KMSFunction.starReflect {ω : State A} {α : Dynamics A} {β : ℝ} {a b : A}
    (H : KMSFunction ω α β (star a) (star b)) :
    KMSFunction ω α β a b where
  toFun := fun z => conj (H.toFun (conj z + (β : ℂ) * I))
  holomorphic := by
    intro z hz
    obtain ⟨hz0, hzβ⟩ := hz
    have hcz : conj z + (β : ℂ) * I ∈ Strip β := by
      refine ⟨?_, ?_⟩ <;> rw [reflect_im] <;> linarith
    have hshift : DifferentiableAt ℂ (fun w => w + (β : ℂ) * I) (conj z) :=
      differentiableAt_id.add_const _
    have hHat : DifferentiableAt ℂ H.toFun (conj z + (β : ℂ) * I) :=
      H.holomorphic.differentiableAt ((isOpen_Strip β).mem_nhds hcz)
    have hf : DifferentiableAt ℂ (fun w => H.toFun (w + (β : ℂ) * I)) (conj z) :=
      hHat.comp (conj z) hshift
    have hd := DifferentiableAt.conj_conj hf
    rw [Complex.conj_conj] at hd
    exact hd.differentiableWithinAt
  continuousOn := by
    have hmaps : Set.MapsTo (fun z => conj z + (β : ℂ) * I) (ClosedStrip β) (ClosedStrip β) := by
      intro z hz
      obtain ⟨hz0, hzβ⟩ := hz
      refine ⟨?_, ?_⟩ <;> rw [reflect_im] <;> linarith
    have hcont_inner :
        ContinuousOn (fun z => H.toFun (conj z + (β : ℂ) * I)) (ClosedStrip β) :=
      H.continuousOn.comp ((Complex.continuous_conj.add continuous_const).continuousOn) hmaps
    exact Complex.continuous_conj.comp_continuousOn hcont_inner
  bounded := by
    obtain ⟨M, hM⟩ := H.bounded
    refine ⟨M, ?_⟩
    rintro y ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨hz0, hzβ⟩ := hz
    have hmem : conj z + (β : ℂ) * I ∈ ClosedStrip β := by
      refine ⟨?_, ?_⟩ <;> rw [reflect_im] <;> linarith
    change ‖conj (H.toFun (conj z + (β : ℂ) * I))‖ ≤ M
    rw [starRingEnd_apply, norm_star]
    exact hM (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hmem))
  lower_boundary := fun t => by
    show conj (H.toFun (conj (realToLower t) + (β : ℂ) * I)) = ω (a * α.evolve t b)
    have harg : conj (realToLower t) + (β : ℂ) * I = realToUpper β t := by
      simp [realToLower, realToUpper, Complex.conj_ofReal]
    rw [harg, H.upper_boundary, kms_correlation_conj ω α t a b, starRingEnd_apply]
  upper_boundary := fun t => by
    show conj (H.toFun (conj (realToUpper β t) + (β : ℂ) * I)) = ω (α.evolve t b * a)
    have harg : conj (realToUpper β t) + (β : ℂ) * I = realToLower t := by
      simp only [realToUpper, realToLower, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have halg : star (star a * α.evolve t (star b)) = α.evolve t b * a := by
      rw [star_mul, ← α.map_star t (star b), star_star, star_star]
    rw [harg, H.lower_boundary, starRingEnd_apply, ← ω.star_apply, halg]

/-- **Conjugation symmetry of the two-point function.** On the closed strip the canonical
two-point continuation for `(a, b)` equals the conjugate reflection of the one for
`(star a, star b)`:  `F_{a,b}(z) = conj (F_{a⋆,b⋆}(conj z + iβ))`. -/
lemma KMSFunction.eqOn_starReflect {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    {a b : A} (F : KMSFunction ω α β a b) (H : KMSFunction ω α β (star a) (star b)) :
    Set.EqOn F.toFun (fun z => conj (H.toFun (conj z + (β : ℂ) * I))) (ClosedStrip β) :=
  KMSFunction.unique hβ F H.starReflect

/-! ## Three-Lines Bound for KMS Correlations -/

/-- **Hadamard three-lines bound for KMS two-point functions.**

The analytic two-point function `F_{a,b}` of a KMS state is bounded on the closed strip by the
logarithmically convex interpolation of its two edge suprema — the suprema of the boundary
correlations `t ↦ ‖ω(a · α_t b)‖` (lower edge `Im = 0`) and `t ↦ ‖ω(α_t b · a)‖` (upper edge
`Im = β`):

`‖F z‖ ≤ (sup_t ‖ω(a · α_t b)‖) ^ ((β − Im z)/β) · (sup_t ‖ω(α_t b · a)‖) ^ (Im z/β)`.

A maximum principle for thermal correlations: the value inside the strip cannot exceed the
interpolation of the boundary correlations. This is the KMS-level payoff of
`Spectra.ThreeLines.hadamard_three_lines_horizontal`. -/
lemma KMSFunction.norm_le_threeLines
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β) {a b : A}
    (F : KMSFunction ω α β a b) {z : ℂ} (hz : z ∈ ClosedStrip β) :
    ‖F.toFun z‖ ≤
      sSup (Set.range fun t : ℝ => ‖ω (a * α.evolve t b)‖) ^ ((β - z.im) / β) *
      sSup (Set.range fun t : ℝ => ‖ω (α.evolve t b * a)‖) ^ (z.im / β) := by
  -- Identify the boundary-line images of ‖F‖ with the ranges of the boundary correlations.
  have hlow : (norm ∘ F.toFun) '' (Complex.im ⁻¹' {(0 : ℝ)})
      = Set.range fun t : ℝ => ‖ω (a * α.evolve t b)‖ := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      have hwre : realToLower w.re = w := by apply Complex.ext <;> simp [realToLower, hw]
      refine ⟨w.re, ?_⟩
      change ‖ω (a * α.evolve w.re b)‖ = ‖F.toFun w‖
      rw [← F.lower_boundary w.re, hwre]
    · rintro ⟨t, rfl⟩
      refine ⟨realToLower t, by simp [realToLower], ?_⟩
      change ‖F.toFun (realToLower t)‖ = ‖ω (a * α.evolve t b)‖
      rw [F.lower_boundary]
  have hup : (norm ∘ F.toFun) '' (Complex.im ⁻¹' {β})
      = Set.range fun t : ℝ => ‖ω (α.evolve t b * a)‖ := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      have hwre : realToUpper β w.re = w := by apply Complex.ext <;> simp [realToUpper, hw]
      refine ⟨w.re, ?_⟩
      change ‖ω (α.evolve w.re b * a)‖ = ‖F.toFun w‖
      rw [← F.upper_boundary w.re, hwre]
    · rintro ⟨t, rfl⟩
      refine ⟨realToUpper β t, by simp [realToUpper], ?_⟩
      change ‖F.toFun (realToUpper β t)‖ = ‖ω (α.evolve t b * a)‖
      rw [F.upper_boundary]
  have key := Spectra.ThreeLines.hadamard_three_lines_horizontal F.toFun hβ
    F.holomorphic F.continuousOn F.bounded z hz
  rwa [hlow, hup] at key

/-! ## The Special KMS Function for (1, a) -/

/-- For a KMS function witnessing the pair (1, a), both boundaries give ω(α_t(a)).
This is the key observation that enables the invariance proof. -/
lemma kms_function_one_boundaries_agree
    {ω : State A} {α : Dynamics A} {β : ℝ} {a : A}
    (F : KMSFunction ω α β 1 a) (t : ℝ) :
    F.toFun (realToLower t) = F.toFun (realToUpper β t) := by
  rw [F.lower_boundary, F.upper_boundary]
  -- Lower: ω(1 * α_t(a)) = ω(α_t(a))
  -- Upper: ω(α_t(a) * 1) = ω(α_t(a))
  simp only [one_mul, mul_one]


/-! ## The Main Invariance Theorem -/

/-- **KMS states are time-invariant.**

If ω is a KMS state at inverse temperature β with respect to dynamics α,
then ω(α_t(a)) = ω(a) for all t ∈ ℝ and a ∈ A.

**Proof outline:**
1. Get the KMS function F for pair (1, a)
2. Both boundaries give ω(α_t(a)), so F(t) = F(t + iβ)
3. Extend F periodically to get a bounded entire function G
4. By Liouville's theorem, G is constant
5. Therefore ω(α_t(a)) = G(t) = G(0) = ω(a)
-/
lemma IsKMSState.isInvariant
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    (h : IsKMSState ω α β) :
    IsInvariant ω α := by
  intro t a
  -- Get the KMS function for (1, a)
  obtain ⟨F⟩ := h 1 a
  -- The boundaries agree
  have boundary_match : ∀ s : ℝ, F.toFun (realToLower s) = F.toFun (realToUpper β s) :=
    kms_function_one_boundaries_agree F
  -- Extend to a bounded entire function
  obtain ⟨G, G_diff, G_bdd, G_extends⟩ := periodic_strip_extension
    F.toFun hβ F.holomorphic F.continuousOn F.bounded boundary_match
  -- By Liouville, G is constant
  have G_const : ∀ z w : ℂ, G z = G w :=
    fun z w => G_diff.apply_eq_apply_of_bounded G_bdd z w
  -- Connect back to ω
  calc ω (α.evolve t a)
      = F.toFun (realToLower t) := by rw [F.lower_boundary]; simp [one_mul]
    _ = G (realToLower t) := (G_extends (realToLower t) (by
        simp only [ClosedStrip, realToLower, mem_setOf_eq, ofReal_im]
        exact ⟨le_refl 0, le_of_lt hβ⟩)).symm
    _ = G (realToLower 0) := by
        simp only [realToLower]
        exact G_const t 0
    _ = F.toFun (realToLower 0) := G_extends (realToLower 0) (by
        simp only [ClosedStrip, realToLower, mem_setOf_eq, ofReal_zero, zero_im]
        exact ⟨le_refl 0, le_of_lt hβ⟩)
    _ = ω (α.evolve 0 a) := by rw [F.lower_boundary]; simp [one_mul]
    _ = ω a := by rw [α.evolve_zero]

/-- In a commutative algebra, the two KMS boundaries agree for ANY pair (a, b).

    Lower: F(t) = ω(a · α_t(b))
    Upper: F(t + iβ) = ω(α_t(b) · a) = ω(a · α_t(b)) = F(t)    [commutativity]

    This is the algebraic content of "the strip is a cylinder." -/
lemma kms_boundaries_agree_of_comm
    (hcomm : ∀ a b : A, a * b = b * a)
    {ω : State A} {α : Dynamics A} {β : ℝ} {a b : A}
    (F : KMSFunction ω α β a b) (t : ℝ) :
    F.toFun (realToLower t) = F.toFun (realToUpper β t) := by
  rw [F.lower_boundary, F.upper_boundary, hcomm]

/-- **The Cylinder Theorem.** If the algebra is commutative, every KMS function
    is constant on the closed strip.

    Commutativity kills the Möbius twist. The periodic extension is bounded
    and entire, so Liouville forces it to be constant.

    Physically: in classical (commutative) equilibrium, the two-point
    correlator ω(a · α_t(b)) carries no dynamical information — it equals
    ω(a · b) for all t. The state "sees no time." -/
lemma commutative_kms_correlations_constant
    (hcomm : ∀ a b : A, a * b = b * a)
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    (hkms : IsKMSState ω α β) :
    ∀ a b : A, ∀ t : ℝ, ω (a * α.evolve t b) = ω (a * b) := by
  intro a b t
  -- Get the KMS function for (a, b)
  obtain ⟨F⟩ := hkms a b
  -- Boundaries agree by commutativity
  have hperiod : ∀ s : ℝ, F.toFun (realToLower s) = F.toFun (realToUpper β s) :=
    kms_boundaries_agree_of_comm hcomm F
  -- F is constant on the strip (Liouville)
  obtain ⟨c, hc⟩ := periodic_strip_is_constant F.toFun hβ F.holomorphic
    F.continuousOn F.bounded hperiod
  -- Evaluate at t and at 0
  have ht : ω (a * α.evolve t b) = c := by
    rw [← F.lower_boundary t]
    exact hc (realToLower t)
      (LowerBoundary_subset_ClosedStrip (le_of_lt hβ) (realToLower_mem_LowerBoundary t))
  have h0 : ω (a * b) = c := by
    have := hc (realToLower 0)
      (LowerBoundary_subset_ClosedStrip (le_of_lt hβ) (realToLower_mem_LowerBoundary 0))
    rwa [F.lower_boundary, α.evolve_zero] at this
  exact ht.trans h0.symm  -- both equal c

/-- **Corollary**: A commutative KMS state is invariant. This follows from the
    cylinder theorem by taking `a = 1`. (Currently unused.) -/
lemma commutative_kms_is_invariant
    (hcomm : ∀ a b : A, a * b = b * a)
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    (hkms : IsKMSState ω α β) :
    IsInvariant ω α := by
  intro t a
  have := commutative_kms_correlations_constant hcomm hβ hkms 1 a t
  simp only [one_mul] at this
  exact this

end Spectra.KMS

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.KMS.Condition
import Mathlib.Analysis.VonNeumannAlgebra.Basic
/-!
# The Modular-KMS Interface: bundled hypotheses and time-rescaling

This file does **not** prove Takesaki's theorem. It defines the interface through which the
theorem will eventually be stated and consumed:

**Every faithful normal state on a von Neumann algebra is KMS at β = 1 with respect
to its modular automorphism group.**

**The modular flow IS thermal time evolution at temperature T = 1/k_B.**

Here that statement is packaged as the bundle `ModularTheoryData` (`kms_at_one` is a *field*,
not a proved theorem) — see `## Takesaki's theorem` below for exactly what is and is not
asserted. What this file *does* prove unconditionally is the KMS time-rescaling machinery:
given KMS at one inverse temperature, `IsKMSState.rescale` produces KMS at any other, via
reparametrized `Dynamics` (`Dynamics.rescale`) and reparametrized KMS functions
(`KMSFunction.rescaleGeneral`). Combined with a genuine `ModularTheoryData` construction (the
target of `Spectra.Modular.TomitaTakesaki`), this is the mathematical foundation of the "thermal
time hypothesis" in quantum gravity and the reason modular theory appears throughout quantum
field theory.

## What We Bundle as Hypotheses

Since the full Tomita-Takesaki theory requires:
- Von Neumann algebras (weak operator topology, preduals)
- Unbounded operators (densely defined, closed, polar decomposition)
- Cyclic and separating vectors
- The actual construction of Δ and J

We bundle:
1. `WStarAlgebra` (from Mathlib) - the property of being a von Neumann algebra, i.e. a
   C*-algebra with a Banach-space predual (Sakai's definition)
2. `IsFaithfulNormal` - the property of a state being faithful and normal
3. `ModularTheoryData` - the modular automorphism group, its invariance, and KMS

## References

* M. Tomita, "Quasi-standard von Neumann algebras" (1967, unpublished)
* M. Takesaki, "Tomita's theory of modular Hilbert algebras" (1970)
* O. Bratteli, D.W. Robinson, "Operator Algebras and Quantum Statistical Mechanics 2"
* A. Connes, "Noncommutative Geometry" (1994)
* S.J. Summers, "Tomita-Takesaki Modular Theory" (arXiv:math-ph/0511034)
-/

open Complex Set Filter Topology StarAlgebra
open Spectra.PeriodicHolomorphic

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

/-! ## Von Neumann Algebras

A von Neumann algebra is a C*-algebra that is also closed in the weak operator
topology (equivalently, equals its double commutant, or has a predual).

We use Mathlib's `WStarAlgebra` — Sakai's abstract definition of a von Neumann algebra
as a C*-algebra possessing a Banach-space predual (`WStarAlgebra.exists_predual`). This
replaces the previous placeholder class and gives the predual assumption real content.
-/

/-- A state is faithful if ω(a*a) = 0 implies a = 0.

The hypothesis is the equality `ω (star a * a) = 0` of *complex* numbers, but this is the same
condition as the usual positive-functional formulation `(ω (star a * a)).re = 0`: `State.nonneg`
already forces `ω (star a * a)` to lie in `{z : ℂ | 0 ≤ z}` (i.e. `0 ≤ z.re ∧ z.im = 0`), so its
real part vanishing and the complex number itself vanishing are equivalent for a state. -/
def State.IsFaithful (ω : State A) : Prop :=
  ∀ a : A, ω (star a * a) = 0 → a = 0

/-- A state is **normal** iff it is order-continuous: it preserves the suprema of bounded
increasing nets of positive elements.

This is the standard predual-free characterization of normality — equivalent, for a positive
functional on a von Neumann algebra, to σ-weak continuity and to complete additivity. Stating it
needs only the order `[PartialOrder A]` on `A` itself (to speak of `DirectedOn`/`IsLUB`), *not*
a chosen predual (which `WStarAlgebra.exists_predual` asserts only existentially) nor the
`WStarAlgebra`/`StarOrderedRing` structure — those are what make the predicate *meaningful* for a
von Neumann algebra, and are imposed at the call sites (`FaithfulNormalState`, `ModularTheoryData`)
rather than here. Discharging this predicate for concrete states — e.g. proving vector states
normal — is future work; the point of this definition is that normality is now an honest
restriction, not the vacuous `True` it used to be. -/
def State.IsNormal [PartialOrder A] (ω : State A) : Prop :=
  ∀ (s : Set A) (a : A),
    DirectedOn (· ≤ ·) s → (∀ x ∈ s, 0 ≤ x) → IsLUB s a →
      IsLUB ((fun x => (ω x).re) '' s) (ω a).re

/-- A faithful normal state. These are the states for which modular theory applies. -/
structure FaithfulNormalState (A : Type*) [CStarAlgebra A] [WStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    extends State A where
  faithful : toState.IsFaithful
  normal : toState.IsNormal

/-! ## The Modular Automorphism Group

The crown jewel of Tomita-Takesaki theory: every faithful normal state ω on a
von Neumann algebra M determines a canonical one-parameter automorphism group σ^ω,
called the modular automorphism group.

Construction (sketch):
1. GNS representation: (H_ω, π_ω, Ω_ω) with ω(a) = ⟨Ω_ω, π_ω(a)Ω_ω⟩
2. Ω_ω is cyclic (by GNS) and separating (by faithfulness)
3. Define S : π_ω(a)Ω_ω ↦ π_ω(a*)Ω_ω
4. S is closable; take polar decomposition S̄ = JΔ^{1/2}
5. The modular automorphism group is σ_t(a) = Δ^{it} a Δ^{-it}

Properties:
- σ_t is a *-automorphism for each t
- t ↦ σ_t is a group homomorphism
- t ↦ σ_t(a) is strongly continuous
- ω is σ-invariant: ω ∘ σ_t = ω
- ω satisfies KMS at β = 1 with respect to σ
-/

/-- Bundled data for the Tomita-Takesaki modular theory of a faithful normal state.

    Packages the modular automorphism group together with its two fundamental
    properties: state invariance and the KMS condition at β = 1.

    Construct this term once from a concrete Tomita-Takesaki construction
    (e.g. via `TomitaTakesaki.modularGroupBundle`); everything downstream
    lights up for free. -/
structure ModularTheoryData (A : Type*) [CStarAlgebra A] [WStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (ω : FaithfulNormalState A) where
  /-- The modular automorphism group σ^ω. -/
  dynamics : Dynamics A
  /-- ω is σ-invariant: ω ∘ σ_t = ω. -/
  invariant : IsInvariant ω.toState dynamics
  /-- ω satisfies KMS at β = 1 with respect to σ^ω. -/
  kms_at_one : IsKMSState ω.toState dynamics 1

/-- `σ[hmod]` extracts the modular automorphism group `Dynamics A` bundled in `hmod`. -/
notation:max "σ[" hmod "]" => ModularTheoryData.dynamics hmod

/-! ## Properties of the Modular Automorphism Group

These are now projections from `ModularTheoryData`, not global axioms.
-/

/-- Trivial accessor: the bundled invariance field of `hmod`. This is a *projection* of the
hypothesis `ModularTheoryData`, not a proof that invariant modular data exists. (Currently unused.)
-/
lemma modularAutomorphismGroup_invariant {A : Type*} [CStarAlgebra A] [WStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {ω : FaithfulNormalState A} (hmod : ModularTheoryData A ω) :
    IsInvariant ω.toState σ[hmod] :=
  hmod.invariant

/-- **Connes' cocycle theorem (Radon-Nikodym)**: If ω and φ are both faithful
normal states, their modular automorphism groups differ by a cocycle.

σ^φ_t = u_t σ^ω_t u_t* where u_t is a σ^ω-cocycle.

This means the modular flow is "almost unique" - unique up to inner automorphisms.
-/
structure ConnesCocycle {A : Type*} [CStarAlgebra A] [WStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {ω : FaithfulNormalState A} (hmod : ModularTheoryData A ω) (u : ℝ → A) where
  unitary : ∀ t, u t * star (u t) = 1 ∧ star (u t) * u t = 1
  cocycle_law : ∀ s t, u (s + t) = u s * σ[hmod].evolve s (u t)
  continuous : Continuous u

/-! ## Takesaki's theorem — the target, NOT yet a theorem here

Takesaki's theorem states that a faithful normal state `ω` is KMS at `β = 1` with respect to its
own modular automorphism group `σ^ω`. In this file that fact is available **only as the bundled
hypothesis** `ModularTheoryData.kms_at_one` — it is *assumed*, not proved.

There is deliberately **no** lemma `modular_state_is_kms` here: such a lemma would be a
content-free projection of `hmod.kms_at_one` dressed up as Takesaki's theorem, and
`ModularTheoryData` is currently uninhabited, so it would assert nothing about any actual state.
Callers that hold a `hmod` should write `hmod.kms_at_one` directly.

The genuine theorem is discharged only once `ModularTheoryData` is *constructed* from the
Tomita–Takesaki data — the modular operator `Δ` and the KMS function
`F_{a,b}(z) = ω(a · σ_z b)`, analytic on the strip `0 < Im z < 1` with
`F_{a,b}(t + i) = ω(σ_t(b) · a)` — which is the objective of the `tomitaTakesaki_exists`
construction. Until then this is an open target, not a result. -/

/-! ## Scaling: KMS at Arbitrary Temperature

The modular group gives KMS at β = 1. What about other temperatures?

If we rescale time: α_t = σ_{t/β}, then ω is KMS at inverse temperature β
with respect to α. This is just reparametrization.
-/

/-- Rescale dynamics by a factor. -/
def Dynamics.rescale (α : Dynamics A) (c : ℝ) : Dynamics A where
  evolve := fun t => α.evolve (c * t)
  map_mul := fun t a b => α.map_mul (c * t) a b
  map_one := fun t => α.map_one (c * t)
  map_star := fun t a => α.map_star (c * t) a
  evolve_add := fun s t a => by simp [mul_add, α.evolve_add]
  evolve_zero := fun a => by simp [α.evolve_zero]
  continuous_evolve := fun a => (α.continuous_evolve a).comp (continuous_const_mul c)

/-- Two dynamics agreeing on their evolution maps are equal: the remaining fields
are propositions, hence determined by proof irrelevance. -/
@[ext]
lemma Dynamics.ext {α α' : Dynamics A} (h : α.evolve = α'.evolve) : α = α' := by
  cases α; cases α'; subst h; rfl

/-- Rescaling by `1` is the identity: `σ_{1·t} = σ_t`. -/
@[simp]
lemma Dynamics.rescale_one (α : Dynamics A) : α.rescale 1 = α := by
  ext t; simp [Dynamics.rescale]

/-- Rescaling is multiplicative in the factor: rescaling by `c` then by `d`
equals rescaling by `c * d`. Together with `rescale_one` this makes time
reparametrization a multiplicative action on dynamics. -/
lemma Dynamics.rescale_rescale (α : Dynamics A) (c d : ℝ) :
    (α.rescale c).rescale d = α.rescale (c * d) := by
  ext t; simp [Dynamics.rescale, mul_assoc]

/-! ## Rescaling KMS States

The key lemma: if ω is KMS at β₁ for dynamics α, then ω is KMS at β₂ for the
rescaled dynamics α_{t·β₁/β₂}. This is just reparametrization of time.
-/

/-- Rescaling the strip: z ↦ z/β maps Strip β to Strip 1. (Currently unused.) -/
lemma strip_rescale_mem {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : z ∈ Strip β) :
    z / β ∈ Strip 1 := by
  simp only [Strip, mem_setOf_eq] at hz ⊢
  simp only [div_ofReal_im]
  constructor
  · exact div_pos hz.1 hβ
  · rw [div_lt_one hβ]
    exact hz.2

/-- Rescaling the closed strip. (Currently unused.) -/
lemma closedStrip_rescale_mem {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : z ∈ ClosedStrip β) :
    z / β ∈ ClosedStrip 1 := by
  simp only [ClosedStrip, mem_setOf_eq] at hz ⊢
  simp only [div_ofReal_im]
  constructor
  · exact div_nonneg hz.1 (le_of_lt hβ)
  · rw [div_le_one hβ]
    exact hz.2

/-- The inverse rescaling. -/
lemma strip_rescale_mem' {β : ℝ} (hβ : 0 < β) {w : ℂ} (hw : w ∈ Strip 1) :
    w * β ∈ Strip β := by
  simp only [Strip, mem_setOf_eq] at hw ⊢
  constructor
  · simp only [mul_im, ofReal_im, mul_zero, ofReal_re, zero_add]
    exact mul_pos hw.1 hβ
  · calc (w * β).im = w.im * β := by simp [mul_comm]
      _ < 1 * β := by exact mul_lt_mul_of_pos_right hw.2 hβ
      _ = β := one_mul β

/-- General rescaling: KMS function at β₁ → KMS function at β₂. -/
noncomputable def KMSFunction.rescaleGeneral {A : Type*} [CStarAlgebra A]
    {ω : State A} {α : Dynamics A} {a b : A} {β₁ : ℝ}
    (F : KMSFunction ω α β₁ a b) (β₂ : ℝ) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) :
    KMSFunction ω (α.rescale (β₁/β₂)) β₂ a b where
  toFun := fun z => F.toFun (z * (β₁ / β₂))
  holomorphic := by
    have _hc : (β₁ / β₂ : ℂ) ≠ 0 := by simp [ne_of_gt hβ₁, ne_of_gt hβ₂]
    have h1 : DifferentiableOn ℂ (fun z : ℂ => z * (β₁ / β₂ : ℂ)) (Strip β₂) :=
      differentiableOn_id.mul (differentiableOn_const _)
    have h2 : Set.MapsTo (fun z : ℂ => z * (β₁ / β₂ : ℂ)) (Strip β₂) (Strip β₁) := by
      intro z hz
      simp only [Strip, mem_setOf_eq] at hz ⊢
      simp only [mul_im, div_ofReal_im, ofReal_im, zero_div, mul_zero, div_ofReal_re, ofReal_re,
        zero_add]
      constructor
      · exact mul_pos hz.1 (div_pos hβ₁ hβ₂)
      · calc z.im * (β₁ / β₂) < β₂ * (β₁ / β₂) := by
                apply mul_lt_mul_of_pos_right hz.2 (div_pos hβ₁ hβ₂)
          _ = β₁ := by field_simp
    convert F.holomorphic.comp h1 h2 using 1
  continuousOn := by
    have h1 : ContinuousOn (fun z : ℂ => z * (β₁ / β₂ : ℂ)) (ClosedStrip β₂) :=
      continuousOn_id.mul continuousOn_const
    have h2 : Set.MapsTo (fun z : ℂ => z * (β₁ / β₂ : ℂ)) (ClosedStrip β₂) (ClosedStrip β₁) := by
      intro z hz
      simp only [ClosedStrip, mem_setOf_eq] at hz ⊢
      simp only [mul_im, div_ofReal_im, ofReal_im, zero_div, mul_zero, div_ofReal_re, ofReal_re,
        zero_add]
      constructor
      · exact mul_nonneg hz.1 (le_of_lt (div_pos hβ₁ hβ₂))
      · calc z.im * (β₁ / β₂) ≤ β₂ * (β₁ / β₂) := by
                apply mul_le_mul_of_nonneg_right hz.2 (le_of_lt (div_pos hβ₁ hβ₂))
          _ = β₁ := by field_simp
    convert F.continuousOn.comp h1 h2 using 1
  bounded := by
    obtain ⟨M, hM⟩ := F.bounded
    use M
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hz
    apply hM
    refine ⟨F.toFun (w * (β₁ / β₂)), ⟨w * (β₁ / β₂), ?_, rfl⟩, rfl⟩
    simp only [ClosedStrip, mem_setOf_eq] at hw ⊢
    simp only [mul_im, div_ofReal_im, ofReal_im, zero_div, mul_zero, div_ofReal_re, ofReal_re,
      zero_add]
    constructor
    · exact mul_nonneg hw.1 (le_of_lt (div_pos hβ₁ hβ₂))
    · calc w.im * (β₁ / β₂) ≤ β₂ * (β₁ / β₂) := by
              apply mul_le_mul_of_nonneg_right hw.2 (le_of_lt (div_pos hβ₁ hβ₂))
        _ = β₁ := by field_simp
  lower_boundary := by
    intro t
    have h1 : realToLower t * (β₁ / β₂ : ℂ) = realToLower (t * (β₁ / β₂)) := by
      simp only [realToLower, ofReal_mul, ofReal_div]
    rw [h1, F.lower_boundary]
    congr 2
    simp only [Dynamics.rescale]
    ring_nf
  upper_boundary := by
    intro t
    have hβ₂' : (β₂ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hβ₂)
    have h1 : realToUpper β₂ t * (β₁ / β₂ : ℂ) = realToUpper β₁ (t * (β₁ / β₂)) := by
      simp only [realToUpper, ofReal_mul, ofReal_div]
      field_simp
    rw [h1, F.upper_boundary]
    congr 2
    simp only [Dynamics.rescale]
    ring_nf

/-- Rescale a KMS function from temperature 1 to temperature β.

If F witnesses KMS at β = 1 for dynamics σ, then it rescales to a witness of KMS
at β for the rescaled dynamics α_t = σ_{t/β}. This is the special case `β₁ = 1`
of `KMSFunction.rescaleGeneral`. -/
noncomputable def KMSFunction.rescale {A : Type*} [CStarAlgebra A]
    {ω : State A} {σ : Dynamics A} {a b : A}
    (F : KMSFunction ω σ 1 a b) (β : ℝ) (hβ : 0 < β) :
    KMSFunction ω (σ.rescale (1/β)) β a b :=
  F.rescaleGeneral β one_pos hβ

/-- General rescaling theorem: KMS at β₁ implies KMS at β₂ for appropriately rescaled dynamics. -/
lemma IsKMSState.rescale {A : Type*} [CStarAlgebra A]
    {ω : State A} {α : Dynamics A} {β₁ : ℝ} (hβ₁ : 0 < β₁)
    (h : IsKMSState ω α β₁) (β₂ : ℝ) (hβ₂ : 0 < β₂) :
    IsKMSState ω (α.rescale (β₁/β₂)) β₂ := by
  intro a b
  obtain ⟨F⟩ := h a b
  exact ⟨F.rescaleGeneral β₂ hβ₁ hβ₂⟩

/-- **Given** modular theory data `hmod` for a faithful normal state `ω` (in particular its KMS@1
witness `hmod.kms_at_one`), `ω` is KMS at every inverse temperature `β > 0` for the rescaled
modular flow. This is a genuine reparametrization — real content is the strip rescaling
`KMSFunction.rescale` — but it is **conditional on `hmod`**; it does not assert that such `hmod`
exists. -/
lemma modular_state_is_kms_at_beta {A : Type*} [CStarAlgebra A] [WStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {ω : FaithfulNormalState A} (hmod : ModularTheoryData A ω)
    (β : ℝ) (hβ : 0 < β) :
    IsKMSState ω.toState (σ[hmod].rescale (1/β)) β := by
  intro a b
  obtain ⟨F⟩ := hmod.kms_at_one a b
  exact ⟨F.rescale β hβ⟩

end Spectra.KMS

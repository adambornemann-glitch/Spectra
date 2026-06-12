/-
Spectra: Cocycle.lean
The Connes cocycle: state-independence of the modular flow in Out(M),
the cocycle bundle, the chain rule, and Radon–Nikodym surjectivity.

Filename: ModularTheory/Cocycle.lean
Target: Mathlib master (2026-06-10)
-/
import Spectra.ModularTheory.RelativeModular
/-!
# The Connes Cocycle (Radon–Nikodym Theorem for von Neumann Algebras)

The cocycle identity and the intertwining theorem now live in
`RelativeModular.lean`, where both are **theorems** (the identity outright; the
intertwining given `RelativeTomitaTheorem`).  This file holds what is downstream
of them:

1. **State-independence in `Out(M)`** (`modular_flow_state_independent`): the
   modular automorphisms of any two states define the same class modulo inner
   automorphisms.  Was assembled from two hypothesis bundles
   (`IntertwiningData`, `SpatialDerivativeUnitarity`) in the old file; both are
   gone — unitarity is a theorem, intertwining is a theorem, and the only
   remaining inputs are the two fields of `RelativeTomitaTheorem`.
2. **The thermal time flow** `δ : ℝ → Out(M)` (`canonicalOuterFlow`,
   `thermalTimeFlow`), the Connes–Rovelli state-independent flow.
3. **`ModularCocycle`** — the abstract σ-cocycle bundle — and the capstone
   `spatialDerivativeCocycle`: every spatial derivative *is* a modular cocycle
   (unitarity, membership, cocycle law, `u_0 = 1`, strong continuity — all five
   discharged, the first/fourth/fifth by theorems).  This is the "easy
   direction" of Connes' Radon–Nikodym theorem, fully assembled.
4. **The chain rule** `(Dχ:Dφ)_t = (Dχ:Dψ)_t·(Dψ:Dφ)_t` and **surjectivity**
   (every σ-cocycle is a spatial derivative) as hypothesis bundles.
   Surjectivity is the hard half: the Connes inverse construction
   `ψ(a) = φ(u_{−i/2}† a u_{−i/2})` needs analytic continuation of the cocycle
   into the strip — exactly the PeriodicStrip machinery.

## References

* [Connes, "Une classification des facteurs de type III", Ann. Sci. ENS 6 (1973)]
* [Connes, "Sur le théorème de Radon-Nikodym pour les poids normaux fidèles
  semi-finis", Bull. Sci. Math. 97 (1973)]
* [Connes–Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics
  relation", gr-qc/9406019]
* [Takesaki, *Theory of Operator Algebras II*][takesaki2003], Ch. VIII, Thm. 3.3
-/
open Complex Filter Topology
open scoped InnerProductSpace
open Spectra.QuantumMechanics OneParameterUnitaryGroup
open Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.ModularTheory
/-!
## Section 1: Inner equivalence and Out(M)

Two maps `α, β : B(H) → B(H)` are inner-equivalent over `A` if they differ by
conjugation with a unitary of `A`.  `Out(M)` is the quotient.
-/

/-- Two automorphisms are *inner-equivalent* over `A` if they differ by
conjugation with a unitary `u ∈ A`. -/
def InnerEquivalent (α β : (H →L[ℂ] H) → (H →L[ℂ] H))
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ u : H →L[ℂ] H,
    u ∈ A ∧
    u * ContinuousLinearMap.adjoint u = 1 ∧
    ContinuousLinearMap.adjoint u * u = 1 ∧
    ∀ a ∈ A, β a = u * α a * ContinuousLinearMap.adjoint u

/-- Inner equivalence is reflexive (`u = 1`). -/
lemma innerEquivalent_refl (α : (H →L[ℂ] H) → (H →L[ℂ] H))
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    InnerEquivalent α α A := by
  refine ⟨1, one_mem _, ?_, ?_, fun a _ => ?_⟩ <;>
    simp only [adjoint_one, mul_one];
    exact ContinuousLinearMap.ext (congrFun rfl)


/-- Inner equivalence is symmetric: if `β = Ad(u)∘α` then `α = Ad(u†)∘β`. -/
lemma innerEquivalent_symm {α β : (H →L[ℂ] H) → (H →L[ℂ] H)}
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (h : InnerEquivalent α β A) :
    InnerEquivalent β α A := by
  obtain ⟨u, hu_mem, hu_l, hu_r, hu_eq⟩ := h
  refine ⟨ContinuousLinearMap.adjoint u, adjoint_mem hu_mem, ?_, ?_, fun a ha => ?_⟩
  · rw [ContinuousLinearMap.adjoint_adjoint]; exact hu_r
  · rw [ContinuousLinearMap.adjoint_adjoint]; exact hu_l
  · calc α a = 1 * α a * 1 := by rw [one_mul, mul_one]
      _ = (ContinuousLinearMap.adjoint u * u) * α a
            * (ContinuousLinearMap.adjoint u * u) := by rw [hu_r]
      _ = ContinuousLinearMap.adjoint u
            * (u * α a * ContinuousLinearMap.adjoint u) * u := by
          simp only [mul_assoc]
      _ = ContinuousLinearMap.adjoint u * β a * u := by rw [← hu_eq a ha]
      _ = ContinuousLinearMap.adjoint u * β a
            * ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint u) := by
          rw [ContinuousLinearMap.adjoint_adjoint]

/-- Inner equivalence is transitive: `Ad(v)∘Ad(u) = Ad(vu)`. -/
lemma innerEquivalent_trans {α β γ : (H →L[ℂ] H) → (H →L[ℂ] H)}
    {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (h₁ : InnerEquivalent α β A) (h₂ : InnerEquivalent β γ A) :
    InnerEquivalent α γ A := by
  obtain ⟨u, hu_mem, hu_l, hu_r, hu_eq⟩ := h₁
  obtain ⟨v, hv_mem, hv_l, hv_r, hv_eq⟩ := h₂
  refine ⟨v * u, mul_mem hv_mem hu_mem, ?_, ?_, fun a ha => ?_⟩
  · calc (v * u) * ContinuousLinearMap.adjoint (v * u)
        = v * (u * ContinuousLinearMap.adjoint u) * ContinuousLinearMap.adjoint v := by
          rw [adjoint_mul]; simp only [mul_assoc]
      _ = v * ContinuousLinearMap.adjoint v := by rw [hu_l, mul_one]
      _ = 1 := hv_l
  · calc ContinuousLinearMap.adjoint (v * u) * (v * u)
        = ContinuousLinearMap.adjoint u * (ContinuousLinearMap.adjoint v * v) * u := by
          rw [adjoint_mul]; simp only [mul_assoc]
      _ = ContinuousLinearMap.adjoint u * u := by rw [hv_r, mul_one]
      _ = 1 := hu_r
  · calc γ a = v * β a * ContinuousLinearMap.adjoint v := hv_eq a ha
      _ = v * (u * α a * ContinuousLinearMap.adjoint u)
            * ContinuousLinearMap.adjoint v := by rw [← hu_eq a ha]
      _ = (v * u) * α a * ContinuousLinearMap.adjoint (v * u) := by
          rw [adjoint_mul]; simp only [mul_assoc]

/-- Inner equivalence as a setoid; `Out(M)` is its quotient. -/
def innerEquivalentSetoid (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Setoid ((H →L[ℂ] H) → (H →L[ℂ] H)) :=
  ⟨fun α β => InnerEquivalent α β A,
    ⟨fun α => innerEquivalent_refl α A,
     fun h => innerEquivalent_symm h,
     fun h₁ h₂ => innerEquivalent_trans h₁ h₂⟩⟩

/-!
## Section 2: State-independence of the modular flow in Out(M)
-/

/-- **Connes' theorem: state-independence of the modular flow in `Out(M)`.**

For two faithful states on the same algebra, `σ_t^φ` and `σ_t^ψ` define the same
class modulo inner automorphisms, for every `t` — witnessed by the cocycle `u_t`,
whose unitarity and intertwining are theorems (`RelativeModular.lean`); the only
inputs are the two fields of `RelativeTomitaTheorem`. -/
theorem modular_flow_state_independent {D : TwoStateData H}
    (md_φ : ModularData H D.φ) (md_ψ : ModularData H D.ψ)
    (rel : RelativeModularData H D)
    (hRT : RelativeTomitaTheorem H D md_φ md_ψ rel) (t : ℝ) :
    InnerEquivalent (modularAutomorphism md_φ t) (modularAutomorphism md_ψ t)
      D.φ.algebra :=
  ⟨spatialDerivative md_φ rel t,
    hRT.cocycle_mem t,
    spatialDerivative_mul_adjoint md_φ rel t,
    spatialDerivative_adjoint_mul md_φ rel t,
    fun a ha => spatialDerivative_intertwines md_φ md_ψ rel hRT t a ha⟩

/-!
## Section 3: The canonical flow δ : ℝ → Out(M) (thermal time)
-/

/-- The outer-automorphism class of `σ_t^φ`.  By
`modular_flow_state_independent` this class does not depend on the state. -/
noncomputable def canonicalOuterFlow {M : VNAlgebraWithVector H}
    (md : ModularData H M) (t : ℝ) :
    Quotient (innerEquivalentSetoid M.algebra) :=
  Quotient.mk _ (modularAutomorphism md t)

/-- The canonical flow respects the group law (pointwise form):
`[σ_{s+t}] = [σ_s ∘ σ_t]` in `Out(M)`. -/
theorem canonicalOuterFlow_group_law {M : VNAlgebraWithVector H}
    (md : ModularData H M) (s t : ℝ) :
    canonicalOuterFlow md (s + t)
      = Quotient.mk (innerEquivalentSetoid M.algebra)
          (fun a => modularAutomorphism md s (modularAutomorphism md t a)) := by
  simp only [canonicalOuterFlow]
  congr 1
  funext a
  exact modularAutomorphism_group_law md s t a

/-- **The thermal time flow** of `(M, Ω)` — the state-independent one-parameter
family of outer automorphism classes (Connes–Rovelli).  The mathematical content
of the thermal time hypothesis: the algebra alone determines the flow of time,
up to the gauge freedom of inner automorphisms. -/
noncomputable def thermalTimeFlow {M : VNAlgebraWithVector H}
    (md : ModularData H M) : ℝ → Quotient (innerEquivalentSetoid M.algebra) :=
  canonicalOuterFlow md

/-!
## Section 4: The cocycle bundle, and the spatial derivative as a cocycle
-/

/-- A σ-cocycle: a strongly continuous unitary-valued 1-cocycle for the modular
automorphism group of `(M, md)`. -/
structure ModularCocycle (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VNAlgebraWithVector H) (md : ModularData H M) where
  /-- The cocycle values. -/
  u : ℝ → H →L[ℂ] H
  /-- Each `u_t` is unitary. -/
  isUnitary : ∀ t : ℝ,
    u t * ContinuousLinearMap.adjoint (u t) = 1 ∧
    ContinuousLinearMap.adjoint (u t) * u t = 1
  /-- Each `u_t ∈ M`. -/
  mem_algebra : ∀ t : ℝ, u t ∈ M.algebra
  /-- The cocycle identity `u_{s+t} = u_s · σ_s(u_t)`. -/
  cocycle_law : ∀ s t : ℝ, u (s + t) = u s * modularAutomorphism md s (u t)
  /-- `u_0 = 1`. -/
  at_zero : u 0 = 1
  /-- Strong continuity: `t ↦ u_tψ` is continuous for every `ψ`. -/
  strongly_continuous : ∀ ψ : H, Continuous fun t => u t ψ

/-- **The spatial derivative is a modular cocycle** — the assembled "easy
direction" of Connes' Radon–Nikodym theorem.  All five obligations are
discharged: unitarity, the cocycle law, `u_0 = 1` and strong continuity are
theorems of `RelativeModular.lean`; membership is `hRT.cocycle_mem`. -/
noncomputable def spatialDerivativeCocycle {D : TwoStateData H}
    (md_φ : ModularData H D.φ) (md_ψ : ModularData H D.ψ)
    (rel : RelativeModularData H D)
    (hRT : RelativeTomitaTheorem H D md_φ md_ψ rel) :
    ModularCocycle H D.φ md_φ where
  u := spatialDerivative md_φ rel
  isUnitary t := ⟨spatialDerivative_mul_adjoint md_φ rel t,
    spatialDerivative_adjoint_mul md_φ rel t⟩
  mem_algebra := hRT.cocycle_mem
  cocycle_law := connes_cocycle_identity md_φ rel
  at_zero := spatialDerivative_zero md_φ rel
  strongly_continuous := spatialDerivative_strongly_continuous md_φ rel

/-!
## Section 5: The chain rule (transitivity of the cocycle)

`(Dχ : Dφ)_t = (Dχ : Dψ)_t · (Dψ : Dφ)_t` — the noncommutative chain rule
`dχ/dφ = (dχ/dψ)·(dψ/dφ)`.  Hypothesis bundle: the proof needs the
factorization of relative modular operators (balanced weights).
-/

/-- Three states on the same algebra. -/
structure ThreeStateData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The first state φ. -/
  φ : VNAlgebraWithVector H
  /-- The second state ψ. -/
  ψ : VNAlgebraWithVector H
  /-- The third state χ. -/
  χ : VNAlgebraWithVector H
  /-- φ and ψ live on the same algebra. -/
  same_algebra_φψ : φ.algebra = ψ.algebra
  /-- ψ and χ live on the same algebra. -/
  same_algebra_ψχ : ψ.algebra = χ.algebra

namespace ThreeStateData

variable (T : ThreeStateData H)

/-- The `(φ, ψ)` pair. -/
def toφψ : TwoStateData H := ⟨T.φ, T.ψ, T.same_algebra_φψ⟩

/-- The `(ψ, χ)` pair. -/
def toψχ : TwoStateData H := ⟨T.ψ, T.χ, T.same_algebra_ψχ⟩

/-- The `(φ, χ)` pair. -/
def toφχ : TwoStateData H := ⟨T.φ, T.χ, T.same_algebra_φψ.trans T.same_algebra_ψχ⟩

end ThreeStateData

/-- **The chain rule for Connes cocycles**, as a hypothesis bundle:
`(Dχ : Dφ)_t = (Dχ : Dψ)_t · (Dψ : Dφ)_t`. -/
structure ChainRuleData (T : ThreeStateData H)
    (md_φ : ModularData H T.φ) (md_ψ : ModularData H T.ψ)
    (rel_φψ : RelativeModularData H T.toφψ)
    (rel_ψχ : RelativeModularData H T.toψχ)
    (rel_φχ : RelativeModularData H T.toφχ) : Prop where
  /-- `(Dχ : Dφ)_t = (Dχ : Dψ)_t · (Dψ : Dφ)_t`. -/
  chain_rule : ∀ t : ℝ,
    spatialDerivative md_φ rel_φχ t
      = spatialDerivative md_ψ rel_ψχ t * spatialDerivative md_φ rel_φψ t

/-!
## Section 6: Radon–Nikodym surjectivity (the hard direction)

Every σ^φ-cocycle arises as `(Dψ : Dφ)_t` for some faithful state ψ
([Connes 1973, Thm. 1.2.4]).  The proof is the Connes inverse construction
`ψ(a) = φ(u_{−i/2}† a u_{−i/2})`, requiring analytic continuation of the cocycle
to imaginary time — the PeriodicStrip/KMS machinery.  Until that is built, this
is the surviving deep hypothesis of the development.
-/

/-- **Radon–Nikodym surjectivity** as a hypothesis bundle: a witness that the
cocycle `c` is the spatial derivative of some second state. -/
structure RadonNikodymSurjectivity (M : VNAlgebraWithVector H)
    (md : ModularData H M) (c : ModularCocycle H M md) where
  /-- The two-state data witnessing the cocycle as a spatial derivative. -/
  twoState : TwoStateData H
  /-- Modular data for the base state of `twoState`. -/
  mdBase : ModularData H twoState.φ
  /-- The relative modular data. -/
  relModular : RelativeModularData H twoState
  /-- The base state matches `M`. -/
  base_eq : twoState.φ = M
  /-- The cocycle equals the spatial derivative. -/
  is_spatial : ∀ t : ℝ, c.u t = spatialDerivative mdBase relModular t

/-!
## Hypothesis inventory after this rebuild

Theorems now (were hypotheses or absent):
* cocycle unitarity, `u_0 = 1`, strong continuity of `t ↦ u_tψ`;
* the cocycle identity (`connes_cocycle_identity`);
* the intertwining theorem (given `RelativeTomitaTheorem`);
* state-independence in `Out(M)` (given `RelativeTomitaTheorem`);
* the spatial derivative as a `ModularCocycle` (`spatialDerivativeCocycle`).

Remaining hypotheses, ordered by depth:
1. `ModularData` / `RelativeModularData` — polar decomposition of the closed
   (anti)linear operators; closability is proved, the closure construction and
   the polar decomposition are the next milestone.
2. `TomitaTheorem` / `RelativeTomitaTheorem` — Tomita's theorem and its relative
   form (`conjugation_eq`, `cocycle_mem`).
3. `ChainRuleData` — factorization of relative modular operators.
4. `RadonNikodymSurjectivity` — Connes' inverse construction; needs the
   PeriodicStrip analytic continuation (`u_{−i/2}`).
-/

end Spectra.QuantumMechanics.ModularTheory

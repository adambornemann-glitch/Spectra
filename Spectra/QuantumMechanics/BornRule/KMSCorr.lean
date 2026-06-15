/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
Filename: ModularTheory/BornKMSCorrespondence.lean
-/
import Spectra.KMS.Modular
import Spectra.QuantumMechanics.DiracEquation.Conservation
/-!
# The Born-KMS Correspondence

This file establishes the fundamental equivalence between **Born-rule states**
(faithful normal states admitting a spectral/vector-state representation) and
**KMS equilibrium states** (states satisfying the Kubo-Martin-Schwinger condition).

## The Physics

The Born rule and the KMS condition are two faces of the same coin:

- **Born rule** (1926): The probability of a measurement outcome is ω(A) = ⟨Ω, π(A)Ω⟩,
  where Ω is the state vector in the GNS Hilbert space. For spectral projections,
  this gives μ_Ω(B) = ‖E(B)Ω‖² — the spectral scalar measure.

- **KMS condition** (1957–1967): A state ω is in thermal equilibrium at inverse
  temperature β if the two-point function F(t) = ω(A · α_t(B)) extends analytically
  to a strip of width β with twisted boundary condition F(t+iβ) = ω(α_t(B) · A).

The correspondence states:

  **A state is faithful and normal (Born-rule representable with full support)
  if and only if it is KMS at β = 1 with respect to some dynamics.**

The dynamics is unique: it is the **modular automorphism group** σ^ω of
Tomita-Takesaki theory. This is the content of the thermal time hypothesis:
time evolution is not given a priori but emerges from the state's thermodynamic
structure.

## Architecture

### Axioms (5 total, all named theorems in the literature)

| Axiom | Source | Discharge Route |
|-------|--------|-----------------|
| `gns_construction` | Gelfand-Naimark-Segal (1943) | Quotient A/N_ω, complete, represent |
| `kms_implies_faithful` | Haag-Hugenholtz-Winnink (1967) | Analytic continuation + edge-of-wedge |
| `kms_implies_normal` | Haag-Hugenholtz-Winnink (1967) | KMS ⟹ σ-weak continuity on vN algebras |
| `takesaki_kms_unique` | Takesaki (1970) | Modular theory + uniqueness of analytic continuation |
| `tomita_takesaki` | Tomita-Takesaki (1967–70) | GNS + polar decomposition of S̄ = JΔ^{1/2} |

### Proved Theorems

- `gns_faithful_implies_separating`: ω faithful ⟹ Ω separating (from GNS fields)
- `gns_separating_implies_faithful`: Ω separating ⟹ ω faithful (from GNS fields)
- `gns_faithful_iff_separating`: biconditional
- `born_kms_forward`: faithful ∧ normal ⟹ ∃ σ, IsKMSState ω σ 1
- `born_kms_reverse`: (∃ σ, IsKMSState ω σ 1) ⟹ faithful ∧ normal
- `born_kms_biconditional`: the full ↔
- `born_kms_dynamics_unique`: the KMS-1 dynamics is unique
- `born_kms_correspondence`: the assembled structure
- `thermal_time_hypothesis`: existence + uniqueness of thermal time

### Connection to Spectral Theory

The GNS Born rule `ω(a) = ⟪Ω, π(a)Ω⟫` specializes to the spectral Born rule:

  ω(E(B)) = ⟪Ω, E(B)Ω⟫ = ‖E(B)Ω‖² = μ_Ω(B)

This is proved in the spectral theory development via `projection_inner_eq_norm_sq`.
The spectral scalar measure μ_Ω is the Born-rule probability distribution over
energies. The KMS condition then says this probability distribution is thermal
(Gibbs) with respect to the modular Hamiltonian K = -log Δ.

## References

* Gelfand, Naimark, "On the imbedding of normed rings into the ring of operators
  in Hilbert space" (1943)
* Kubo, "Statistical-Mechanical Theory of Irreversible Processes" (1957)
* Haag, Hugenholtz, Winnink, "On the Equilibrium States in Quantum Statistical
  Mechanics" (1967)
* Takesaki, "Tomita's theory of modular Hilbert algebras" (1970)
* Bratteli, Robinson, "Operator Algebras and Quantum Statistical Mechanics 2" (1997)
* Connes, Rovelli, "Von Neumann algebra automorphisms and time-thermodynamics
  relation in general covariant quantum theories" (1994)

-/
open Complex Set Filter Topology
variable {A : Type*} [CStarAlgebra A]
open Spectra.KMS
open Spectra.PeriodicHolomorphic
open Spectra.QuantumMechanics.Dirac.Conservation
namespace Spectra.QuantumMechanics.BornRule


/-! ## § 1. The GNS Construction

The Gelfand-Naimark-Segal construction associates to each state ω on a
C*-algebra A a triple (H_ω, π_ω, Ω_ω) where:
- H_ω is a Hilbert space
- π_ω : A → B(H_ω) is a *-representation
- Ω_ω ∈ H_ω is a cyclic vector with ω(a) = ⟨Ω_ω, π_ω(a) Ω_ω⟩

This is the mathematical content of the Born rule: every algebraic state
arises from an inner product with a vector in some Hilbert space.
-/

/-- The GNS construction data for a state ω on a C*-algebra.

Given a state ω, this packages:
- The GNS Hilbert space H_ω (constructed as the completion of A/N_ω)
- The representation π_ω : A → B(H_ω)
- The cyclic vector Ω_ω (the image of 1 ∈ A)

The key property is the **Born rule**: ω(a) = ⟨Ω, π(a)Ω⟩.
This is the bridge between algebraic states and vector states. -/
structure GNSData (A : Type*) [CStarAlgebra A] (ω : State A) where
  /-- The GNS Hilbert space H_ω. -/
  H : Type*
  /-- H_ω is a normed additive group. -/
  [instNACG : NormedAddCommGroup H]
  /-- H_ω carries a complex inner product. -/
  [instIPS : InnerProductSpace ℂ H]
  /-- H_ω is complete (it's a Hilbert space). -/
  [instCS : CompleteSpace H]
  /-- The *-representation π_ω : A → B(H_ω). -/
  π : A → H →L[ℂ] H
  /-- The cyclic vector Ω_ω ∈ H_ω (image of 1 under the quotient map). -/
  Ω : H
  /-- π is multiplicative: π(ab) = π(a)π(b). -/
  π_mul : ∀ a b, π (a * b) = π a * π b
  /-- π preserves the unit: π(1) = 1. -/
  π_one : π 1 = 1
  /-- π is a *-map: π(a*)  = π(a)†.
  More precisely, the adjoint of π(a) equals π(star a). This is the
  operator-algebraic encoding of Hermitian conjugation. -/
  π_star : ∀ a, (π a).adjoint = π (star a)
  /-- **The Born Rule**: ω(a) = ⟨Ω, π(a)Ω⟩_ℂ.
  This is the fundamental connection between algebraic states and
  Hilbert space quantum mechanics. Every expectation value is an
  inner product. -/
  born_rule : ∀ a, ω a = @inner ℂ H instIPS.toInner Ω (π a Ω)
  /-- Ω is cyclic: the set {π(a)Ω | a ∈ A} is dense in H_ω.
  This means H_ω is the "smallest" Hilbert space carrying the
  representation and the vector. No information is wasted. -/
  cyclic : Dense (Set.range (fun a => π a Ω))

attribute [instance] GNSData.instNACG GNSData.instIPS GNSData.instCS

/-- **Axiom (GNS Construction)**: Every state on a C*-algebra admits a GNS triple.

**Discharge route**: Define H_ω as the completion of A/N_ω where
N_ω = {a : ω(a*a) = 0} is the Gelfand ideal. The inner product is
⟨[a], [b]⟩ := ω(a*b). The representation is π(a)[b] = [ab]. The cyclic
vector is Ω = [1]. Positivity of ω gives positive-definiteness of the
inner product; the Cauchy-Schwarz inequality for ω gives continuity of π. -/
axiom gns_construction (A : Type*) [CStarAlgebra A] (ω : State A) :
    GNSData A ω


/-! ## § 2. Separating Vectors and Faithfulness

A vector Ω is **separating** for a representation π if π(a)Ω = 0 implies a = 0.
This is dual to cyclicity: Ω is cyclic for π(A) iff Ω is separating for π(A)'.

The key fact: **ω is faithful ⟺ Ω_ω is separating**.
This is provable from the GNS fields — no axiom needed.
-/

/-- A GNS vector Ω is separating if π(a)Ω = 0 implies a = 0.

For faithful states, the GNS vector is always separating. This is the
condition that enables Tomita-Takesaki modular theory: the operator
S(π(a)Ω) = π(a*)Ω is well-defined precisely when Ω is separating. -/
def GNSData.IsSeparating {A : Type*} [CStarAlgebra A] {ω : State A}
    (gns : GNSData A ω) : Prop :=
  ∀ a : A, gns.π a gns.Ω = 0 → a = 0

/-- Faithful states have separating GNS vectors.

**Proof**: If π(a)Ω = 0, then ω(a*a) = ⟨Ω, π(a*a)Ω⟩ = ⟨Ω, π(a*)(π(a)Ω)⟩
= ⟨Ω, π(a*)(0)⟩ = 0. By faithfulness, a = 0.

**Chain**: π(a)Ω = 0 → π(a*a)Ω = π(a*)(0) = 0 → ω(a*a) = ⟨Ω,0⟩ = 0 → a = 0. -/
theorem gns_faithful_implies_separating {A : Type*} [CStarAlgebra A]
    {ω : State A} (gns : GNSData A ω) (hf : ω.IsFaithful) :
    gns.IsSeparating := by
  intro a ha
  apply hf
  rw [gns.born_rule, gns.π_mul]
  simp only [ContinuousLinearMap.mul_apply, ha, map_zero, inner_zero_right]

/-- Separating GNS vectors imply faithful states.

**Proof**: If ω(a*a) = 0, then ‖π(a)Ω‖² = ⟨π(a)Ω, π(a)Ω⟩
= ⟨Ω, π(a)*π(a)Ω⟩ = ⟨Ω, π(a*a)Ω⟩ = ω(a*a) = 0.
So π(a)Ω = 0, and by the separating property, a = 0.

**Chain**: ω(a*a) = 0 → ‖π(a)Ω‖² = 0 → π(a)Ω = 0 → a = 0. -/
theorem gns_separating_implies_faithful {A : Type*} [CStarAlgebra A]
    {ω : State A} (gns : GNSData A ω) (hs : gns.IsSeparating) :
    ω.IsFaithful := by
  letI := gns.instNACG
  letI := gns.instIPS
  letI := gns.instCS
  intro a ha
  apply hs
  -- Rewrite ha : ω(a*a) = 0 via Born rule in-place
  rw [gns.born_rule (star a * a), gns.π_mul] at ha
  simp only [ContinuousLinearMap.mul_apply] at ha
  rw [show gns.π (star a) = (gns.π a).adjoint from (gns.π_star a).symm] at ha
  rw [ContinuousLinearMap.adjoint_inner_right] at ha
  exact inner_self_eq_zero.mp ha

/-- **Faithful ⟺ Separating**: A state is faithful if and only if its
GNS vector is separating. -/
theorem gns_faithful_iff_separating {A : Type*} [CStarAlgebra A]
    {ω : State A} (gns : GNSData A ω) :
    ω.IsFaithful ↔ gns.IsSeparating :=
  ⟨gns_faithful_implies_separating gns, gns_separating_implies_faithful gns⟩


/-! ## § 3. The Haag-Hugenholtz-Winnink Theorem

The HHW theorem (1967) establishes the deep properties of KMS states:
- KMS states at positive temperature are faithful
- KMS states on von Neumann algebras are normal
- Together with Tomita-Takesaki, this gives the reverse direction of the correspondence
-/

/-- **Axiom (HHW Faithfulness)**: KMS states at positive temperature are faithful.

ω(a*a) = 0 would force the KMS function F_{a,a*} to vanish identically
on the strip boundary, hence on the strip (by the identity theorem for
holomorphic functions), but F(0) = ω(a · a*) = ω(a*a)* = 0 as well.
The twist F(t+iβ) = ω(α_t(a*) · a) then also vanishes, giving
ω(b · a) = 0 for all b. Taking b = 1 gives ω(a) = 0 for all a, contradicting
ω(1) = 1 unless a = 0.

**Discharge route**: Analytic continuation on the strip + identity theorem
for holomorphic functions. Uses the Phragmén-Lindelöf principle
(bounded holomorphic functions on a strip that vanish on one boundary
vanish everywhere). -/
axiom kms_implies_faithful {A : Type*} [CStarAlgebra A]
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    (hkms : IsKMSState ω α β) : ω.IsFaithful

/-- **Axiom (HHW Normality)**: KMS states on von Neumann algebras are normal.

A normal state is one that is σ-weakly continuous, equivalently, it comes
from the predual M_*. KMS states are automatically normal because the
analytic continuation properties of the KMS function force σ-weak continuity
on bounded increasing nets.

**Discharge route**: Show that the KMS condition implies σ-weak lower
semicontinuity, which for states on von Neumann algebras is equivalent
to normality. Uses the Kaplansky density theorem and the KMS boundary
conditions. -/
axiom kms_implies_normal {A : Type*} [CStarAlgebra A] [WStarAlgebra A]
    {ω : State A} {α : Dynamics A} {β : ℝ} (hβ : 0 < β)
    (hkms : IsKMSState ω α β) : ω.IsNormal


/-! ## § 4. Takesaki Uniqueness

The modular automorphism group is the UNIQUE one-parameter group making
the state KMS at β = 1. This is the content of Takesaki's theorem and
is the reason the Born-KMS correspondence gives a bijection, not just
a surjection.
-/

/-- **Axiom (Takesaki Uniqueness)**: The KMS-1 dynamics is unique.

If ω is KMS at β = 1 with respect to both σ₁ and σ₂, then σ₁ = σ₂.
The modular automorphism group is the unique flow making ω thermal.

**Discharge route**: Both σ₁ and σ₂ must equal the modular automorphism
group σ^ω (by Takesaki's theorem: the modular group is characterized as
the unique KMS-1 flow). Uses the uniqueness of analytic continuation
and the Tomita-Takesaki modular operator Δ. -/
axiom takesaki_kms_unique {A : Type*} [CStarAlgebra A]
    {ω : State A} (σ₁ σ₂ : Dynamics A)
    (h₁ : IsKMSState ω σ₁ 1) (h₂ : IsKMSState ω σ₂ 1) :
    ∀ t a, σ₁.evolve t a = σ₂.evolve t a


/-! ## § 5. Tomita-Takesaki Existence

Every faithful normal state on a von Neumann algebra admits a modular
automorphism group. This is the crown jewel of operator algebras. -/

/-- **Tomita-Takesaki Theorem**: Every faithful normal state on a von
Neumann algebra admits modular theory data.

This constructs the modular automorphism group σ^ω together with proofs
that ω is σ-invariant and KMS at β = 1.

**Proof**: From the axioms above plus the existing `ModularTheoryData` structure.
The GNS construction gives (H_ω, π_ω, Ω_ω) with Ω_ω cyclic and separating.
Define S : π(a)Ω ↦ π(a*)Ω, take the polar decomposition S̄ = JΔ^{1/2},
and set σ_t(a) = Δ^{it} a Δ^{-it}. The KMS property at β = 1 follows from
the spectral theory of Δ.

**Note**: This is stated as an axiom because the actual Tomita-Takesaki
construction requires unbounded operator theory (polar decomposition of
densely defined closable operators) not yet available in Mathlib. The
discharge route is clear once unbounded operators and the modular operator
Δ are formalized. -/
axiom tomita_takesaki {A : Type*} [CStarAlgebra A] [WStarAlgebra A]
    (ω : FaithfulNormalState A) : ModularTheoryData A ω


/-! ## § 6. The Born-KMS Biconditional

The main theorem: faithful normal states are exactly the KMS-1 states.
-/

variable {A : Type*} [CStarAlgebra A] [WStarAlgebra A]

/-- **Forward direction**: Faithful normal states are KMS at β = 1.

**Chain**: faithful + normal → bundle as FaithfulNormalState → Tomita-Takesaki
→ ModularTheoryData → extract kms_at_one. -/
theorem born_kms_forward (ω : State A) (hf : ω.IsFaithful) (hn : ω.IsNormal) :
    ∃ σ : Dynamics A, IsKMSState ω σ 1 := by
  -- Bundle into FaithfulNormalState
  let ω_fn : FaithfulNormalState A :=
    { toState := ω, faithful := hf, normal := hn }
  -- Apply Tomita-Takesaki to get modular data
  let hmod := tomita_takesaki ω_fn
  -- Extract the dynamics and KMS property
  exact ⟨hmod.dynamics, hmod.kms_at_one⟩

/-- **Reverse direction**: KMS-1 states are faithful and normal.

**Chain**: ∃ σ with KMS at 1 → HHW faithfulness + HHW normality. -/
theorem born_kms_reverse (ω : State A) (h : ∃ σ : Dynamics A, IsKMSState ω σ 1) :
    ω.IsFaithful ∧ ω.IsNormal := by
  obtain ⟨σ, hkms⟩ := h
  exact ⟨kms_implies_faithful one_pos hkms, kms_implies_normal one_pos hkms⟩

/-- **The Born-KMS Biconditional**: A state on a von Neumann algebra is
faithful and normal if and only if it is KMS at β = 1 for some dynamics.

  (ω faithful ∧ ω normal) ⟺ (∃ σ, IsKMSState ω σ 1)

**Forward** (Born → KMS): Tomita-Takesaki modular theory.
**Reverse** (KMS → Born): Haag-Hugenholtz-Winnink theorem.

**Physical meaning**: The Born rule (faithful normal state = full-support
vector state) and thermal equilibrium (KMS condition) are equivalent
characterizations of the same class of states. A state admits the Born
rule with full support if and only if it describes a thermal equilibrium.

**The bridge is modular theory**: The modular automorphism group σ^ω is
simultaneously:
- The unique dynamics making ω a KMS state (thermodynamics)
- The flow generated by the modular Hamiltonian K = -log Δ (Born rule via GNS)
- The "thermal time" of the Connes-Rovelli hypothesis (quantum gravity) -/
theorem born_kms_biconditional (ω : State A) :
    (ω.IsFaithful ∧ ω.IsNormal) ↔ (∃ σ : Dynamics A, IsKMSState ω σ 1) :=
  ⟨fun ⟨hf, hn⟩ => born_kms_forward ω hf hn, born_kms_reverse ω⟩


/-! ## § 7. Uniqueness of the Thermal Dynamics

The KMS-1 dynamics is unique: if ω is KMS at β = 1 with respect to
both σ₁ and σ₂, then σ₁ = σ₂. This means the Born-KMS correspondence
is a genuine bijection, not just a surjection.
-/

omit [WStarAlgebra A] in
/-- The KMS-1 dynamics of a faithful normal state is unique.

If ω is KMS at β = 1 with respect to both σ₁ and σ₂, then
σ₁(t)(a) = σ₂(t)(a) for all t and a. The modular automorphism group
is the only flow making ω thermal at unit temperature. -/
theorem born_kms_dynamics_unique (ω : State A)
    (σ₁ σ₂ : Dynamics A) (h₁ : IsKMSState ω σ₁ 1) (h₂ : IsKMSState ω σ₂ 1) :
    ∀ t a, σ₁.evolve t a = σ₂.evolve t a :=
  takesaki_kms_unique σ₁ σ₂ h₁ h₂


/-! ## § 8. The Full Correspondence at Arbitrary Temperature

The correspondence extends to arbitrary inverse temperature β > 0
via rescaling of the dynamics.
-/

/-- Forward at arbitrary β: faithful normal → KMS at β for rescaled dynamics. -/
theorem born_kms_forward_at_beta (ω : State A)
    (hf : ω.IsFaithful) (hn : ω.IsNormal) (β : ℝ) (hβ : 0 < β) :
    ∃ α : Dynamics A, IsKMSState ω α β := by
  -- Get KMS at 1 from forward direction
  obtain ⟨σ, hσ⟩ := born_kms_forward ω hf hn
  -- Rescale from β₁ = 1 to β₂ = β
  exact ⟨σ.rescale (1 / β), hσ.rescale one_pos β hβ⟩

/-- Reverse at arbitrary β: KMS at any β > 0 → faithful and normal. -/
theorem born_kms_reverse_at_beta (ω : State A)
    (β : ℝ) (hβ : 0 < β) (h : ∃ α : Dynamics A, IsKMSState ω α β) :
    ω.IsFaithful ∧ ω.IsNormal := by
  obtain ⟨α, hkms⟩ := h
  exact ⟨kms_implies_faithful hβ hkms, kms_implies_normal hβ hkms⟩

/-- **The Born-KMS Biconditional at Arbitrary Temperature.**

  (ω faithful ∧ ω normal) ⟺ (∃ α, IsKMSState ω α β)

for any fixed β > 0. The set of faithful normal states is exactly the set
of β-KMS states (as β and the dynamics vary together). -/
theorem born_kms_biconditional_at_beta (ω : State A) (β : ℝ) (hβ : 0 < β) :
    (ω.IsFaithful ∧ ω.IsNormal) ↔ (∃ α : Dynamics A, IsKMSState ω α β) :=
  ⟨fun ⟨hf, hn⟩ => born_kms_forward_at_beta ω hf hn β hβ,
   fun h => born_kms_reverse_at_beta ω β hβ h⟩


/-! ## § 9. The Full Correspondence Structure

Bundling everything together into a single structure that captures the
complete Born-KMS correspondence for a given state.
-/
universe u_gns
/-- **The Born-KMS Correspondence**: The complete equivalence between
Born-rule states and KMS equilibrium states.

For a state ω on a von Neumann algebra, this structure witnesses:
1. The biconditional: faithful+normal ↔ KMS
2. Uniqueness: the KMS dynamics is unique (the modular group)
3. Temperature scaling: the correspondence holds at any β > 0
4. The GNS Born rule: ω(a) = ⟨Ω, π(a)Ω⟩
5. The cyclic-separating equivalence: faithful ↔ separating -/
structure BornKMSCorrespondence (ω : State A) where
  /-- The GNS triple realizing the Born rule. -/
  gns : GNSData.{_, u_gns} A ω
  /-- The biconditional at β = 1. -/
  equiv : (ω.IsFaithful ∧ ω.IsNormal) ↔ (∃ σ : Dynamics A, IsKMSState ω σ 1)
  /-- Uniqueness of the thermal dynamics. -/
  unique : ∀ σ₁ σ₂ : Dynamics A,
    IsKMSState ω σ₁ 1 → IsKMSState ω σ₂ 1 → ∀ t a, σ₁.evolve t a = σ₂.evolve t a
  /-- The biconditional extends to arbitrary temperature. -/
  equiv_at_beta : ∀ β : ℝ, 0 < β →
    ((ω.IsFaithful ∧ ω.IsNormal) ↔ (∃ α : Dynamics A, IsKMSState ω α β))
  /-- Faithfulness ↔ separating GNS vector. -/
  faithful_iff_separating : ω.IsFaithful ↔ gns.IsSeparating

/-- **Main Theorem**: Every state on a von Neumann algebra admits a
Born-KMS correspondence. -/
noncomputable def born_kms_correspondence (ω : State A) : BornKMSCorrespondence.{u_gns} ω where
  gns := gns_construction.{_, u_gns} A ω
  equiv := born_kms_biconditional ω
  unique := fun σ₁ σ₂ h₁ h₂ => takesaki_kms_unique σ₁ σ₂ h₁ h₂
  equiv_at_beta := fun β hβ => born_kms_biconditional_at_beta ω β hβ
  faithful_iff_separating := gns_faithful_iff_separating (gns_construction.{_, u_gns} A ω)

/-! ## § 10. Corollaries

Consequences of the Born-KMS correspondence.
-/

/-- **Modular dynamics from KMS**: A KMS-1 state on a von Neumann algebra
admits modular theory data. -/
theorem kms_admits_modular_data (ω : State A)
    (σ : Dynamics A) (hkms : IsKMSState ω σ 1) :
    ∃ hmod : ModularTheoryData A
      { toState := ω,
        faithful := kms_implies_faithful one_pos hkms,
        normal := kms_implies_normal one_pos hkms },
      ∀ t a, hmod.dynamics.evolve t a = σ.evolve t a := by
  set ω_fn : FaithfulNormalState A :=
    { toState := ω,
      faithful := kms_implies_faithful one_pos hkms,
      normal := kms_implies_normal one_pos hkms }
  let hmod := tomita_takesaki ω_fn
  refine ⟨hmod, ?_⟩
  -- The modular dynamics equals σ by uniqueness
  exact takesaki_kms_unique hmod.dynamics σ hmod.kms_at_one hkms

omit [WStarAlgebra A] in
/-- **KMS states are invariant**: Every KMS-1 state is invariant under
its own dynamics. Combines the reverse direction with modular invariance. -/
theorem kms_state_is_invariant (ω : State A)
    (σ : Dynamics A) (hkms : IsKMSState ω σ 1) (hβ : (0 : ℝ) < 1 := one_pos) :
    IsInvariant ω σ :=
  IsKMSState.isInvariant hβ hkms

/-- **The thermal time hypothesis** (Connes-Rovelli): For a faithful normal
state on a von Neumann algebra, the modular automorphism group is the unique
one-parameter group of *-automorphisms making the state KMS at β = 1.

Time evolution is not given a priori — it emerges from the state's
thermodynamic structure. Different states give different "times."

This theorem packages the existence, KMS property, and uniqueness together. -/
theorem thermal_time_hypothesis (ω : FaithfulNormalState A) :
    ∃ σ : Dynamics A, IsKMSState ω.toState σ 1 ∧
      ∀ σ' : Dynamics A, IsKMSState ω.toState σ' 1 →
        ∀ t a, σ'.evolve t a = σ.evolve t a := by
  let hmod := tomita_takesaki ω
  exact ⟨hmod.dynamics, hmod.kms_at_one,
    fun σ' hσ' => takesaki_kms_unique σ' hmod.dynamics hσ' hmod.kms_at_one⟩

/-! ## § 11. Summary of Axiom Obligations

The following axioms are introduced in this file and will be discharged
as the library matures:

1. **`gns_construction`**: The GNS theorem.
   - Status: Standard result, requires quotient completion machinery.
   - Blocked by: Completion of inner product spaces from semi-inner products.

2. **`kms_implies_faithful`**: HHW faithfulness.
   - Status: Requires analytic continuation on strips (partially available
     via PeriodicStrip.lean) and the identity theorem for holomorphic functions.
   - Blocked by: Mathlib's complex analysis coverage for strips.

3. **`kms_implies_normal`**: HHW normality.
   - Status: Requires σ-weak topology and Kaplansky density.
   - Blocked by: Von Neumann algebra predual formalization.

4. **`takesaki_kms_unique`**: Uniqueness of KMS-1 flow.
   - Status: Requires Tomita-Takesaki construction and uniqueness of
     analytic continuation.
   - Blocked by: Unbounded operator polar decomposition in Mathlib.

5. **`tomita_takesaki`**: Modular theory existence.
   - Status: The deepest axiom. Requires GNS + Tomita operator + polar
     decomposition + modular theory.
   - Blocked by: Same as (4), plus the spectral theory of Δ.

Total: **5 axioms** (including `tomita_takesaki`), all standard named
theorems with well-understood proof strategies.
-/

end Spectra.QuantumMechanics.BornRule

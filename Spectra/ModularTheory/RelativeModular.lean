/-
Spectra: RelativeModular.lean
Relative modular theory: two states in standard form, the relative Tomita
operator, the relative modular flow, and the Connes cocycle.

Filename: ModularTheory/RelativeModular.lean
Target: Mathlib master (2026-06-10)
-/
import Spectra.ModularTheory.TomitaTakesaki
/-!
# Relative Modular Theory and the Connes Cocycle

Two faithful states on the same algebra, in standard form: the same `M ⊆ B(H)`,
two cyclic/separating vectors `Ω_φ`, `Ω_ψ`.  The relative Tomita operator

  `S_{ψ,φ}(aΩ_φ) = a*Ω_ψ`

is `preTomitaOpTo D.φ D.ψ.Ω` — the general definition from `TomitaTakesaki.lean`
instantiated at the other state's vector, so well-definedness, antilinearity,
formal adjointness and **closability** are inherited with no new proofs.  (The old
file re-proved all four; they are deleted here, not moved.)

The relative modular flow `t ↦ Δ_{ψ,φ}^{it}` is a `OneParameterUnitaryGroup`
(`RelativeModularData`), replacing the old bounded-`op`-plus-axiomatized-spectral-
measure structure.  The old `diagonal_eq` field — which quantified over *all*
`ModularOperatorData` instances and was therefore unsatisfiable — is replaced by
the honest statement `relativePreTomitaOp_diagonal` at the level of the operator,
where it is a one-line congruence.

## The Connes cocycle

`u_t = (Dψ : Dφ)_t = Δ_{ψ,φ}^{it} · Δ_φ^{−it}`.  What the unitary-group encoding
buys, compared to the old files:

* **unitarity of `u_t`** — was a hypothesis (`SpatialDerivativeUnitarity.isUnitary`),
  now a theorem (`spatialDerivative_mul_adjoint`, `_adjoint_mul`);
* **the cocycle identity** `u_{s+t} = u_s·σ_s^φ(u_t)` — proved here by group-law
  telescoping (`connes_cocycle_identity`), one `simp` after expanding;
* **strong continuity** `t ↦ u_tψ` — was absent, now a theorem
  (`spatialDerivative_strongly_continuous`);
* **the intertwining theorem** `σ_t^ψ = Ad(u_t) ∘ σ_t^φ` — was a bare hypothesis
  (`IntertwiningData`), now a *theorem* given the single genuinely deep relation
  `Δ_{ψ,φ}^{it} a Δ_{ψ,φ}^{−it} = σ_t^ψ(a)` (`RelativeTomitaTheorem.conjugation_eq`,
  Takesaki TOA II Ch. VIII), via pure telescoping.

## What is still a hypothesis (honest inventory)

* `RelativeModularData` — existence of the flow `Δ_{ψ,φ}^{it}` (polar
  decomposition of the closure of `S_{ψ,φ}`; closability is proved).
* `RelativeTomitaTheorem.conjugation_eq` — `Δ_{ψ,φ}^{it}(·)Δ_{ψ,φ}^{−it} = σ_t^ψ`
  on `M` (the relative Tomita theorem).
* `RelativeTomitaTheorem.cocycle_mem` — `u_t ∈ M` (part of Connes' theorem;
  classically proved via the 2×2-matrix balanced-weight trick).

## References

* [Connes, "Une classification des facteurs de type III", Ann. Sci. ENS 6 (1973)]
* [Araki, "Relative Hamiltonian for faithful normal states" (1973)]
* [Takesaki, *Theory of Operator Algebras II*][takesaki2003], Ch. VIII
* [Bratteli–Robinson, *Operator Algebras and QSM 1*][bratteli1987], §2.5.4
-/
open Complex Filter Topology
open scoped InnerProductSpace

namespace Spectra.QuantumMechanics.ModularTheory

open Spectra.QuantumMechanics OneParameterUnitaryGroup
open Spectra.QuantumMechanics.SpectralTheory
open VNAlgebraWithVector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## Section 1: Two states in standard form

The same algebra, two distinguished vectors.  (In Araki's standard form every
faithful normal state is represented by a unique vector in the natural cone of
the *same* Hilbert space, so this is no loss of generality.)
-/

/-- Two faithful states on the same von Neumann algebra, in standard form:
the same `*`-subalgebra, two cyclic/separating vectors. -/
structure TwoStateData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The reference state `φ` (with vector `Ω_φ`). -/
  φ : VNAlgebraWithVector H
  /-- The target state `ψ` (with vector `Ω_ψ`). -/
  ψ : VNAlgebraWithVector H
  /-- The two states live on the SAME algebra. -/
  same_algebra : φ.algebra = ψ.algebra

namespace TwoStateData

variable (D : TwoStateData H)

/-- Transport of membership `M_φ → M_ψ`. -/
lemma mem_ψ_of_mem_φ {a : H →L[ℂ] H} (ha : a ∈ D.φ.algebra) : a ∈ D.ψ.algebra := by
  rw [← D.same_algebra]; exact ha

/-- Transport of membership `M_ψ → M_φ`. -/
lemma mem_φ_of_mem_ψ {a : H →L[ℂ] H} (ha : a ∈ D.ψ.algebra) : a ∈ D.φ.algebra := by
  rw [D.same_algebra]; exact ha

/-- The state-swapped data: `(φ, ψ) ↦ (ψ, φ)`. -/
def swap : TwoStateData H := ⟨D.ψ, D.φ, D.same_algebra.symm⟩

@[simp] lemma swap_φ : D.swap.φ = D.ψ := rfl
@[simp] lemma swap_ψ : D.swap.ψ = D.φ := rfl

end TwoStateData

/-!
## Section 2: The relative Tomita operator

`S_{ψ,φ}(aΩ_φ) = a*Ω_ψ` — *defined* as `preTomitaOpTo D.φ D.ψ.Ω`.  Every
property below is a one-line instance of the corresponding general theorem.
-/

variable (D : TwoStateData H)

/-- **The relative Tomita operator** `S_{ψ,φ} : aΩ_φ ↦ a*Ω_ψ`, the general
`preTomitaOpTo` with base `Ω_φ` and target `Ω_ψ`. -/
noncomputable def relativePreTomitaOp : D.φ.algebraΩ →ₗ⋆[ℂ] H :=
  preTomitaOpTo D.φ D.ψ.Ω

/-- **The relative co-Tomita operator** `F : b'Ω_φ ↦ b'*Ω_ψ` on `M'Ω_φ` — the
formal adjoint partner of `S_{ψ,φ}` (both decompose over the base `Ω_φ`; the old
file's remark that the naive domain `M'Ω_ψ` does NOT work is built into the
general definition). -/
noncomputable def relativePreCoTomitaOp : D.φ.commutantΩ →ₗ⋆[ℂ] H :=
  preCoTomitaOpTo D.φ D.ψ.Ω

@[simp] lemma relativePreTomitaOp_apply (ξ : D.φ.algebraΩ) :
    relativePreTomitaOp D ξ
      = ContinuousLinearMap.adjoint (D.φ.algebraΩ_repr ξ) D.ψ.Ω := rfl

@[simp] lemma relativePreCoTomitaOp_apply (η : D.φ.commutantΩ) :
    relativePreCoTomitaOp D η
      = ContinuousLinearMap.adjoint (D.φ.commutantΩ_repr η) D.ψ.Ω := rfl

/-- Formal adjointness: `⟪S_{ψ,φ}(aΩ_φ), b'Ω_φ⟫ = ⟪F(b'Ω_φ), aΩ_φ⟫`. -/
theorem relative_formal_adjoint (ξ : D.φ.algebraΩ) (η : D.φ.commutantΩ) :
    ⟪relativePreTomitaOp D ξ, (η : H)⟫_ℂ = ⟪relativePreCoTomitaOp D η, (ξ : H)⟫_ℂ :=
  preTomitaOpTo_formal_adjoint D.φ D.ψ.Ω ξ η

/-- `S_{ψ,φ}` is closable (theorem, not hypothesis). -/
theorem relativePreTomitaOp_isClosable :
    IsClosableOn D.φ.algebraΩ (relativePreTomitaOp D) :=
  preTomitaOpTo_isClosable D.φ D.ψ.Ω

/-- **Diagonal reduction**: when the two vectors coincide, `S_{ψ,φ} = S₀`.
(The honest replacement for the old unsatisfiable `diagonal_eq` field.) -/
lemma relativePreTomitaOp_diagonal (h : D.ψ.Ω = D.φ.Ω) :
    relativePreTomitaOp D = preTomitaOp D.φ := by
  simp only [relativePreTomitaOp, preTomitaOp, h]

/-- `S_{ψ,φ}` maps `MΩ_φ` into `MΩ_ψ`. -/
lemma relativePreTomitaOp_mem (ξ : D.φ.algebraΩ) :
    relativePreTomitaOp D ξ ∈ D.ψ.algebraΩ :=
  ⟨ContinuousLinearMap.adjoint (D.φ.algebraΩ_repr ξ),
    D.mem_ψ_of_mem_φ (adjoint_mem (D.φ.algebraΩ_repr_mem ξ)),
    (relativePreTomitaOp_apply D ξ).symm⟩

/-- **The swap inverts the relative operator on `MΩ_φ`**:
`S_{φ,ψ}(S_{ψ,φ}(aΩ_φ)) = S_{φ,ψ}(a*Ω_ψ) = a**Ω_φ = aΩ_φ`.
(The relative analogue of `preTomitaOp_involutive`.) -/
lemma relativePreTomitaOp_swap_apply (ξ : D.φ.algebraΩ) :
    relativePreTomitaOp D.swap
      ⟨relativePreTomitaOp D ξ, relativePreTomitaOp_mem D ξ⟩ = (ξ : H) := by
  have hrepr : D.ψ.algebraΩ_repr
        ⟨relativePreTomitaOp D ξ, relativePreTomitaOp_mem D ξ⟩
      = ContinuousLinearMap.adjoint (D.φ.algebraΩ_repr ξ) := by
    symm
    apply D.ψ.algebraΩ_repr_unique
    · exact D.mem_ψ_of_mem_φ (adjoint_mem (D.φ.algebraΩ_repr_mem ξ))
    · exact (relativePreTomitaOp_apply D ξ).symm
  rw [relativePreTomitaOp_apply]
  rw [show D.swap.φ.algebraΩ_repr
        ⟨relativePreTomitaOp D ξ, relativePreTomitaOp_mem D ξ⟩
      = ContinuousLinearMap.adjoint (D.φ.algebraΩ_repr ξ) from hrepr]
  rw [ContinuousLinearMap.adjoint_adjoint]
  exact D.φ.algebraΩ_repr_spec ξ

/-!
## Section 3: The relative modular flow

`t ↦ Δ_{ψ,φ}^{it}` as a one-parameter unitary group.  The flow is to be
constructed from the polar decomposition of the closure of `S_{ψ,φ}`; until then
this is the hypothesis bundle, with its characterizing relations in
`RelativeTomitaTheorem` below — *not* baked in as fields, so that constructing
an instance never requires more than what the polar decomposition provides.
-/

/-- The relative modular data: the flow `t ↦ Δ_{ψ,φ}^{it}`. -/
structure RelativeModularData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : TwoStateData H) where
  /-- The relative modular flow `t ↦ Δ_{ψ,φ}^{it}`. -/
  flow : OneParameterUnitaryGroup (H := H)

variable {D}

/-- The relative modular unitary `Δ_{ψ,φ}^{it}` (notation for the flow). -/
noncomputable abbrev relativeModularUnitary (rel : RelativeModularData H D)
    (t : ℝ) : H →L[ℂ] H :=
  rel.flow.U t

/-- `Δ_{ψ,φ}^{i(s+t)} = Δ_{ψ,φ}^{is}·Δ_{ψ,φ}^{it}`. -/
lemma relativeModularUnitary_group_law (rel : RelativeModularData H D) (s t : ℝ) :
    relativeModularUnitary rel (s + t)
      = relativeModularUnitary rel s * relativeModularUnitary rel t :=
  (U_mul rel.flow s t).symm

/-- `Δ_{ψ,φ}^{i·0} = 1`. -/
lemma relativeModularUnitary_zero (rel : RelativeModularData H D) :
    relativeModularUnitary rel 0 = 1 :=
  U_zero rel.flow

/-!
## Section 4: The Connes cocycle (spatial derivative)

`u_t = (Dψ : Dφ)_t = Δ_{ψ,φ}^{it} · Δ_φ^{−it}`.  Unitarity, `u_0 = 1`, strong
continuity, and the cocycle identity are theorems — only membership `u_t ∈ M`
and the conjugation relation to `σ^ψ` remain hypotheses (`RelativeTomitaTheorem`).
-/

/-- **The Connes cocycle / spatial derivative**
`(Dψ : Dφ)_t = Δ_{ψ,φ}^{it} · Δ_φ^{−it}`. -/
noncomputable def spatialDerivative (md : ModularData H D.φ)
    (rel : RelativeModularData H D) (t : ℝ) : H →L[ℂ] H :=
  rel.flow.U t * md.flow.U (-t)

/-- `u_0 = 1`. -/
lemma spatialDerivative_zero (md : ModularData H D.φ) (rel : RelativeModularData H D) :
    spatialDerivative md rel 0 = 1 := by
  simp only [spatialDerivative, neg_zero, U_zero, mul_one]

/-- `u_t† = Δ_φ^{it} · Δ_{ψ,φ}^{−it}`. -/
lemma spatialDerivative_adjoint (md : ModularData H D.φ)
    (rel : RelativeModularData H D) (t : ℝ) :
    ContinuousLinearMap.adjoint (spatialDerivative md rel t)
      = md.flow.U t * rel.flow.U (-t) := by
  simp only [spatialDerivative]
  rw [adjoint_mul, ← inverse_eq_adjoint rel.flow t, ← inverse_eq_adjoint md.flow (-t),
    neg_neg]

/-- **Unitarity of the cocycle, half 1**: `u_t · u_t† = 1`.
(Was the hypothesis `SpatialDerivativeUnitarity.isUnitary`; now telescoping.) -/
theorem spatialDerivative_mul_adjoint (md : ModularData H D.φ)
    (rel : RelativeModularData H D) (t : ℝ) :
    spatialDerivative md rel t
      * ContinuousLinearMap.adjoint (spatialDerivative md rel t) = 1 := by
  rw [spatialDerivative_adjoint]
  simp only [spatialDerivative, mul_assoc, U_neg_mul_cancel, U_mul_neg]

/-- **Unitarity of the cocycle, half 2**: `u_t† · u_t = 1`. -/
theorem spatialDerivative_adjoint_mul (md : ModularData H D.φ)
    (rel : RelativeModularData H D) (t : ℝ) :
    ContinuousLinearMap.adjoint (spatialDerivative md rel t)
      * spatialDerivative md rel t = 1 := by
  rw [spatialDerivative_adjoint]
  simp only [spatialDerivative, mul_assoc, U_neg_mul_cancel, U_mul_neg]

/-- `t ↦ u_tψ` is continuous: joint strong continuity of the product of flows.
(Absent from the old file; needed for `u` to be an honest `ModularCocycle`.) -/
lemma spatialDerivative_strongly_continuous (md : ModularData H D.φ)
    (rel : RelativeModularData H D) (ψ : H) :
    Continuous fun t => spatialDerivative md rel t ψ := by
  have hf : Continuous fun t : ℝ => md.flow.U (-t) ψ := by
    exact (md.flow.strong_continuous ψ).comp continuous_neg
  have h := continuous_U_apply rel.flow hf
  have heq : (fun t => rel.flow.U t (md.flow.U (-t) ψ))
      = fun t => spatialDerivative md rel t ψ := by
    funext t
    simp [spatialDerivative, ContinuousLinearMap.mul_apply]
  rw [← heq]
  exact h

/-- **The Connes cocycle identity** (the algebraic half of the Radon–Nikodym
theorem): `u_{s+t} = u_s · σ_s^φ(u_t)`.

`u_{s+t} = R_{s+t}Φ_{-(s+t)} = R_s(Φ_{-s}Φ_s)R_tΦ_{-t}Φ_{-s}
        = (R_sΦ_{-s})·(Φ_s(R_tΦ_{-t})Φ_{-s}) = u_s·σ_s^φ(u_t)`
where `R = Δ_{ψ,φ}^{i·}`, `Φ = Δ_φ^{i·}` — pure group-law telescoping, closed by
the cancellation `simp` set.  [Connes 1973, Thm. 1.2.1]; [Takesaki TOA II,
Ch. VIII, Thm. 3.3]. -/
theorem connes_cocycle_identity (md : ModularData H D.φ)
    (rel : RelativeModularData H D) (s t : ℝ) :
    spatialDerivative md rel (s + t)
      = spatialDerivative md rel s
        * modularAutomorphism md s (spatialDerivative md rel t) := by
  simp only [spatialDerivative, modularAutomorphism]
  rw [← U_mul rel.flow s t, show -(s + t) = -t + -s from by ring,
    ← U_mul md.flow (-t) (-s)]
  simp only [mul_assoc, U_neg_mul_cancel]

/-!
## Section 5: The relative Tomita theorem and the intertwining theorem

The single deep input is `Δ_{ψ,φ}^{it} a Δ_{ψ,φ}^{−it} = σ_t^ψ(a)` for `a ∈ M`
(Takesaki TOA II, Ch. VIII) plus `u_t ∈ M`.  The intertwining theorem — the old
`IntertwiningData` hypothesis — is then a *theorem*.
-/

/-- **The relative Tomita theorem**, as a `Prop`-valued bundle: the conjugation
relation characterizing the relative flow, and membership of the cocycle in `M`. -/
structure RelativeTomitaTheorem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (D : TwoStateData H)
    (md_φ : ModularData H D.φ) (md_ψ : ModularData H D.ψ)
    (rel : RelativeModularData H D) : Prop where
  /-- `Δ_{ψ,φ}^{it} a Δ_{ψ,φ}^{−it} = σ_t^ψ(a)` for `a ∈ M`. -/
  conjugation_eq : ∀ (t : ℝ) (a : H →L[ℂ] H), a ∈ D.φ.algebra →
    rel.flow.U t * a * rel.flow.U (-t) = modularAutomorphism md_ψ t a
  /-- `u_t ∈ M` for every `t` (part of Connes' theorem). -/
  cocycle_mem : ∀ t : ℝ, spatialDerivative md_φ rel t ∈ D.φ.algebra

/-- **The intertwining theorem** (was the `IntertwiningData` hypothesis; now a
theorem): `σ_t^ψ(a) = u_t · σ_t^φ(a) · u_t†` for `a ∈ M`.

`u_tσ_t^φ(a)u_t† = R_tΦ_{-t}·Φ_taΦ_{-t}·Φ_tR_{-t} = R_t a R_{-t} = σ_t^ψ(a)`,
telescoping plus `conjugation_eq`. -/
theorem spatialDerivative_intertwines (md_φ : ModularData H D.φ)
    (md_ψ : ModularData H D.ψ) (rel : RelativeModularData H D)
    (hRT : RelativeTomitaTheorem H D md_φ md_ψ rel)
    (t : ℝ) (a : H →L[ℂ] H) (ha : a ∈ D.φ.algebra) :
    modularAutomorphism md_ψ t a
      = spatialDerivative md_φ rel t
        * modularAutomorphism md_φ t a
        * ContinuousLinearMap.adjoint (spatialDerivative md_φ rel t) := by
  rw [spatialDerivative_adjoint, ← hRT.conjugation_eq t a ha]
  simp only [spatialDerivative, modularAutomorphism, mul_assoc, U_neg_mul_cancel]

end Spectra.QuantumMechanics.ModularTheory

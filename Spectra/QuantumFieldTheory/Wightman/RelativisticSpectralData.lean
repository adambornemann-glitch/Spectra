/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.Joint.Defs
import Spectra.ProjValMeasure.General
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The Wightman spectral condition and mass gap, as a joint-spectral hypothesis bundle

This file states — precisely, as a genuine *joint*-spectral fact — the Wightman spectral condition
(axiom W2), uniqueness of the vacuum (W3), and the **mass gap**, for a relativistic quantum theory
carried on a complex Hilbert space `H`.  It is deliberately **generic relativistic-QFT content**:
nothing here mentions a gauge group, a lattice, or Yang–Mills.  It belongs to any future Spectra
development that wants to *reason from* "a mass gap holds," independently of how the theory is
constructed.

## The mathematics

The energy-momentum generators `P = (P⁰, P¹, P², P³)` (with `P⁰` the Hamiltonian) generate the
translation representation `U(a) = e^{i P·a}`.  They pairwise **strongly commute** (they generate an
abelian translation group), so — *in principle* — they admit a **joint** projection-valued measure
`E` on spacetime-momentum space `ℝ⁴`, whose coordinate marginals recover each `P^μ`.  The physics is
three constraints on *that* measure:

* **Spectral condition (W2).**  The joint spectrum lies in the closed forward light cone
  `V̄⁺ = {p : p⁰ ≥ 0 ∧ (p⁰)² ≥ |p⃗|²}` — equivalently, `E` puts no weight on its complement.
* **Uniqueness of the vacuum (W3).**  The weight *exactly* at `p = 0` is the rank-one projector onto
  the vacuum line.
* **Mass gap.**  For some `Δ > 0`, `E` puts no weight in the *forbidden annulus* — the part of the
  cone that is off the origin yet below the mass-`Δ` upper hyperboloid.  Via functional calculus
  this is exactly `spec((P^μ P_μ)^{1/2}) ⊆ {0} ∪ [Δ, ∞)`: an isolated vacuum at `0`, then a gap
  up to `Δ`.

Because these are conditions on a Borel function of the *joint* measure, phrasing the gap on the
joint spectrum of the four generators is the honest primitive — it is *not* a statement about `P⁰`
alone.

## The Lean shape

Following `Spectra.TomitaTakesaki.ModularData` (`Modular/TomitaTakesaki/Basic.lean`), the data is
bundled in a structure whose fields are the *defining properties* a genuine construction (e.g. an
Osterwalder–Schrader reconstruction) would have to discharge.

**Honesty, in the spirit of `ModularData`'s.**  `P`, `jointPVM`, and `vacuum` are **not**
constructed here.  The bundle is *consistent* — it is not self-contradictory: the degenerate
one-dimensional theory (`H = ℂ`, all generators `0`, all joint weight a Dirac mass at `p = 0`)
satisfies every field, since the origin is excluded from the forbidden annulus, so its mass gap
holds vacuously.  But **no physically nontrivial relativistic theory is known to inhabit it** —
in particular no interacting four-dimensional Yang–Mills theory, whose very existence with a
positive gap is the open Millennium problem.  Producing such an inhabitant requires a genuine
construction (an Osterwalder–Schrader reconstruction of an interacting representation on `H`),
which does not exist.  Downstream developments reasoning "**if** a mass gap holds, **then**
…" may nevertheless take a `RelativisticSpectralData H` as a hypothesis and reason from it.

## Design notes (discovered by writing it)

* **No new `support` notion.**  Rather than define a topological support and phrase the
  constraints as `support ⊆ region` (which would need a Lindelöf/second-countability covering
  argument), everything is phrased directly as `jointPVM.proj (forbidden region) _ = 0` — the
  exact idiom Spectra already uses for the Dirac mass gap
  (`spectralProjection_Ioo_eq_zero_of_norm_ge`).  Zero new infrastructure.
* **`IsJointOfFamily` is stated as operator equations**, comparing `.proj`-applied-to-a-set
  values in `H →L[ℂ] H`, because `ProjValMeasure H` (the single-operator, `ι = ℝ` type) and
  `ProjValMeasure' H (EuclideanSpace ℝ (Fin 4))` (the general-`ι` type) are deliberately
  **separate Lean types**; a marginal of the latter can never be *equal as a structure* to the
  former.  This is exactly how `BornRule.Joint.IsJointOf` handles the pair case.
* **`ProjValMeasure'` already bakes in `proj_inter`** (genuine projectivity), so — unlike the pair
  case, which needed `POVM` + a separate `IsProjective` predicate — `IsJointOfFamily` needs no extra
  projectivity hypothesis.
* **`stronglyCommute` is a *redundant* field** (see
  `RelativisticSpectralData.stronglyCommute_of_marginal`):
  pairwise strong commutativity already follows from `jointPVM_marginal`.  It is retained as a
  field because it is the *primitive physical hypothesis*, and because the genuinely hard
  content — building a `jointPVM` **from** strong commutativity (the `n`-ary spectral theorem,
  an open engineering task generalizing `stronglyCommute_iff_jointPVM`) — is not available, so a
  construction cannot yet drop it "for free."

## References

* [Streater, Wightman, *PCT, Spin and Statistics, and All That*], the spectral condition (Axiom W2),
  p. 97.
* [Reed, Simon, *Methods of Modern Mathematical Physics I*], §VIII.5 (strong commutativity; joint
  spectral measure of commuting self-adjoint operators).
* Clay Mathematics Institute, *Quantum Yang–Mills theory* (Jaffe–Witten): the mass gap as
  `Δ > 0` in the energy-momentum spectrum.

## Tags

Wightman axioms, spectral condition, mass gap, joint spectral measure, projection-valued measure,
vacuum, relativistic quantum field theory
-/

open MeasureTheory Complex InnerProductSpace
open scoped InnerProductSpace
open Spectra Spectra.Operator Spectra.QuantumMechanics.BornRule

namespace Spectra.QuantumFieldTheory.Wightman

/-! ## §1  The spacetime-momentum regions

Concrete subsets of `ℝ⁴ = EuclideanSpace ℝ (Fin 4)` (coordinate `0` is the energy `p⁰`;
coordinates `1,2,3` are the spatial momentum `p⃗`) and their `MeasurableSet` proofs.  All are
Hilbert-space-free.
-/

/-- Continuity of the `i`-th coordinate evaluation `p ↦ p i` on `ℝ⁴`, as the underlying function of
the continuous linear coordinate projection `EuclideanSpace.proj i`. -/
lemma continuous_coord (i : Fin 4) :
    Continuous fun p : EuclideanSpace ℝ (Fin 4) => p i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

/-- Measurability of the `i`-th coordinate evaluation `p ↦ p i` on `ℝ⁴`. -/
lemma measurable_coord (i : Fin 4) :
    Measurable fun p : EuclideanSpace ℝ (Fin 4) => p i :=
  (continuous_coord i).measurable

/-- The **cylinder set** fixing coordinate `i` into `S`, letting the other three coordinates float
free: `{p : ℝ⁴ | p i ∈ S}`.  Its marginal effect under the joint PVM must recover the spectral
projection of the `i`-th generator (`IsJointOfFamily`). -/
def cylinder (i : Fin 4) (S : Set ℝ) : Set (EuclideanSpace ℝ (Fin 4)) := {p | p i ∈ S}

/-- A cylinder over a measurable base is measurable: it is the coordinate preimage of `S`. -/
lemma measurableSet_cylinder (i : Fin 4) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (cylinder i S) :=
  measurable_coord i hS

/-- The **closed forward light cone** `V̄⁺ = {p : ℝ⁴ | p⁰ ≥ 0 ∧ (p⁰)² ≥ |p⃗|²}` (with the
mostly-minus convention `p⁰² − |p⃗|² ≥ 0`).  The spectral condition (W2) says the joint spectrum
lies here. -/
def closedForwardLightCone : Set (EuclideanSpace ℝ (Fin 4)) :=
  {p | 0 ≤ p 0 ∧ ∑ i : Fin 3, (p i.succ) ^ 2 ≤ (p 0) ^ 2}

lemma measurableSet_closedForwardLightCone : MeasurableSet closedForwardLightCone := by
  have hsum : Continuous fun p : EuclideanSpace ℝ (Fin 4) => ∑ i : Fin 3, (p i.succ) ^ 2 :=
    continuous_finsetSum Finset.univ fun i _ => (continuous_coord i.succ).pow 2
  have hsq : Continuous fun p : EuclideanSpace ℝ (Fin 4) => (p 0) ^ 2 :=
    (continuous_coord 0).pow 2
  unfold closedForwardLightCone
  rw [Set.setOf_and]
  exact (measurableSet_le measurable_const (measurable_coord 0)).inter
    (measurableSet_le hsum.measurable hsq.measurable)

/-- The **forbidden annulus** for a mass gap `Δ`: inside the forward cone, off the origin, and
strictly below the mass-`Δ` upper hyperboloid `p⁰ = √(Δ² + |p⃗|²)`.  The mass gap says the joint
spectrum avoids this region entirely. -/
def massGapAnnulus (Δ : ℝ) : Set (EuclideanSpace ℝ (Fin 4)) :=
  closedForwardLightCone \
    ({0} ∪ {p | Real.sqrt (Δ ^ 2 + ∑ i : Fin 3, (p i.succ) ^ 2) ≤ p 0})

/-- `{0}` (the zero-momentum point of `ℝ⁴`) is measurable — it is closed in the metric topology. -/
lemma measurableSet_singleton_zero :
    MeasurableSet ({0} : Set (EuclideanSpace ℝ (Fin 4))) :=
  isClosed_singleton.measurableSet

lemma measurableSet_massGapAnnulus (Δ : ℝ) : MeasurableSet (massGapAnnulus Δ) := by
  have hsqrt : Continuous
      fun p : EuclideanSpace ℝ (Fin 4) => Real.sqrt (Δ ^ 2 + ∑ i : Fin 3, (p i.succ) ^ 2) :=
    Real.continuous_sqrt.comp <| continuous_const.add <|
      continuous_finsetSum Finset.univ fun i _ => (continuous_coord i.succ).pow 2
  have hhyp : MeasurableSet
      {p : EuclideanSpace ℝ (Fin 4) | Real.sqrt (Δ ^ 2 + ∑ i : Fin 3, (p i.succ) ^ 2) ≤ p 0} :=
    measurableSet_le hsqrt.measurable (measurable_coord 0)
  unfold massGapAnnulus
  exact measurableSet_closedForwardLightCone.diff
    (measurableSet_singleton_zero.union hhyp)

/-! ## §2  The vacuum projector and the family marginal condition -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **rank-one orthogonal projection** `|v⟩⟨v|` onto the line `ℂ ∙ v`.  For a unit vector
this is a genuine (star) projection: `isStarProjection_rankOneProjection`. -/
noncomputable def rankOneProjection (v : H) : H →L[ℂ] H := rankOne ℂ v v

/-- For a unit vector, `rankOneProjection v` is a genuine star projection (self-adjoint idempotent).
This is what makes the `vacuum_unique` field say "`E({0})` is *the* rank-one vacuum projector." -/
lemma isStarProjection_rankOneProjection {v : H} (hv : ‖v‖ = 1) :
    IsStarProjection (rankOneProjection v) :=
  isStarProjection_rankOne_self hv

/-- **The family marginal condition.**  Four self-adjoint operators
`P : Fin 4 → SelfAdjointOperator H` marginalize correctly out of a joint `ProjValMeasure'` on
spacetime-momentum space `ℝ⁴`: the effect on the cylinder fixing coordinate `i` into `S` is the
spectral projection `E_{P i}(S)`.

This is `BornRule.Joint.IsJointOf` generalized from a pair to a `Fin 4`-family.  Because
`ProjValMeasure'` already bakes in multiplicativity (`proj_inter`), no separate projectivity
hypothesis is needed. -/
def IsJointOfFamily (M : ProjValMeasure' H (EuclideanSpace ℝ (Fin 4)))
    (P : Fin 4 → SelfAdjointOperator H) : Prop :=
  ∀ (i : Fin 4) (S : Set ℝ) (hS : MeasurableSet S),
    M.proj (cylinder i S) (measurableSet_cylinder i hS) = (P i).spectralPVM.proj S hS

/-- **The easy direction of the `n`-ary spectral theorem** (the sanity lemma): a joint
`ProjValMeasure'` with the right cylinder marginals forces the whole family to pairwise strongly
commute.  For any
`i, j` and measurable `S, T`,
`E_{P i}(S) · E_{P j}(T) = M(cyl i S) · M(cyl j T) = M(cyl i S ∩ cyl j T) = M(cyl j T ∩ cyl i S)
= M(cyl j T) · M(cyl i S) = E_{P j}(T) · E_{P i}(S)` — pure algebra from `proj_inter` and
`Set.inter_comm`.  (The *hard* converse — building `M` **from** strong commutativity — is the open
`n`-ary generalization of `stronglyCommute_iff_jointPVM`.) -/
theorem stronglyCommute_of_isJointOfFamily
    {M : ProjValMeasure' H (EuclideanSpace ℝ (Fin 4))} {P : Fin 4 → SelfAdjointOperator H}
    (hM : IsJointOfFamily M P) (i j : Fin 4) :
    StronglyCommute (P i) (P j) := by
  intro S T hS hT
  rw [← hM i S hS, ← hM j T hT]
  change M.proj (cylinder i S) (measurableSet_cylinder i hS)
        * M.proj (cylinder j T) (measurableSet_cylinder j hT)
      = M.proj (cylinder j T) (measurableSet_cylinder j hT)
        * M.proj (cylinder i S) (measurableSet_cylinder i hS)
  rw [M.proj_inter, M.proj_inter]
  exact M.proj_congr (Set.inter_comm _ _) _ _

/-! ## §3  The bundled data -/

/-- **Bundled Wightman spectral-condition + mass-gap data** for a relativistic Hilbert space `H`.

See the module docstring for the honesty caveats: the fields are the *defining properties* a
genuine construction would discharge.  The bundle is consistent (a degenerate one-dimensional
model inhabits it), but no *nontrivial* relativistic theory inhabits it until such a
construction exists; downstream "if a mass gap holds, then …" developments may take it as a
hypothesis. -/
structure RelativisticSpectralData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The energy-momentum generators `P⁰` (Hamiltonian), `P¹`, `P²`, `P³`. -/
  P : Fin 4 → SelfAdjointOperator H
  /-- Pairwise **strong** commutativity — the Nelson-safe notion, not algebraic `Commute`.  This is
  the primitive physical hypothesis; it is redundant given `jointPVM_marginal`
  (`RelativisticSpectralData.stronglyCommute_of_marginal`). -/
  stronglyCommute : ∀ i j, StronglyCommute (P i) (P j)
  /-- The joint spectral measure on spacetime-momentum space `ℝ⁴`. -/
  jointPVM : ProjValMeasure' H (EuclideanSpace ℝ (Fin 4))
  /-- The joint measure marginalizes to each generator's spectral projection. -/
  jointPVM_marginal : IsJointOfFamily jointPVM P
  /-- The vacuum: a distinguished unit vector. -/
  vacuum : H
  vacuum_unit : ‖vacuum‖ = 1
  /-- **Spectral condition (W2):** no joint spectral weight outside the closed forward light
  cone. -/
  spectral_condition :
    jointPVM.proj closedForwardLightConeᶜ measurableSet_closedForwardLightCone.compl = 0
  /-- **Uniqueness of the vacuum (W3):** the joint spectral weight exactly at `p = 0` is the
  rank-one projector onto the vacuum line. -/
  vacuum_unique :
    jointPVM.proj {0} measurableSet_singleton_zero = rankOneProjection vacuum
  /-- **Mass gap:** for some `Δ > 0`, no joint spectral weight in the forbidden annulus. -/
  mass_gap : ∃ Δ : ℝ, 0 < Δ ∧
    jointPVM.proj (massGapAnnulus Δ) (measurableSet_massGapAnnulus Δ) = 0

namespace RelativisticSpectralData

variable (D : RelativisticSpectralData H)

/-- **The `stronglyCommute` field is redundant.**  Pairwise strong commutativity of the
generators already follows from the marginal condition, via
`stronglyCommute_of_isJointOfFamily`.  (Recorded as a sanity check: were the `n`-ary spectral
theorem available to *build* `jointPVM` from strong commutativity, this field could be
dropped.) -/
theorem stronglyCommute_of_marginal (i j : Fin 4) : StronglyCommute (D.P i) (D.P j) :=
  stronglyCommute_of_isJointOfFamily D.jointPVM_marginal i j

/-- **The vacuum weight is a genuine projection.**  The joint spectral weight at `p = 0` is a star
projection (self-adjoint idempotent) — the rank-one vacuum projector `|Ω⟩⟨Ω|` — forced by the unit
vacuum together with `vacuum_unique`. -/
theorem isStarProjection_proj_zero :
    IsStarProjection (D.jointPVM.proj {0} measurableSet_singleton_zero) := by
  rw [D.vacuum_unique]
  exact isStarProjection_rankOneProjection D.vacuum_unit

end RelativisticSpectralData

end Spectra.QuantumFieldTheory.Wightman

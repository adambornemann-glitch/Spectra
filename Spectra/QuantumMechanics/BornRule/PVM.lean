/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.SelfAdjoint
import Spectra.ProjValMeasure.Basic
import Spectra.SpectralTheory.Measure.Polarized
import Spectra.SpectralTheory.Measure.PVM
import Spectra.Resolvent.SpectralRepresentation
import Spectra.QuantumMechanics.Unitarity.Basic
/-!
# The Born rule

The Born rule is the assignment that turns a **state** and an **observable** into the
classical probability law of the observable's measurement outcomes.  In its sharp
(projective) form on a pure state `ψ` with `‖ψ‖ = 1`, the probability that a measurement
of the self-adjoint operator `A` returns a value in a Borel set `B ⊆ ℝ` is

  `P(outcome ∈ B) = ‖E_A(B) ψ‖²  =  ⟪ψ, E_A(B) ψ⟫`,

where `E_A` is the projection-valued measure of `A`.  This file does **not** re-prove the
analysis; it *relabels* and *assembles* machinery already built elsewhere in Spectra under
the names that make the physical content explicit.

## Main definitions

* `bornMeasure` — the Born measure of a pure state `ψ` against a resolution of the identity
  `P`, i.e. the diagonal scalar measure `P.diag ψ`; the physics-facing name for the outcome
  law of a sharp single-observable measurement.

## Main results

* `isProbabilityMeasure_bornMeasure` — for a unit vector the Born measure has total mass `1`.
* `born_rule` — **the Born rule (projection form)**: `((bornMeasure P ψ) B).toReal =
  ‖P.proj B hB ψ‖ ^ 2`.
* `born_rule_ennreal` — the `ℝ≥0∞`-valued restatement of `born_rule`.
* `born_rule_le` — Born probabilities are bounded by `‖ψ‖²` (by `1` for a unit vector).

All four results are one-line consequences of already-proved `ProjValMeasure` lemmas
(`norm_sq_proj_apply`, `diag_univ_toReal`, `norm_proj_apply_le`); there is no `sorry` and no
new analysis here.

## Implementation notes

The kinematic core of the rule lives in `ProjValMeasure`, under operator-theoretic names:

* `Spectra.ProjValMeasure.norm_sq_proj_apply` : `‖P.proj B hB ξ‖² = ((P.diag ξ) B).toReal`.
  **This is the projection form of the Born rule.**  `bornMeasure` and `born_rule` below
  are its physics-facing aliases.
* `Spectra.ProjValMeasure.diag_univ_toReal` : `((P.diag ξ) univ).toReal = ‖ξ‖²`.
  This is the normalization that makes `bornMeasure` a probability measure for `‖ξ‖ = 1`.
* `Spectra.ProjValMeasure.{isSelfAdjoint_proj, proj_idem, proj_union, norm_proj_apply_le}`
  are the resolution-of-identity facts the rule rests on.

The bridge from a `SelfAdjointOperator` to its PVM — the existence half of the keystone
`∃! P, (resolvent formula against P.diag)`, with uniqueness `ProjValMeasure.ext_of_diag` —
is `spectralPVM` (`SpectralTheory.Measure.PVM` / `SpectralTheory.ResolventForm`, built on the
StoneFormula / Herglotz / CayleyTransform stack).  The observable-level Born measure that
composes `spectralPVM` with `bornMeasure` lives in `BornRule.Observable`.  This file stays at
the PVM level: every declaration below is a proved consequence of the `ProjValMeasure` lemmas
above.

The general (mixed-state) rule `B ↦ Tr(ρ E(B))` for a density operator `ρ` — the form Gleason
produces and the form `InformationGeometry.CramerRao.Quantum` / `FisherModel` consume — needs
trace-class / `DensityOperator` and lives elsewhere; `bornMeasure` here is pure-state only
(`P.diag : H → Measure ℝ`).  Joint spectral measures for a commuting family (and the
non-existence of a joint law for non-commuting observables), which make `Uncertainty` and
`BellsTheorem` theorems *about* the Born rule, likewise live in their own files; only the
single-observable marginal lives here.

## References

* M. Born, *Zur Quantenmechanik der Stoßvorgänge*, Z. Phys. **37** (1926), 863–867
  (the probabilistic interpretation; the `|ψ|²` correction is the footnote added in proof).
* [von Neumann, *Mathematische Grundlagen der Quantenmechanik*][vN1932] (the operator form).
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapters 7, 9–10.
* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*], §VIII
  (spectral measures) and [*IV: Analysis of Operators*] (the spectral resolution of a
  self-adjoint operator).

## Tags

Born rule, projection-valued measure, spectral measure, outcome probability, quantum
measurement
-/

open MeasureTheory Complex
open scoped InnerProductSpace
open Spectra Spectra.ProjValMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.BornRule

namespace PVM

/-! ## §1  The Born measure (projection-valued-measure level)

These statements need only a `ProjValMeasure`; they are immediate from the existing
`ProjValMeasure` lemmas.  They are the Born rule for a *sharp measurement of a single
observable on a pure state*, with the observable presented through its PVM.  Every
declaration here is fully proved (no `sorry`). -/

/-- The **Born measure** of a state `ψ` against a resolution of the identity `P`: the
probability law of the measurement outcomes.  Definitionally the diagonal scalar measure
`P.diag ψ = ⟪ψ, P.proj · ψ⟫`; this name records its physical meaning. -/
noncomputable def bornMeasure (P : ProjValMeasure H) (ψ : H) : Measure ℝ :=
  P.diag ψ

/-- For a unit vector the Born measure is a genuine probability measure.
Proof: `P.diag_univ_toReal ψ` gives total mass `‖ψ‖² = 1`; with `P.diag_finite` this is
`(bornMeasure P ψ) univ = 1`. -/
lemma isProbabilityMeasure_bornMeasure (P : ProjValMeasure H) {ψ : H}
    (hψ : ‖ψ‖ = 1) : IsProbabilityMeasure (bornMeasure P ψ) := by
  refine ⟨(ENNReal.toReal_eq_one_iff _).mp ?_⟩
  change ((P.diag ψ) Set.univ).toReal = 1
  rw [P.diag_univ_toReal, hψ, one_pow]

/-- **The Born rule (projection form).**  The probability that a measurement
lands in `B` equals the squared norm of the projected state.
Proof: `(P.norm_sq_proj_apply B hB ψ).symm`. -/
theorem born_rule (P : ProjValMeasure H) (ψ : H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ((bornMeasure P ψ) B).toReal = ‖P.proj B hB ψ‖ ^ 2 :=
  (P.norm_sq_proj_apply B hB ψ).symm

/-- The `ℝ≥0∞`-valued restatement, convenient when the measure is consumed
directly.  Proof: `born_rule` plus `ENNReal.ofReal_toReal (measure_ne_top _ _)`. -/
lemma born_rule_ennreal (P : ProjValMeasure H) (ψ : H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (bornMeasure P ψ) B = ENNReal.ofReal (‖P.proj B hB ψ‖ ^ 2) := by
  change (P.diag ψ) B = ENNReal.ofReal (‖P.proj B hB ψ‖ ^ 2)
  rw [P.norm_sq_proj_apply B hB ψ, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Born probabilities are bounded by `‖ψ‖²` (by `1` for a unit vector).
Proof: `P.norm_proj_apply_le` and `born_rule`. -/
lemma born_rule_le (P : ProjValMeasure H) (ψ : H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ((bornMeasure P ψ) B).toReal ≤ ‖ψ‖ ^ 2 := by
  rw [born_rule P ψ hB]
  exact pow_le_pow_left₀ (norm_nonneg _) (P.norm_proj_apply_le B hB ψ) 2

end PVM
end Spectra.QuantumMechanics.BornRule

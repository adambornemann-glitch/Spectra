/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
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

## What is already done, and where it lives

The kinematic core of the rule is a theorem you have already proved, under an
operator-theoretic name:

* `Spectra.ProjValMeasure.norm_sq_proj_apply` : `‖P.proj B hB ξ‖² = ((P.diag ξ) B).toReal`.
  **This is the projection form of the Born rule.**  `bornMeasure` and `born_rule` below
  are its physics-facing aliases.
* `Spectra.ProjValMeasure.diag_univ_toReal` : `((P.diag ξ) univ).toReal = ‖ξ‖²`.
  This is the normalization that makes `bornMeasure` a probability measure for `‖ξ‖ = 1`.
* `Spectra.ProjValMeasure.{isSelfAdjoint_proj, proj_idem, proj_union, norm_proj_apply_le}`
  are the resolution-of-identity facts the rule rests on.

What is **not** done is the bridge from a `SelfAdjointOperator` to its PVM — the existence
half of your keystone `∃! P, (resolvent formula against P.diag)`.  Its uniqueness half is
`ProjValMeasure.ext_of_diag`; its existence half is `spectralPVM`, which you are building
on the StoneFormula / Herglotz / CayleyTransform stack.  Until `spectralPVM` lands, every
declaration tagged `[needs spectralPVM]` below is conditional on it.

## Status legend (per declaration)

* `[done]`            — a one-line alias/consequence of an existing, proved lemma.
* `[needs spectralPVM]` — correct as stated, blocked only on the observable→PVM construction.
* `[needs infra]`     — blocked on infrastructure not present in the manifest
                        (trace-class / density operators, POVMs, joint spectral measures,
                        a position observable, or the `InformationGeometry` weld).

## Conceptual map (what "the Born rule" still owes the rest of the library)

1. **Mixed states.** `bornMeasure` is pure-state only (`P.diag : H → Measure ℝ`).  The
   general rule is `B ↦ Tr(ρ E(B))` for a density operator `ρ`.  Requires trace-class /
   `DensityOperator`, which is not yet in Spectra.  This is the form Gleason produces and
   the form `InformationGeometry.CramerRao.Quantum` / `FisherModel` consume.
2. **The relational layer.** Joint spectral measures for a *commuting* family (and the
   non-existence of a joint law for non-commuting observables) are what make `Uncertainty`
   and `BellsTheorem` theorems *about* the Born rule.  Only the single-observable marginal
   lives here.
3. **The weld.** `(state, observable) ↦ Measure ℝ` is the functor `InformationGeometry`
   reasons about as a `StatisticalModel`.  Naming that functor is what finally connects the
   spectral half of the library to the statistical half.

## References

* M. Born, *Zur Quantenmechanik der Stoßvorgänge*, Z. Phys. **37** (1926), 863–867
  (the probabilistic interpretation; the `|ψ|²` correction is the footnote added in proof).
* [von Neumann, *Mathematische Grundlagen der Quantenmechanik*][vN1932] (the operator form).
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapters 7, 9–10.
-/

open MeasureTheory Complex
open scoped InnerProductSpace
open Spectra Spectra.ProjValMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics.BornRule

namespace PVM

/-! ## §1  The Born measure (projection-valued-measure level)

These statements need only a `ProjValMeasure`; they are immediate from your existing
`ProjValMeasure` lemmas.  They are the Born rule for a *sharp measurement of a single
observable on a pure state*, with the observable presented through its PVM. -/

/-- The **Born measure** of a state `ψ` against a resolution of the identity `P`: the
probability law of the measurement outcomes.  Definitionally the diagonal scalar measure
`P.diag ψ = ⟪ψ, P.proj · ψ⟫`; this name records its physical meaning. -/
noncomputable def bornMeasure (P : ProjValMeasure H) (ψ : H) : Measure ℝ :=
  P.diag ψ

/-- `[done]` For a unit vector the Born measure is a genuine probability measure.
Proof: `P.diag_univ_toReal ψ` gives total mass `‖ψ‖² = 1`; with `P.diag_finite` this is
`(bornMeasure P ψ) univ = 1`. -/
lemma isProbabilityMeasure_bornMeasure (P : ProjValMeasure H) {ψ : H}
    (hψ : ‖ψ‖ = 1) : IsProbabilityMeasure (bornMeasure P ψ) := by
  refine ⟨(ENNReal.toReal_eq_one_iff _).mp ?_⟩
  show ((P.diag ψ) Set.univ).toReal = 1
  rw [P.diag_univ_toReal, hψ, one_pow]

/-- `[done]` **The Born rule (projection form).**  The probability that a measurement
lands in `B` equals the squared norm of the projected state.
Proof: `(P.norm_sq_proj_apply B hB ψ).symm`. -/
theorem born_rule (P : ProjValMeasure H) (ψ : H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ((bornMeasure P ψ) B).toReal = ‖P.proj B hB ψ‖ ^ 2 :=
  (P.norm_sq_proj_apply B hB ψ).symm

/-- `[done]` The `ℝ≥0∞`-valued restatement, convenient when the measure is consumed
directly.  Proof: `born_rule` plus `ENNReal.ofReal_toReal (measure_ne_top _ _)`. -/
lemma born_rule_ennreal (P : ProjValMeasure H) (ψ : H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (bornMeasure P ψ) B = ENNReal.ofReal (‖P.proj B hB ψ‖ ^ 2) := by
  show (P.diag ψ) B = ENNReal.ofReal (‖P.proj B hB ψ‖ ^ 2)
  rw [P.norm_sq_proj_apply B hB ψ, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- `[done]` Born probabilities are bounded by `‖ψ‖²` (by `1` for a unit vector).
Proof: `P.norm_proj_apply_le` and `born_rule`. -/
lemma born_rule_le (P : ProjValMeasure H) (ψ : H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ((bornMeasure P ψ) B).toReal ≤ ‖ψ‖ ^ 2 := by
  rw [born_rule P ψ hB]
  exact pow_le_pow_left₀ (norm_nonneg _) (P.norm_proj_apply_le B hB ψ) 2

end PVM
end Spectra.QuantumMechanics.BornRule

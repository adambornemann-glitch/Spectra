/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.PVM
import Spectra.QuantumMechanics.BornRule.Moments
import Spectra.Operator.SelfAdjoint
import Spectra.ProjValMeasure.Basic
import Spectra.SpectralTheory.Weak
import Spectra.SpectralTheory.Spectrum
import Spectra.Resolvent.SpectralRepresentation
import Mathlib.MeasureTheory.Measure.Support
/-!
# §3 The observable layer

Everything here is the *physics* object: a `SelfAdjointOperator` and its outcome law, as
opposed to the abstract PVM-level statements in `BornRule.PVM`/`BornRule.Moments` that this
file specializes.

## Main definitions

* `Spectra.Operator.SelfAdjointOperator.spectralPVM` — the projection-valued measure of a
  self-adjoint operator, built via Stone's theorem (`YosidaHille.genToGroup`) and `toPVM`.
* `Spectra.Operator.SelfAdjointOperator.bornMeasure` — the Born measure of a state `ψ` for
  a given observable `A`, i.e. `BornRule.PVM.bornMeasure A.spectralPVM ψ`.

## Main results

* `born_rule` : the Born measure of a Borel set is the squared norm of the spectral
  projection, `((A.bornMeasure ψ) B).toReal = ‖A.spectralPVM.proj B hB ψ‖ ^ 2`.
* `isProbabilityMeasure_bornMeasure` : the outcome law is a probability measure for unit `ψ`.
* `bornExpectation_eq_inner` : the first-moment identity `∫ λ dμ_ψ = ⟪ψ, Aψ⟫`, supplied by
  the weak spectral theorem `SpectralTheory.spectralPVM_integral_id`.
* `bornVariance_eq_central_moment` : the second central moment equals `‖(A − ⟨A⟩)ψ‖²`, the
  exact quantity the Robertson inequality bounds.
* `bornMeasure_support_subset_spectrum` : no measurement outcome occurs outside
  `spectrum A.toLinearPMap`.

All five results are fully discharged (no `sorry`); this file closes §3 of the Born-rule arc.

## References

See `PVM.lean`'s module docstring for the Born-rule references this section's arc builds on.
-/
open MeasureTheory Complex
open scoped InnerProductSpace Topology
open Spectra Spectra.ProjValMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics
open SpectralTheory PVM

/-- `[done]` **The keystone construction.**  The projection-valued measure of a self-adjoint
operator, i.e. the existence half of `∃! P, (resolvent formula against P.diag)`.

Defined as
`SpectralTheory.spectralPVM A.selfAdjoint = (YosidaHille.genToGroup A.selfAdjoint).toPVM`:
the self-adjoint generator is exponentiated to a strongly continuous one-parameter unitary
group by Stone's theorem, and that group's `toPVM` bundles the resolution of the identity.
All five `ProjValMeasure` fields are genuinely discharged through the Stone / Cayley / Herglotz
stack — `#print axioms` reports only `propext, Classical.choice, Quot.sound`, no `sorry`. This
is the bridge from "an abstract PVM has the Born properties" to "every observable has a Born
measure." -/
noncomputable def _root_.Spectra.Operator.SelfAdjointOperator.spectralPVM
    (A : Spectra.Operator.SelfAdjointOperator H) : ProjValMeasure H :=
  Spectra.QuantumMechanics.SpectralTheory.PVM.spectralPVM A.selfAdjoint

/-- `[done]` The Born measure of a state for a given observable. -/
noncomputable def _root_.Spectra.Operator.SelfAdjointOperator.bornMeasure
    (A : Spectra.Operator.SelfAdjointOperator H) (ψ : H) : Measure ℝ :=
  BornRule.PVM.bornMeasure A.spectralPVM ψ

namespace BornRule.Observable
open Spectra.Operator SelfAdjointOperator
open BornRule.PVM

/-- `[done]` **The Born rule, observable form.**  Probability of an outcome in
`B` for a measurement of `A` in state `ψ`.  Proof: `BornRule.PVM.born_rule A.spectralPVM ψ hB`. -/
theorem born_rule (A : SelfAdjointOperator H) (ψ : H)
    {B : Set ℝ} (hB : MeasurableSet B) :
    ((A.bornMeasure ψ) B).toReal = ‖A.spectralPVM.proj B hB ψ‖ ^ 2 :=
  BornRule.PVM.born_rule A.spectralPVM ψ hB

/-- `[done]` For a unit vector, the outcome law is a probability measure. -/
theorem isProbabilityMeasure_bornMeasure (A : SelfAdjointOperator H) {ψ : H}
    (hψ : ‖ψ‖ = 1) : IsProbabilityMeasure (A.bornMeasure ψ) :=
  BornRule.PVM.isProbabilityMeasure_bornMeasure A.spectralPVM hψ

open QuantumMechanics.BornRule.Moments
/-- `[done]` **Expectation ↔ matrix element.**  The mean of the Born measure is
the diagonal matrix element `⟪ψ, A ψ⟫` (real, since `A` is self-adjoint), for `ψ` in the
domain of `A`.  This is the first-moment identity `∫ λ dμ_ψ = ⟪ψ, Aψ⟫`, now supplied by
`SpectralTheory.spectralPVM_integral_id` (the weak spectral theorem in `SpectralTheory.Weak`). -/
theorem bornExpectation_eq_inner (A : SelfAdjointOperator H) {ψ : H}
    (hψ : ψ ∈ A.domain) :
    bornExpectation A.spectralPVM ψ = (⟪ψ, A.toLinearPMap ⟨ψ, hψ⟩⟫_ℂ).re :=
  SpectralTheory.spectralPVM_integral_id A.selfAdjoint ψ hψ

/-- `[done]` **Variance as a squared norm.**  The second central moment of the
Born measure equals `‖(A − ⟨A⟩)ψ‖²` — the exact quantity the Robertson inequality bounds.
For `ψ ∈ D(A)`.  This is the bridge that makes §4 a statement about Born variances rather
than about operators in isolation; supplied by `SpectralTheory.spectralPVM_central_moment`. -/
theorem bornVariance_eq_central_moment (A : SelfAdjointOperator H) {ψ : H}
    (hψ : ψ ∈ A.domain) :
    bornVariance A.spectralPVM ψ
      = ‖A.toLinearPMap ⟨ψ, hψ⟩ - (bornExpectation A.spectralPVM ψ : ℂ) • ψ‖ ^ 2 :=
  SpectralTheory.spectralPVM_central_moment A.selfAdjoint ψ hψ

/-- `[done]` **Support inside the spectrum.**  No measurement outcome occurs outside the
spectrum of `A`: the support of the Born measure is contained in `spectrum A.toLinearPMap`
(the resolvent-set complement, `Spectra.Resolvent.spectrum`).  Proof: if `λ ∉ spectrum`
(i.e. `↑λ` is in the resolvent set) then a neighborhood of `λ` carries no spectral projection
(`SpectralTheory.spectralPVM_proj_Ioo_eq_zero_of_mem_resolventSet`), hence zero Born mass
(`norm_sq_proj_apply`), contradicting membership in the support. -/
theorem bornMeasure_support_subset_spectrum (A : SelfAdjointOperator H) (ψ : H) :
    (bornMeasure A.spectralPVM ψ).support ⊆ Spectra.Resolvent.spectrum A.toLinearPMap := by
  haveI : IsFiniteMeasure (A.spectralPVM.diag ψ) := A.spectralPVM.diag_finite ψ
  intro lam hlam
  change (lam : ℂ) ∉ Spectra.Resolvent.resolventSet A.toLinearPMap
  intro hres
  obtain ⟨ε, hε, hzero⟩ :=
    SpectralTheory.spectralPVM_proj_Ioo_eq_zero_of_mem_resolventSet A.selfAdjoint hres
  have hpz : A.spectralPVM.proj (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo = 0 := hzero
  have hnorm :=
    A.spectralPVM.norm_sq_proj_apply (Set.Ioo (lam - ε) (lam + ε)) measurableSet_Ioo ψ
  rw [hpz, ContinuousLinearMap.zero_apply, norm_zero] at hnorm
  have hmass : bornMeasure A.spectralPVM ψ (Set.Ioo (lam - ε) (lam + ε)) = 0 := by
    have htoReal : ((A.spectralPVM.diag ψ) (Set.Ioo (lam - ε) (lam + ε))).toReal = 0 := by
      rw [← hnorm]; norm_num
    rcases (ENNReal.toReal_eq_zero_iff _).mp htoReal with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  have hnhds : Set.Ioo (lam - ε) (lam + ε) ∈ 𝓝 lam :=
    Ioo_mem_nhds (sub_lt_self lam hε) (lt_add_of_pos_right lam hε)
  exact (Measure.notMem_support_iff_exists.mpr
    ⟨Set.Ioo (lam - ε) (lam + ε), hnhds, hmass⟩) hlam

end BornRule.Observable
end Spectra.QuantumMechanics

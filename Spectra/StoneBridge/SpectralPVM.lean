/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.StoneBridge.Basic
import Spectra.SpectralTheory.ResolventForm
import Spectra.CayleyTransform.Generator.Pushforward
import Spectra.OneParameterUnitaryGroup.PVM
/-!
# `spectralPVM` is the Cayley/Riesz–Markov spectral measure, pulled back

Von Neumann's own theorem (1929/1932), made explicit: the canonical `spectralPVM hA` — built from
the Yosida group `genToGroup hA`, and consumed everywhere else in this library (`JointPVM`,
`BornRule`, `Observable`, `pmapOfPVM`, `StoneFormula`, the hydrogen-spectrum work) — is literally
the projection-valued measure of the **Cayley/Borel** group `stoneGroup hA`. Unfolded one step
further, its diagonal measures are the pushforward, under the inverse Möbius map, of the
Riesz–Markov spectral measure of the bounded unitary `cayley hA = (A-i)(A+i)⁻¹`.

Neither half of this is new analysis. `stoneGroup_eq_genToGroup` (`StoneBridge.Basic`) and
`borelMeasure_stoneGroup_eq_map` (`CayleyTransform.Generator.Pushforward`) were already proved,
independently, for different purposes — the former to identify two constructions of `e^{itA}`, the
latter as an internal step toward `generator_stoneGroup`. This file is the missing corollary that
connects both of them to `spectralPVM`, closing the loop the Cayley directory was built to close.

## Main results

* `spectralPVM_eq_groupPVM_stoneGroup` — `spectralPVM hA = groupPVM (stoneGroup hA)`, the one-line
  bridge (generator-uniqueness, transported through `groupPVM`).
* `spectralPVM_diag_eq_map_cayleySpectralMeasure` — unfolded to measures: the honest classical
  statement that `A`'s spectral measure is the pushforward of its Cayley transform's Riesz–Markov
  measure.
* `spectralPVM_proj_eq_spectralProjection_stoneGroup` — the operator-valued form of the bridge.
* `groupPVM_eq_toPVM` — records that `SpectralTheory.ResolventForm.groupPVM` is, by definition,
  `OneParameterUnitaryGroup.toPVM` — `groupPVM` is now an alias for `toPVM`, not a second
  construction, so the two names stay visibly interchangeable wherever a proof still reaches for
  `groupPVM` (the `AxiomCheck`-gated `spectralPVM`/`spectralPVM_resolvent_formula`) instead of
  `.toPVM` (`Spectra.Operator.SelfAdjointOperator.spectralPVM`,
  `QuantumMechanics.BornRule.Observable`).
-/
open MeasureTheory
open scoped InnerProductSpace
open Spectra.YosidaHille Spectra.Cayley Spectra.OneParameterUnitaryGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

namespace Spectra.QuantumMechanics.SpectralTheory

/-- `groupPVM` (`SpectralTheory.ResolventForm`) is definitionally `.toPVM`
(`OneParameterUnitaryGroup.PVM`) — the two historical names for "the PVM of a one-parameter
unitary group" resolve to one construction, so this is `rfl`. -/
theorem groupPVM_eq_toPVM (U : OneParameterUnitaryGroup (H := H)) :
    groupPVM U = U.toPVM := rfl

/-- **The bridge.** `spectralPVM`, built from the Yosida group `genToGroup`, equals the
projection-valued measure of `stoneGroup`, built from the Cayley transform — because the two
groups are the same group (`stoneGroup_eq_genToGroup`: generator-uniqueness, no measure
comparison needed). -/
theorem spectralPVM_eq_groupPVM_stoneGroup [Nontrivial H] (hA : IsSelfAdjoint A) :
    spectralPVM hA = groupPVM (stoneGroup hA) := by
  change groupPVM (genToGroup hA) = groupPVM (stoneGroup hA)
  rw [stoneGroup_eq_genToGroup hA]

/-- The `.toPVM` form of the bridge, for readers who reach `spectralPVM` through the
`OneParameterUnitaryGroup.toPVM` route (e.g. `Spectra.Operator.SelfAdjointOperator.spectralPVM`)
instead of `groupPVM`. -/
theorem spectralPVM_eq_stoneGroup_toPVM [Nontrivial H] (hA : IsSelfAdjoint A) :
    spectralPVM hA = (stoneGroup hA).toPVM := by
  rw [spectralPVM_eq_groupPVM_stoneGroup hA, groupPVM_eq_toPVM]

/-- The operator-valued form: `spectralPVM`'s spectral projections are literally the Cayley
group's spectral projections. -/
theorem spectralPVM_proj_eq_spectralProjection_stoneGroup [Nontrivial H] (hA : IsSelfAdjoint A) :
    (spectralPVM hA).proj = spectralProjection (stoneGroup hA) :=
  congrArg ProjValMeasure.proj (spectralPVM_eq_groupPVM_stoneGroup hA)

/-- **Von Neumann's theorem, stated.** The spectral measure of a self-adjoint operator is the
pushforward, under the inverse Möbius map, of the Riesz–Markov spectral measure of its bounded
Cayley transform `cayley hA = (A-i)(A+i)⁻¹`. Every self-adjoint operator's spectral theorem in this
library now reduces, in principle, to Riesz–Markov on a bounded unitary. -/
theorem spectralPVM_diag_eq_map_cayleySpectralMeasure [Nontrivial H] (hA : IsSelfAdjoint A)
    (ξ : H) :
    (spectralPVM hA).diag ξ
      = Measure.map (inverseMobiusReal hA)
          (Spectra.Riesz.spectralMeasure (cayley hA) (cayley_isStarNormal hA) ξ) := by
  rw [spectralPVM_diag hA, ← stoneGroup_eq_genToGroup hA]
  exact borelMeasure_stoneGroup_eq_map hA ξ

end Spectra.QuantumMechanics.SpectralTheory

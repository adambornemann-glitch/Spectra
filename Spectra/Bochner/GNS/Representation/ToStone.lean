/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Bochner/GNS/Representation/ToStone.lean
-/
import Spectra.Bochner.GNS.Representation.StronglyEx
import Spectra.Bochner.GNS.Representation.Cyclic
import Spectra.YosidaHille.Basic
/-!
# The GNS Unitary Group as a `OneParameterUnitaryGroup`

Repackages a `GNSUnitaryGroup` (built from formal sums over a positive-definite function) into
the standard `OneParameterUnitaryGroup` structure that feeds Stone's theorem.

## Main definitions

* `toOneParameterUnitaryGroup` — the repackaging, given a `GNSUnitaryGroup f`.

## Implementation notes

Each `U(t) = gns.unitaryAction t` is already known to preserve the inner product
(`gns.isometry`), so `LinearMap.isometryOfInner` turns it directly into a `LinearIsometry`, and
`LinearIsometry.toContinuousLinearMap` supplies continuity for free — no separate norm-squared
derivation or `mkContinuous` side-goal is needed.

## References

* Stone, "On one-parameter unitary groups in Hilbert space", Ann. of Math. (1932).
-/
namespace Spectra.Bochner.GNS

/-- The GNS unitary group satisfies all the axioms of a `OneParameterUnitaryGroup`
(`Spectra.OneParameterUnitaryGroup.Basic`). The map is:
  - `U : ℝ → H →L[ℂ] H`   from   `unitaryAction`
  - `unitary t ψ φ`         from   `isometry t ψ φ`
  - `group_law s t`          from   `group_law s t`
  - `identity`               from   `identity`
  - `strong_continuous`      from   `strong_continuous`
-/
noncomputable def toOneParameterUnitaryGroup {f : ℝ → ℂ}
    (gns : GNSUnitaryGroup f) :
    @OneParameterUnitaryGroup gns.H
    gns.instNACG gns.instIPS gns.instComplete := by
  letI := gns.instNACG
  letI := gns.instIPS
  haveI := gns.instComplete
  -- Each U(t) is a linear isometry (from the inner-product isometry hypothesis), hence continuous.
  set Uc : ℝ → (gns.H →L[ℂ] gns.H) :=
    fun t => ((gns.unitaryAction t).isometryOfInner (gns.isometry t)).toContinuousLinearMap
  exact {
    U := Uc
    unitary := fun t ψ φ => by
      simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner]
      exact gns.isometry t ψ φ
    group_law := fun s t => ContinuousLinearMap.ext fun ψ => by
      simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner,
        ContinuousLinearMap.comp_apply]
      exact (gns.group_law s t ψ)
    identity := ContinuousLinearMap.ext fun ψ => by
      simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner,
        ContinuousLinearMap.id_apply]
      exact gns.identity ψ
    strong_continuous := fun ψ => by
      exact (gns.strong_continuous ψ).congr fun t => by
        simp only [Uc, LinearIsometry.coe_toContinuousLinearMap, LinearMap.coe_isometryOfInner]
  }

end Spectra.Bochner.GNS

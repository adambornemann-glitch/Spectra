/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.GNS.Representation.Cyclic
import Spectra.Bochner.GNS.Representation.StronglyEx
import Spectra.OneParameterUnitaryGroup.Basic

/-!
# The GNS Unitary Group as a `OneParameterUnitaryGroup`

Repackages a `GNSUnitaryGroup` (built from formal sums over a positive-definite function) into
the standard `OneParameterUnitaryGroup` structure that feeds Stone's theorem.

## Main definitions

* `toOneParameterUnitaryGroup` — the repackaging, given a `GNSUnitaryGroup f`.

## Implementation notes

`GNSUnitaryGroup.unitaryAction` is already bundled as `H →L[ℂ] H` (built via
`LinearMap.isometryOfInner`/`.toContinuousLinearMap` in `Representation/UnitaryConstructor.lean`
at the point of construction), so this repackaging is a direct field-by-field forwarding — no
re-wrap, norm-squared derivation, or `mkContinuous` side-goal is needed here.

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
  exact {
    U := gns.unitaryAction
    unitary := gns.isometry
    group_law := fun s t => ContinuousLinearMap.ext fun ψ => gns.group_law s t ψ
    identity := ContinuousLinearMap.ext fun ψ => gns.identity ψ
    strong_continuous := gns.strong_continuous
  }

end Spectra.Bochner.GNS

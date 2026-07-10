/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.Borel.Measure.Basic
import Spectra.ProjValMeasure.Basic
import Spectra.SpectralTheory.Measure.Polarized
import Spectra.SpectralTheory.Algebra

/-!
# The Canonical PVM of a One-Parameter Unitary Group

Packages the projection-valued-measure algebra already built in `SpectralTheory/Measure/
Convergence.lean` (`spectralProjection`, `inner_spectralProjection_self`), `SpectralTheory/
Algebra.lean` (`spectralProjection_univ`, `spectralProjection_inter`), and `Bochner/Borel/CDF.lean`
(`borelMeasure`, `borelMeasure_isFiniteMeasure`) into a single `Spectra.ProjValMeasure H`
instance. No new mathematics happens here: every field of `toPVM` is one of those theorems
verbatim. The file exists so that "the PVM of `U_grp`" has one name for downstream consumers
(`SpectralTheory/Calculus/PMapOfPVM.lean`, `PMapSquareRoot.lean`, `SpectralTheory/Measure/
PVM.lean`) to import instead of re-assembling the six fields themselves.

`toPVM` is "canonical" in the sense of `ProjValMeasure.ext_of_diag`/`ext_of_proj`
(`ProjValMeasure/Basic.lean`): a PVM is determined by either its diagonal measures or its
projections alone, so any other construction agreeing with `toPVM` on `diag` (or `proj`) equals
it outright, not merely up to isomorphism. `SpectralTheory/ResolventForm.lean`'s `groupPVM` and
`SpectralTheory/Measure/PVM.lean`'s `PVM.spectralPVM` are aliases for `toPVM` (and, transitively,
for each other) under the names their respective developments were built against — not second
constructions; `StoneBridge/SpectralPVM.lean`'s `groupPVM_eq_toPVM` records the identification.

## Main definitions

* `toPVM` — the canonical `ProjValMeasure H` of a one-parameter unitary group.

## Main statements

None beyond the packaging: `toPVM`'s six fields are exactly the already-proved lemmas named
above, so there is nothing further to prove here.

## References

* Stone, "Linear Transformations in Hilbert Space" (1932), Chapter V (resolutions of the
  identity).
* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], §VII–VIII.
-/

open Spectra.Borel
open Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.OneParameterUnitaryGroup

/-- The canonical PVM of a strongly continuous one-parameter unitary group, assembled from its
already-proved spectral projections and Borel measures. "Canonical" in the sense of
`ProjValMeasure.ext_of_diag`: since a PVM is determined by its diagonal measures alone, `toPVM`
is *the* PVM agreeing with `borelMeasure U_grp` on the diagonal, not one choice among several. -/
noncomputable def toPVM
    (U_grp : OneParameterUnitaryGroup (H := H)) : Spectra.ProjValMeasure H where
  proj := spectralProjection U_grp
  diag := borelMeasure U_grp
  diag_finite := borelMeasure_isFiniteMeasure U_grp
  inner_proj := inner_spectralProjection_self U_grp
  proj_univ := spectralProjection_univ U_grp
  proj_inter := spectralProjection_inter U_grp

end Spectra.OneParameterUnitaryGroup

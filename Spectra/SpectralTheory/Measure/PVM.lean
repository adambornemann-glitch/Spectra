/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.ResolventForm

/-!
# The Spectral Measure, Under the `PVM` Namespace

`PVM.spectralPVM` is the `PVM`-namespace name for `SpectralTheory.spectralPVM`
(`SpectralTheory/ResolventForm.lean`) — the canonical `ProjValMeasure H` witnessing the spectral
theorem in resolvent form for a self-adjoint operator `A`. No new mathematics happens here: the two
are the same declaration under two names. `spectralPVM` was named for the resolvent-form
development it was proved alongside; `PVM.spectralPVM` is the name several downstream call sites
were already built against before the two constructions were unified into one — the Born-rule
observable bridge (`QuantumMechanics/BornRule/Observable.lean`), the hydrogen-spectrum files
(`QuantumMechanics/Hydrogen/Spectrum/`), `Modular/Cocycle/ModularVacuum.lean`,
`Resolvent/Residue.lean`, `SpectralTheory/Eigenspace.lean`, `SpectralTheory/Weak.lean`,
`SpectralTheory/Spectrum.lean`, and `SpectralTheory/Essential/Discrete.lean`. This file exists only
to keep that name resolving, not to construct anything new.

## Main definitions

* `PVM.spectralPVM` — an alias for `SpectralTheory.spectralPVM`.

## Main statements

* `PVM.spectralPVM_proj`, `PVM.spectralPVM_diag` — the alias unfolds to the same projections and
  diagonal measures as `SpectralTheory.spectralPVM` (both `rfl`, since the two are definitionally
  equal).

## References

* Stone, "Linear Transformations in Hilbert Space" (1932), Chapter V (resolutions of the
  identity) — see `SpectralTheory/ResolventForm.lean` for the construction these citations back.
-/

open Spectra.Borel
open Spectra.YosidaHille

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.SpectralTheory
namespace PVM

/-- **The spectral measure of a self-adjoint operator**, under the `PVM`-namespace name several
downstream files were built against: an alias for `SpectralTheory.spectralPVM`
(`SpectralTheory/ResolventForm.lean`) — the resolvent-form spectral theorem's canonical witness,
not a second construction of it. -/
noncomputable def spectralPVM {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    Spectra.ProjValMeasure H :=
  _root_.Spectra.QuantumMechanics.SpectralTheory.spectralPVM hA

/-- The alias's projections are exactly `SpectralTheory.spectralPVM`'s: the spectral projections
of the Yosida group `genToGroup hA`. -/
@[simp] lemma spectralPVM_proj {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    (spectralPVM hA).proj = spectralProjection (genToGroup hA) := rfl

/-- The alias's diagonal measures are exactly `SpectralTheory.spectralPVM`'s: the Borel measures
of the Yosida group `genToGroup hA`. -/
@[simp] lemma spectralPVM_diag {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    (spectralPVM hA).diag = borelMeasure (genToGroup hA) := rfl

end Spectra.QuantumMechanics.SpectralTheory.PVM

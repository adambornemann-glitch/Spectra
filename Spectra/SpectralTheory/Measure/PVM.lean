/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.OneParameterUnitaryGroup.PVM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.SpectralTheory
namespace PVM
/-- The spectral measure of a self-adjoint operator. -/
noncomputable def spectralPVM {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    Spectra.ProjValMeasure H :=
  (StonesTheorem.genToGroup hA).toPVM

end Spectra.QuantumMechanics.SpectralTheory.PVM

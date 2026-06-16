/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.Borel.Measure.Basic
import Spectra.ProjValMeasure.Basic
import Spectra.SpectralTheory.Measure.Polarized
import Spectra.SpectralTheory.Algebra

open Spectra.Borel
open Spectra.ProjValMeasure
open Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.OneParameterUnitaryGroup

/-- The canonical PVM of a strongly continuous one-parameter unitary group. -/
noncomputable def toPVM
    (U_grp : OneParameterUnitaryGroup (H := H)) : Spectra.ProjValMeasure H where
  proj := spectralProjection U_grp
  diag := borelMeasure U_grp
  diag_finite := borelMeasure_isFiniteMeasure U_grp
  inner_proj := inner_spectralProjection_self U_grp
  proj_univ := spectralProjection_univ U_grp
  proj_inter := spectralProjection_inter U_grp

end Spectra.OneParameterUnitaryGroup

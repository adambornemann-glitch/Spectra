/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.EssentialSpectrum
import Spectra.SpectralTheory.Essential.Smul

/-!
# The kinetic operator `−½Δ`

The textbook (atomic-units) hydrogen kinetic energy is `−½Δ`, obtained from the free Laplacian
`laplacianPMap = −Δ` by the real scaling `(½ : ℂ) • (−Δ)`.  This file uses the generic scaling
bridge (`Spectra.SpectralTheory.Essential.Smul`) to transport self-adjointness and the essential
spectrum across the rescaling rather than re-deriving them.

## Main statements

* `halfLaplacianPMap` — the textbook kinetic operator `−½Δ = (½ : ℂ) • (−Δ)`.
* `halfLaplacianPMap_domain` — the rescaling preserves the domain: `D(−½Δ) = D(−Δ)`.
* `halfLaplacianPMap_apply` — on that domain `−½Δ` acts as `½ • (−Δ)`.
* `halfLaplacian_isSelfAdjoint` — `−½Δ` is self-adjoint (`isSelfAdjoint_smul_real`).
* `essSpectrum_halfLaplacian` — `σ_ess(−½Δ) = ½·[0,∞) = [0,∞)` (`essSpectrum_smul_pos_Ici`).

These feed the textbook hydrogen Hamiltonian `−½Δ − Z/r` and its continuous spectrum.
-/

open Spectra.Sobolev Spectra.Essential

namespace Spectra.QuantumMechanics.Hydrogen

/-- The textbook kinetic operator `−½Δ = (½ : ℂ) • (−Δ)`. -/
noncomputable def halfLaplacianPMap : l2R3 →ₗ.[ℂ] l2R3 :=
  ((1 / 2 : ℝ) : ℂ) • laplacianPMap

/-- `−½Δ` is self-adjoint (real scaling of the self-adjoint `−Δ`). -/
lemma halfLaplacian_isSelfAdjoint : IsSelfAdjoint halfLaplacianPMap :=
  isSelfAdjoint_smul_real laplacian_isSelfAdjoint (1 / 2) (by norm_num)

/-- The scalar multiple `−½Δ` has the same domain as the free Laplacian `−Δ`. -/
@[simp] lemma halfLaplacianPMap_domain :
    halfLaplacianPMap.domain = laplacianPMap.domain := by
  rw [halfLaplacianPMap, LinearPMap.smul_domain]

/-- On its (shared) domain, `−½Δ` acts as `½` times the free Laplacian `−Δ`. -/
lemma halfLaplacianPMap_apply (ψ : halfLaplacianPMap.domain) :
    halfLaplacianPMap ψ = ((1 / 2 : ℝ) : ℂ) • laplacianPMap ψ :=
  smul_pmap_apply _ _ ψ

/-- **The essential spectrum of `−½Δ` is `[0, ∞)`** (scaling `σ_ess(−Δ) = [0,∞)` by `½ > 0`). -/
theorem essSpectrum_halfLaplacian :
    Spectra.Essential.essSpectrum halfLaplacian_isSelfAdjoint = Set.Ici (0 : ℝ) :=
  essSpectrum_smul_pos_Ici laplacian_isSelfAdjoint (1 / 2) (by norm_num) essSpectrum_laplacian

end Spectra.QuantumMechanics.Hydrogen

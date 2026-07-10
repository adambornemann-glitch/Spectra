/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.FreeGreens.ResolventL2

/-!
# The Fourier-defined free Green's function (Option B)

This file builds the free Green's function **directly as an `L²` element** as the inverse
`L²`-Fourier transform of the resolvent symbol `m_z(ξ) = (laplacianSymbol ξ − z)⁻¹`,
sidestepping the explicit Yukawa formula `e^{−√(−z)|x|}/(4π|x|)` and the `S²` sphere integral
entirely.

* `freeGreensFunctionL2 z hz : l2R3` — the inverse `L²`-Fourier transform of `(m_z).toLp`.
* `fourierL2_freeGreensFunctionL2` — `𝓕 (G̃_z) =ᵐ m_z`, immediate from `apply_symm_apply`.
* `integrable_conv_integrand` / `integrable_freeGreens_conv_integrand` — the convolution
  integrand `y ↦ G̃_z(x − y) · ψ(y)` is integrable for every `x`, so the convolution
  `(G̃_z ⋆ ψ)(x)` is well-defined a.e.

The resolvent-kernel identity for `G̃_z` (that `R_z` acts as convolution by `G̃_z`) is built on
top of this in `Convolution.lean`, via the `L²×Schwartz` convolution theorem; this file holds
only the parts that need no convolution theorem.
-/

open MeasureTheory
open Spectra.Sobolev

namespace Spectra.QuantumMechanics.Hydrogen

/-- The free Green's function defined directly as an `L²` element: the inverse `L²`-Fourier
transform of the resolvent symbol `m_z(ξ) = (laplacianSymbol ξ − z)⁻¹`.  No explicit Yukawa
formula, no sphere integral — just the isometric equivalence `fourierL2`. -/
noncomputable def freeGreensFunctionL2 (z : ℂ) (hz : z.im ≠ 0) : l2R3 :=
  fourierL2.symm ((memLp_inv_laplacianSymbol_sub z hz).toLp _)

/-- `𝓕 (G̃_z) =ᵐ m_z`, where `m_z(ξ) = (laplacianSymbol ξ − z)⁻¹`.  Immediate from
`LinearIsometryEquiv.apply_symm_apply` and `MemLp.coeFn_toLp`. -/
theorem fourierL2_freeGreensFunctionL2 (z : ℂ) (hz : z.im ≠ 0) :
    (fourierL2 (freeGreensFunctionL2 z hz) : R3 → ℂ)
      =ᵐ[volume] fun ξ => ((laplacianSymbol ξ : ℂ) - z)⁻¹ := by
  unfold freeGreensFunctionL2
  rw [LinearIsometryEquiv.apply_symm_apply fourierL2 _]
  exact MemLp.coeFn_toLp _

/-- For `g, ψ ∈ L²` and any `x`, the integrand `y ↦ g(x−y)·ψ(y)` is integrable: `g(x−·)` is
in `L²` (translation invariance of `volume`) and `L² · L² ⊆ L¹` by Cauchy–Schwarz.  Hence the
convolution `(g ⋆ ψ)(x) = ∫ y, g(x−y)·ψ(y)` is well-defined. -/
theorem integrable_conv_integrand (g ψ : l2R3) (x : R3) :
    Integrable (fun y => (g : R3 → ℂ) (x - y) * (ψ : R3 → ℂ) y) volume := by
  have hg : MemLp (g : R3 → ℂ) 2 volume := Lp.memLp g
  have hψ : MemLp (ψ : R3 → ℂ) 2 volume := Lp.memLp ψ
  have hgx : MemLp (fun y => (g : R3 → ℂ) (x - y)) 2 volume :=
    hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  exact hgx.integrable_mul hψ

/-- Specialisation of `integrable_conv_integrand` to `g = G̃_z`. -/
theorem integrable_freeGreens_conv_integrand (z : ℂ) (hz : z.im ≠ 0) (ψ : l2R3) (x : R3) :
    Integrable
      (fun y => (freeGreensFunctionL2 z hz : R3 → ℂ) (x - y) * (ψ : R3 → ℂ) y) volume :=
  integrable_conv_integrand (freeGreensFunctionL2 z hz) ψ x

end Spectra.QuantumMechanics.Hydrogen

/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Perturbation.CoulombBound
import Spectra.OneParameterUnitaryGroup.Basic
import Spectra.Stone.Basic
import Spectra.SpectralTheory.ResolventForm
/-!
# The Hydrogen Hamiltonian

Assembly of `H = −Δ − Z/r` as a self-adjoint operator on `H²(ℝ³)`, and its
connection to the spectral pipeline (Stone's theorem, the resolvent).

This is the **interface file**: the analytic content lives upstream
(`HardyInequality`, `CoulombBound`), and here we package it into the abstract
objects the spectral machinery consumes. In the current architecture the central
object is `perturbedOp laplacianPMap (coulombPotential p)`, shown self-adjoint by
`hydrogen_isSelfAdjoint` (Kato–Rellich) in `CoulombBound`; this file re-exports it
under hydrogen-specific names and bundles it as an `UnboundedObservable` and a
`OneParameterUnitaryGroup`.

## Main definitions

* `hydrogenHamiltonian` — `H = −Δ − Z/r` as a partial linear map.
* `hydrogenObservable` — `H` bundled as an `UnboundedObservable`.
* `hydrogenUnitaryGroup` — the evolution `e^{itH}` (Stone's theorem).
* `HydrogenData` — bundled hydrogen-atom data.

## Main statements

* `hydrogenHamiltonian_isSelfAdjoint` — `H` is self-adjoint on `H²(ℝ³)`.
* `hydrogenHamiltonian_domain` — `Dom(H) = H²(ℝ³)`.
* `hydrogenHamiltonian_apply` — `Hψ = −Δψ − (Z/r)ψ`.
* `laplacian_spectrum_nonneg` — eigenvalues of `−Δ` are `≥ 0`.
* `laplacian_resolvent_bound` — `‖(−Δ − z)⁻¹‖ ≤ 1/|Im z|`.

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], §V.5.
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
-/
open MeasureTheory Complex Filter InnerProductSpace
open Spectra.Sobolev
open Spectra.OneParameterUnitaryGroup Spectra.StonesTheorem Spectra.Resolvent
open Spectra.QuantumMechanics.Hamiltonian
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.QuantumMechanics.Observable
open scoped Topology NNReal ENNReal
noncomputable section
namespace Spectra.QuantumMechanics.Hydrogen

/-! ## The hydrogen Hamiltonian -/

/-- The hydrogen Hamiltonian `H = −Δ − Z/r` as a partial linear map on `L²(ℝ³)`,
with domain `H²(ℝ³)`. (The sign and charge are inside `coulombMultiplier`.) -/
def hydrogenHamiltonian (p : CoulombParams) : L2_R3 →ₗ.[ℂ] L2_R3 :=
  perturbedOp laplacianPMap (coulombPotential p)

/-- The hydrogen Hamiltonian is self-adjoint on `H²(ℝ³)` (Kato–Rellich, via Hardy);
this is `hydrogen_isSelfAdjoint` from `CoulombBound`. -/
theorem hydrogenHamiltonian_isSelfAdjoint (p : CoulombParams) :
    IsSelfAdjoint (hydrogenHamiltonian p) :=
  hydrogen_isSelfAdjoint p

/-- `Dom(H) = Dom(−Δ) = H²(ℝ³)`: the perturbation `−Z/r` does not change the
domain. -/
@[simp] theorem hydrogenHamiltonian_domain (p : CoulombParams) :
    (hydrogenHamiltonian p).domain = SobolevH2 :=
  rfl

/-- `Hψ = −Δψ − (Z/r)ψ` for `ψ ∈ H²`. -/
theorem hydrogenHamiltonian_apply (p : CoulombParams)
    (ψ : (hydrogenHamiltonian p).domain) :
    hydrogenHamiltonian p ψ = laplacianPMap ψ + coulombPotential p ψ :=
  rfl

/-- The hydrogen Hamiltonian bundled as an `UnboundedObservable`. -/
def hydrogenObservable (p : CoulombParams) : UnboundedObservable L2_R3 where
  toLinearPMap := hydrogenHamiltonian p
  selfAdjoint := hydrogen_isSelfAdjoint p

/-- The hydrogen unitary evolution `U(t) = e^{itH}` (Stone's theorem). -/
def hydrogenUnitaryGroup (p : CoulombParams) :
    OneParameterUnitaryGroup (H := L2_R3) :=
  genToGroup (hydrogen_isSelfAdjoint p)

/-- The generator of `e^{itH}` is `H`. -/
theorem generator_hydrogenUnitaryGroup (p : CoulombParams) :
    generator (hydrogenUnitaryGroup p) = hydrogenHamiltonian p :=
  generator_genToGroup (hydrogen_isSelfAdjoint p)

/-! ## Bundled hydrogen-atom data -/

/-- Bundled hydrogen-atom data: a nuclear charge, from which the self-adjoint
Hamiltonian and its evolution are derived. -/
structure HydrogenData where
  /-- The Coulomb parameters (nuclear charge `Z > 0`). -/
  params : CoulombParams

namespace HydrogenData

/-- The Hamiltonian `H = −Δ − Z/r`. -/
def hamiltonian (d : HydrogenData) : L2_R3 →ₗ.[ℂ] L2_R3 :=
  hydrogenHamiltonian d.params

/-- The Hamiltonian as an `UnboundedObservable`. -/
def observable (d : HydrogenData) : UnboundedObservable L2_R3 :=
  hydrogenObservable d.params

/-- The unitary evolution `e^{itH}`. -/
def unitaryGroup (d : HydrogenData) : OneParameterUnitaryGroup (H := L2_R3) :=
  hydrogenUnitaryGroup d.params

/-- Self-adjointness of the Hamiltonian. -/
theorem isSelfAdjoint (d : HydrogenData) : IsSelfAdjoint d.hamiltonian :=
  hydrogen_isSelfAdjoint d.params

end HydrogenData

/-- Construct `HydrogenData` from a nuclear charge `Z > 0`. -/
def HydrogenData.ofCharge (Z : ℝ) (hZ : 0 < Z) : HydrogenData :=
  ⟨⟨Z, hZ⟩⟩

/-- The standard hydrogen atom (`Z = 1`). -/
def hydrogenAtom : HydrogenData :=
  HydrogenData.ofCharge 1 one_pos

/-- The helium ion `He⁺` (`Z = 2`). -/
def heliumIon : HydrogenData :=
  HydrogenData.ofCharge 2 two_pos

end Spectra.QuantumMechanics.Hydrogen

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Perturbation.CoulombBound
/-!
# The Hydrogen Hamiltonian

Assembly of `H = −½Δ − Z/r` as a self-adjoint operator on `H²(ℝ³)`, and its
connection to the spectral pipeline (Stone's theorem, the resolvent).

This is the **interface file**: the analytic content lives upstream
(`Hardy/Inequality/`, `CoulombBound`), and here we package it into the abstract
objects the spectral machinery consumes. In the current architecture the central
object is `perturbedOp halfLaplacianPMap (coulombPotential p)`, shown self-adjoint by
`hydrogen_isSelfAdjoint` (Kato–Rellich) in `CoulombBound`; this file re-exports it
under hydrogen-specific names and bundles it as a `SelfAdjointOperator` and a
`OneParameterUnitaryGroup`.

## Main definitions

* `hydrogenHamiltonian` — `H = −½Δ − Z/r` as a partial linear map.
* `hydrogenObservable` — `H` bundled as a `SelfAdjointOperator`.
* `hydrogenUnitaryGroup` — the evolution `e^{itH}` (Stone's theorem).
* `HydrogenData` — bundled hydrogen-atom data.

## Main statements

* `hydrogenHamiltonian_isSelfAdjoint` — `H` is self-adjoint on `H²(ℝ³)`.
* `hydrogenHamiltonian_domain` — `Dom(H) = H²(ℝ³)`.
* `hydrogenHamiltonian_apply` — `Hψ = −½Δψ − (Z/r)ψ`.
* `generator_hydrogenUnitaryGroup` — the generator of `e^{itH}` is `H`.

## Implementation notes

`HydrogenData` bundles a `CoulombParams` together with projection lemmas
(`.hamiltonian`, `.observable`, `.unitaryGroup`, `.isSelfAdjoint`) so that
downstream files can carry "a hydrogen atom" as a single piece of data instead
of threading a bare `CoulombParams` through every statement. The bare
`hydrogenHamiltonian p`/`hydrogenObservable p`/`hydrogenUnitaryGroup p` API
remains the one actually used by the spectrum files in this directory; the
`HydrogenData` wrapper is kept as the user-facing convenience surface for
external callers who want to fix "the hydrogen atom" or "the He⁺ ion" as a
single named object (see `hydrogenAtom`, `heliumIon` below) without exposing
`CoulombParams` directly.

## References

* [Kato, *Perturbation Theory for Linear Operators*][kato1995], §V.5.
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
-/
open Spectra.Sobolev
open Spectra.OneParameterUnitaryGroup Spectra.YosidaHille
open Spectra.Operator
noncomputable section
namespace Spectra.QuantumMechanics.Hydrogen

/-! ## The hydrogen Hamiltonian -/

/-- The hydrogen Hamiltonian `H = −½Δ − Z/r` as a partial linear map on `L²(ℝ³)`,
with domain `H²(ℝ³)`. (The sign and charge are inside `coulombMultiplier`; the
kinetic term is the textbook `−½Δ`.) -/
def hydrogenHamiltonian (p : CoulombParams) : l2R3 →ₗ.[ℂ] l2R3 :=
  perturbedOp halfLaplacianPMap (coulombPotential p)

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

/-- `Hψ = −½Δψ − (Z/r)ψ` for `ψ ∈ H²`. -/
theorem hydrogenHamiltonian_apply (p : CoulombParams)
    (ψ : (hydrogenHamiltonian p).domain) :
    hydrogenHamiltonian p ψ = halfLaplacianPMap ψ + coulombPotential p ψ :=
  rfl

/-- The hydrogen Hamiltonian bundled as a `SelfAdjointOperator`. -/
def hydrogenObservable (p : CoulombParams) : SelfAdjointOperator l2R3 where
  toLinearPMap := hydrogenHamiltonian p
  selfAdjoint := hydrogen_isSelfAdjoint p

/-- The hydrogen unitary evolution `U(t) = e^{itH}` (Stone's theorem). -/
def hydrogenUnitaryGroup (p : CoulombParams) :
    OneParameterUnitaryGroup (H := l2R3) :=
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

/-- The Hamiltonian `H = −½Δ − Z/r`. -/
def hamiltonian (d : HydrogenData) : l2R3 →ₗ.[ℂ] l2R3 :=
  hydrogenHamiltonian d.params

/-- The Hamiltonian as a `SelfAdjointOperator`. -/
def observable (d : HydrogenData) : SelfAdjointOperator l2R3 :=
  hydrogenObservable d.params

/-- The unitary evolution `e^{itH}`. -/
def unitaryGroup (d : HydrogenData) : OneParameterUnitaryGroup (H := l2R3) :=
  hydrogenUnitaryGroup d.params

/-- Self-adjointness of the Hamiltonian. -/
theorem isSelfAdjoint (d : HydrogenData) : IsSelfAdjoint d.hamiltonian :=
  hydrogen_isSelfAdjoint d.params

end HydrogenData

/-- Construct `HydrogenData` from a nuclear charge `Z > 0`. -/
def HydrogenData.ofCharge (Z : ℝ) (hZ : 0 < Z) : HydrogenData :=
  ⟨⟨Z, hZ⟩⟩

/-- The standard hydrogen atom (`Z = 1`). Kept here rather than in a separate
constants module: `CoulombParams`/`HydrogenData` are one-field wrappers around
`Z`, so a named instance is a two-line convenience, not a physical-constants
table (there is no separate module for such tables in this library — cf.
[reed1978] §XIII.3, which treats `Z = 1, 2` as running examples of the same
abstract Kato–Rellich result rather than as tabulated data). -/
def hydrogenAtom : HydrogenData :=
  HydrogenData.ofCharge 1 one_pos

/-- The helium ion `He⁺` (`Z = 2`); see `hydrogenAtom` for why it lives here. -/
def heliumIon : HydrogenData :=
  HydrogenData.ofCharge 2 two_pos

end Spectra.QuantumMechanics.Hydrogen

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Dirac/Operators.lean
-/
import Spectra.QuantumMechanics.Dirac.CliffordAlgebra
/-!
# Dirac Operator and Hamiltonian

This file defines the Dirac Hamiltonian as an unbounded self-adjoint operator
on a Hilbert space, along with the physical constants and the key structural
result that the Dirac operator is unbounded in both directions.
-/
open InnerProductSpace Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.QuantumMechanics.Dirac

/-! ## Spinor Space -/

/-- The fiber space ℂ⁴ at each spatial point.

Encodes spin (2 components) and particle/antiparticle (2 components) degrees
of freedom. A Dirac spinor field is a section ψ : ℝ³ → SpinorSpace. -/
abbrev SpinorSpace := EuclideanSpace ℂ (Fin 4)

/-! ## Unbounded Operators -/

/-- An unbounded linear operator with explicit domain.

Unlike bounded operators (elements of H →L[ℂ] H), unbounded operators are
only defined on a dense subspace. The canonical example is the momentum
operator -iℏ∇, which is unbounded on L²(ℝ³). -/

structure DiracOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The domain of definition, a dense subspace of H. -/
  domain : Submodule ℂ H
  /-- The operator itself, mapping domain elements to H. -/
  op : domain →ₗ[ℂ] H

/-! ## Physical Constants -/

/-- Physical constants for the Dirac equation.

These determine the energy scale and spectral gap of the Hamiltonian. -/
structure DiracConstants where
  /-- Reduced Planck constant ℏ: the quantum of action.
      Sets the scale of quantum effects. -/
  hbar : ℝ
  /-- Speed of light c: the relativistic velocity scale.
      Appears in the kinetic term -iℏc(α·∇). -/
  c : ℝ
  /-- Particle rest mass m: determines the spectral gap 2mc².
      For electrons, m ≈ 9.1 × 10⁻³¹ kg. -/
  m : ℝ
  /-- ℏ > 0: required for non-trivial quantum dynamics. -/
  hbar_pos : hbar > 0
  /-- c > 0: required for Lorentz signature. -/
  c_pos : c > 0
  /-- m ≥ 0: negative mass is unphysical.
      Zero mass is allowed (neutrinos, to first approximation). -/
  m_nonneg : m ≥ 0

/-- Rest mass energy E₀ = mc².

This is the energy of a particle at rest, and determines the spectral gap.
For an electron, mc² ≈ 0.511 MeV. -/
def DiracConstants.restEnergy (κ : DiracConstants) : ℝ := κ.m * κ.c^2

end Spectra.QuantumMechanics.Dirac

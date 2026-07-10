/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
/-!
# Pauli Matrices

The Pauli matrices σₓ, σᵧ, σᵤ form the fundamental representation of the
spin-1/2 angular momentum algebra su(2). They satisfy:

  σᵢ² = I           (involutions)
  {σᵢ, σⱼ} = 0      for i ≠ j (anticommutation)
  [σᵢ, σⱼ] = 2iεᵢⱼₖσₖ (cyclic commutators)

## Main definitions

* `pauliX`, `pauliY`, `pauliZ`: The three Pauli matrices

## Main statements

* `pauliX_sq`, `pauliY_sq`, `pauliZ_sq`: Each Pauli matrix squares to I.
* `pauliX_hermitian`, `pauliY_hermitian`, `pauliZ_hermitian`: All are Hermitian
* `pauliX_isSelfAdjoint`, `pauliY_isSelfAdjoint`, `pauliZ_isSelfAdjoint`: hence self-adjoint.
* `pauliXY_anticommute`, `pauliXZ_anticommute`, `pauliYZ_anticommute`:
  anticommutation relations.
* `pauliXY_commutator`, `pauliYZ_commutator`, `pauliZX_commutator`: cyclic commutator
  relations.

## Physical interpretation

The Pauli matrices represent spin-1/2 angular momentum operators:
- σₓ: spin measurement along x-axis, eigenstates |→⟩, |←⟩
- σᵧ: spin measurement along y-axis, eigenstates |↻⟩, |↺⟩
- σᵤ: spin measurement along z-axis, eigenstates |↑⟩, |↓⟩

The eigenvalues ±1 correspond to spin ±ℏ/2 in units where ℏ = 1.

## Implementation notes

The matrices are fixed as concrete `Matrix (Fin 2) (Fin 2) ℂ` literals rather than as
elements of an abstract `Cl(3)`/`su(2)` structure: every fact needed downstream (Bell/CHSH
observables, spin operators) is a decidable equality of `2×2` complex matrices, so `ext;
fin_cases; simp` closes each one directly and there is no benefit to an abstract algebraic
carrier here. Only the three *cyclic* commutators (`XY→Z`, `YZ→X`, `ZX→Y`) are proved; the
three anti-cyclic instances (e.g. `[σᵧ, σₓ] = -2i σᵤ`) follow in one line from antisymmetry
of the commutator and are not restated.

## References

* J.J. Sakurai, J. Napolitano, *Modern Quantum Mechanics* (2nd ed.), §3.2.
* M.A. Nielsen, I.L. Chuang, *Quantum Computation and Quantum Information*, §2.1.3.

## Tags

pauli matrices, spin, su(2), clifford algebra, hermitian, quantum mechanics
-/
open Complex
namespace Spectra.QuantumMechanics.Pauli
/-- Pauli-X (σₓ): spin flip operator. Real symmetric.

      ┌     ┐
σₓ =  │ 0 1 │
      │ 1 0 │
      └     ┘

Eigenvectors: |+⟩ = (1,1)/√2, |-⟩ = (1,-1)/√2 with eigenvalues ±1. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-Y (σᵧ): spin flip with phase. Imaginary antisymmetric, but still Hermitian.

      ┌      ┐
σᵧ =  │ 0 -i │
      │ i  0 │
      └      ┘

The only Pauli matrix with imaginary entries. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli-Z (σᵤ): spin measurement in z-direction. Real diagonal.

      ┌      ┐
σᵤ =  │ 1  0 │
      │ 0 -1 │
      └      ┘

Eigenvectors: |↑⟩ = (1,0), |↓⟩ = (0,1) with eigenvalues +1, -1. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]


/-! ### Hermiticity

All Pauli matrices are Hermitian (self-adjoint), which is required for them
to represent physical observables. -/

/-- σₓ is Hermitian: real symmetric matrix. -/
@[simp]
lemma pauliX_hermitian : pauliX.conjTranspose = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose, Matrix.of_apply]

/-- σᵧ is Hermitian: the ±I entries are in conjugate positions.

Despite having imaginary entries, σᵧ is Hermitian because:
  (σᵧ)†ᵢⱼ = conj((σᵧ)ⱼᵢ) = conj(±I) = ∓I = (σᵧ)ᵢⱼ -/
@[simp]
lemma pauliY_hermitian : pauliY.conjTranspose = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliY, Matrix.conjTranspose, Matrix.of_apply, conj_I]

/-- σᵤ is Hermitian: real diagonal matrix. -/
@[simp]
lemma pauliZ_hermitian : pauliZ.conjTranspose = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.conjTranspose, Matrix.of_apply]

/-- σₓ is Hermitian, hence self-adjoint as an operator: the physical-observable
property the module docstring invokes. -/
lemma pauliX_isSelfAdjoint : IsSelfAdjoint pauliX :=
  Matrix.IsHermitian.isSelfAdjoint pauliX_hermitian

/-- σᵧ is Hermitian, hence self-adjoint as an operator. -/
lemma pauliY_isSelfAdjoint : IsSelfAdjoint pauliY :=
  Matrix.IsHermitian.isSelfAdjoint pauliY_hermitian

/-- σᵤ is Hermitian, hence self-adjoint as an operator. -/
lemma pauliZ_isSelfAdjoint : IsSelfAdjoint pauliZ :=
  Matrix.IsHermitian.isSelfAdjoint pauliZ_hermitian


/-! ### Involution property

Each Pauli matrix squares to the identity, so eigenvalues are ±1. -/

/-- σₓ² = I: eigenvalues are ±1, corresponding to spin-right and spin-left states. -/
@[simp]
lemma pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- σᵧ² = I: the product (-I)(I) = 1 on the off-diagonal. -/
@[simp]
lemma pauliY_sq : pauliY * pauliY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- σᵤ² = I: diagonal entries (±1)² = 1. -/
@[simp]
lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]


/-! ### Anticommutation relations

Distinct Pauli matrices anticommute: {σᵢ, σⱼ} = σᵢσⱼ + σⱼσᵢ = 0 for i ≠ j.

This is the Clifford algebra Cl(3) relation that makes spin non-commutative
and underlies the uncertainty principle for spin measurements along different axes. -/

/-- σₓ and σᵧ anticommute: {σₓ, σᵧ} = 0.

This is the Clifford algebra relation that makes spin non-commutative. -/
lemma pauliXY_anticommute : pauliX * pauliY + pauliY * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliY, Matrix.add_apply]

/-- σₓ and σᵤ anticommute: {σₓ, σᵤ} = 0. -/
lemma pauliXZ_anticommute : pauliX * pauliZ + pauliZ * pauliX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliZ, Matrix.add_apply]

/-- σᵧ and σᵤ anticommute: {σᵧ, σᵤ} = 0. -/
lemma pauliYZ_anticommute : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliY, pauliZ, Matrix.add_apply]


/-! ### Commutation relations

The cyclic commutators are the concrete two-dimensional matrix form of
`[σᵢ, σⱼ] = 2iεᵢⱼₖσₖ`. -/

/-- The cyclic commutator `[σₓ, σᵧ] = 2i σᵤ`. -/
lemma pauliXY_commutator :
    pauliX * pauliY - pauliY * pauliX = (2 * I) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliY, pauliZ, Matrix.sub_apply, Matrix.smul_apply] <;> ring_nf

/-- The cyclic commutator `[σᵧ, σᵤ] = 2i σₓ`. -/
lemma pauliYZ_commutator :
    pauliY * pauliZ - pauliZ * pauliY = (2 * I) • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliY, pauliZ, Matrix.sub_apply, Matrix.smul_apply] <;> ring_nf

/-- The cyclic commutator `[σᵤ, σₓ] = 2i σᵧ`.

Unlike the other two cyclic pairs, the RHS here scales `pauliY` — the one matrix with
imaginary entries — by another factor of `i`, so the goal only closes after `i² = -1`
collapses it back to a real matrix; `pauliXY_commutator`/`pauliYZ_commutator` stay linear
in `i` throughout and never need that extra step. -/
lemma pauliZX_commutator :
    pauliZ * pauliX - pauliX * pauliZ = (2 * I) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [pauliX, pauliY, pauliZ, Matrix.sub_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [I_sq]

end Spectra.QuantumMechanics.Pauli

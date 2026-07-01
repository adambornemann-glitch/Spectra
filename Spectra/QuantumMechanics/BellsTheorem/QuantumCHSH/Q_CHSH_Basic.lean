/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla
Ported by: Adam Bornemann
-/
import Spectra.QuantumMechanics.BellsTheorem.Basic
import Spectra.QuantumMechanics.PauliMatrices
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.NoncommRing

open Matrix Complex MatrixGroups

namespace Spectra.QuantumCHSH

/-! ## Pauli Matrices -/

/-- Pauli X matrix: σₓ = |0⟩⟨1| + |1⟩⟨0| -/
def σₓ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli Y matrix: σᵧ = -i|0⟩⟨1| + i|1⟩⟨0| -/
def σᵧ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- Pauli Z matrix: σ_z = |0⟩⟨0| - |1⟩⟨1| -/
def σ_z : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The 2×2 identity matrix -/
def I₂ : Matrix (Fin 2) (Fin 2) ℂ := 1

/-! ## Properties of Pauli Matrices

`σₓ`, `σᵧ`, `σ_z` are definitionally the matrices `Spectra.QuantumMechanics.Pauli.pauliX/Y/Z`
(both sides unfold to the same literal), so their properties reuse the canonical module's
proofs instead of re-deriving them from scratch. -/

section
open Spectra.QuantumMechanics.Pauli

lemma σₓ_hermitian : σₓ.IsHermitian := pauliX_hermitian

lemma σᵧ_hermitian : σᵧ.IsHermitian := pauliY_hermitian

lemma σ_z_hermitian : σ_z.IsHermitian := pauliZ_hermitian

lemma σₓ_sq : σₓ * σₓ = 1 := pauliX_sq

lemma σᵧ_sq : σᵧ * σᵧ = 1 := pauliY_sq

lemma σ_z_sq : σ_z * σ_z = 1 := pauliZ_sq

/-- Pauli matrices anticommute: σₓσ_z = -σ_zσₓ -/
lemma σₓ_σ_z_anticomm : σₓ * σ_z = -σ_z * σₓ := by
  show pauliX * pauliZ = -pauliZ * pauliX
  linear_combination (norm := noncomm_ring) pauliXZ_anticommute

end

/-! ## The Bell State -/

/-- The singlet (Bell) state |Ψ⁻⟩ = (|01⟩ - |10⟩)/√2 as a ket vector -/
noncomputable def ket_Ψ_minus : Fin 4 → ℂ := ![0, 1/Real.sqrt 2, -1/Real.sqrt 2, 0]

/-- The Bell state |Ψ⁻⟩ = (1/√2)(|01⟩ - |10⟩) as a density matrix -/
noncomputable def ρ_Ψ_minus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | (0, 1), (0, 1) =>  (1/2 : ℂ)
    | (0, 1), (1, 0) => -(1/2 : ℂ)
    | (1, 0), (0, 1) => -(1/2 : ℂ)
    | (1, 0), (1, 0) =>  (1/2 : ℂ)
    | _, _ => 0

lemma ρ_Ψ_minus_trace : ρ_Ψ_minus.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, ρ_Ψ_minus, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue]
  norm_num

end Spectra.QuantumCHSH

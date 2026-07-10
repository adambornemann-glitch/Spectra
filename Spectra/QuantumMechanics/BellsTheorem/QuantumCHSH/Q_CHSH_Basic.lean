/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla, by Adam Bornemann
-/
import Spectra.QuantumMechanics.BellsTheorem.Basic
import Spectra.QuantumMechanics.PauliMatrices
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing
/-!
# CHSH Building Blocks: Pauli Matrices and the Singlet State

Seeds the `Spectra.QuantumCHSH` port chain (`Correlations.lean`, `Violation.lean`,
`Tsirelson.lean`) with the Pauli matrices, the 2×2 identity, and the singlet Bell state, in the
naming convention of Echenim & Mhalla's Isabelle/HOL formalization.

## Main definitions

* `σₓ`, `σᵧ`, `σZ` : the Pauli matrices, re-exported from `Spectra.QuantumMechanics.Pauli`
* `I₂` : the 2×2 identity
* `ρΨMinus` : the singlet density matrix, re-exported from `Spectra.QuantumInfo.bellStatePsiMinus`

## Main results

* `σₓ_hermitian`, `σᵧ_hermitian`, `σZ_hermitian` : the Pauli matrices are Hermitian
* `σₓ_sq`, `σᵧ_sq`, `σZ_sq` : each Pauli matrix squares to the identity
* `σₓ_σZ_anticomm` : `σₓ` and `σZ` anticommute
* `ρΨMinus_trace` : the singlet density matrix has trace 1

## Implementation notes

`σₓ`, `σᵧ`, `σZ` are definitionally the matrices `Spectra.QuantumMechanics.Pauli.pauliX/Y/Z`
(both sides unfold to the same literal), so their properties reuse the canonical module's proofs
instead of re-deriving them from scratch. `ρΨMinus` is, likewise, a re-export of
`Spectra.QuantumInfo.bellStatePsiMinus` (`BellsTheorem/Basic.lean`) under this port chain's own
name, rather than an independent re-derivation of the same density matrix.

## References

* [Echenim, Mhalla, *A formalization of the CHSH inequality and Tsirelson's
  upper-bound in Isabelle/HOL*][echenim2023]

## Tags

chsh, bell state, pauli matrices, quantum information
-/
open Matrix Complex

namespace Spectra.QuantumCHSH

/-! ## Pauli Matrices -/

/-- Pauli X matrix: σₓ = |0⟩⟨1| + |1⟩⟨0| -/
def σₓ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- Pauli Y matrix: σᵧ = -i|0⟩⟨1| + i|1⟩⟨0| -/
def σᵧ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

/-- Pauli Z matrix: σZ = |0⟩⟨0| - |1⟩⟨1| -/
def σZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The 2×2 identity matrix, feeding `Correlations.lean`'s `kroneckerMap (· * ·) σZ I₂`-style
    tensor-product observables. -/
def I₂ : Matrix (Fin 2) (Fin 2) ℂ := 1

/-! ## Properties of Pauli Matrices

`σₓ`, `σᵧ`, `σZ` are definitionally the matrices `Spectra.QuantumMechanics.Pauli.pauliX/Y/Z`
(both sides unfold to the same literal), so their properties reuse the canonical module's
proofs instead of re-deriving them from scratch. -/

section
open Spectra.QuantumMechanics.Pauli

lemma σₓ_hermitian : σₓ.IsHermitian := pauliX_hermitian

lemma σᵧ_hermitian : σᵧ.IsHermitian := pauliY_hermitian

lemma σZ_hermitian : σZ.IsHermitian := pauliZ_hermitian

lemma σₓ_sq : σₓ * σₓ = 1 := pauliX_sq

lemma σᵧ_sq : σᵧ * σᵧ = 1 := pauliY_sq

lemma σZ_sq : σZ * σZ = 1 := pauliZ_sq

/-- Pauli matrices anticommute: σₓσZ = -σZσₓ -/
lemma σₓ_σZ_anticomm : σₓ * σZ = -σZ * σₓ := by
  change pauliX * pauliZ = -pauliZ * pauliX
  linear_combination (norm := noncomm_ring) pauliXZ_anticommute

end

/-! ## The Bell State -/

/-- The singlet (Bell) state |Ψ⁻⟩ = (1/√2)(|01⟩ - |10⟩) as a density matrix.

A re-export of `Spectra.QuantumInfo.bellStatePsiMinus` (`BellsTheorem/Basic.lean`) under this
port chain's own name, rather than an independent re-derivation of the same object. -/
noncomputable def ρΨMinus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Spectra.QuantumInfo.bellStatePsiMinus

lemma ρΨMinus_trace : ρΨMinus.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, ρΨMinus, Spectra.QuantumInfo.bellStatePsiMinus,
    Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue]
  norm_num

end Spectra.QuantumCHSH

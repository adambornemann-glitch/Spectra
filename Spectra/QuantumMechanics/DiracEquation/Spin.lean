/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Spectra.QuantumMechanics.DiracEquation.GammaTrace
/-!
# Spin and Total Angular Momentum

This file introduces the spin operator of the Dirac theory and the algebraic facts behind
the conservation of total angular momentum.

For a spin-1/2 particle the spin is represented by the `4 × 4` matrices

  `Σⁱ = diag(σⁱ, σⁱ)`,

block-diagonal copies of the Pauli matrices acting on the two-component upper and lower
spinors simultaneously. The physical spin operator is `S = (ℏ/2) Σ`.

The central physical statement is that, although neither the orbital angular momentum `L`
nor the spin `S` is separately conserved by the Dirac Hamiltonian `H_D = c α·p + βmc²`, the
**total** angular momentum `J = L + (ℏ/2)Σ` *is* conserved: `[H_D, J] = 0`. The orbital part
of this fact involves the momentum operator and lives at the level of differential operators
(see `Operators.lean`); what can be stated purely algebraically — and is proved here — is the
commutator identity `[Σⁱ, αʲ] = 2i εⁱʲᵏ αᵏ`, which is exactly the term that cancels the
non-conservation of `L` against that of `S`.

## Main definitions

* `spinSigma1`, `spinSigma2`, `spinSigma3` — the spin matrices `Σ¹, Σ², Σ³`.
* `spinAt` — uniform access `spinAt i = Σⁱ⁺¹` indexed by `i : Fin 3`.

## Main statements

* `spinSigma{1,2,3}_hermitian` — each `Σⁱ` is Hermitian, hence an observable.
* `spinSigma{1,2,3}_isSelfAdjoint` — each `Σⁱ` is self-adjoint (`IsSelfAdjoint`), the same fact in
  Mathlib's operator-theoretic vocabulary.
* `spinSigma{1,2,3}_sq` — `(Σⁱ)² = I`: spin measurements yield `±1` (`±ℏ/2`).
* `spinSigma_su2_{12,23,31}` — `Σ¹Σ² = iΣ³` and cyclic: the `su(2)` spin algebra.
* `spinSigma_anticomm_{12,23,31}` — `{Σⁱ, Σʲ} = 0` for `i ≠ j`: distinct spin matrices anticommute.
* `spinSigma_comm_{12,23,31}` — `[Σⁱ, Σʲ] = 2i εⁱʲᵏ Σᵏ`.
* `spinSigma{1,2,3}_comm_beta` — `[Σⁱ, β] = 0`: spin commutes with the mass term.
* `diracAlpha_eq_gamma5_mul_spin{1,2,3}` — `αⁱ = γ⁵ Σⁱ`.
* `spin_alpha_comm_{12,23,31}` — `[Σⁱ, αʲ] = 2i εⁱʲᵏ αᵏ`, the spin–orbit identity behind
  conservation of total angular momentum.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1
* [Sakurai, *Advanced Quantum Mechanics*][sakurai1967], Chapter 3
* [Bjorken, Drell, *Relativistic Quantum Mechanics*][bjorkendrell1964], Chapter 4

## Tags

spin, angular momentum, Pauli matrices, su(2), spin-orbit coupling, Dirac equation
-/
open Complex Matrix
namespace Spectra.QuantumMechanics.Dirac

/-- Verify an entrywise matrix *commutator* identity. Like `dirac_compute`, but it also unfolds
    `Matrix.sub_apply` and reduces `I² = -1` after `ring_nf`, so commutators `A·B - B·A` with an
    imaginary right-hand side close. Pass the matrix definitions to unfold as simp lemmas. -/
macro "spin_compute" defs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic|
    (ext a b
     fin_cases a <;> fin_cases b <;>
       simp [$defs,*, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
             Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply,
             Fin.sum_univ_four, Complex.I_mul_I] <;>
     ring_nf <;> (try simp only [Complex.I_sq]) <;> ring))

/-! ## The spin matrices `Σⁱ = diag(σⁱ, σⁱ)` -/

/-- The spin matrix `Σ¹ = diag(σˣ, σˣ)` (block-diagonal Pauli-X). -/
def spinSigma1 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- The spin matrix `Σ² = diag(σʸ, σʸ)` (block-diagonal Pauli-Y; the only one with `±i`). -/
def spinSigma2 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, -I, 0, 0;
     I, 0, 0, 0;
     0, 0, 0, -I;
     0, 0, I, 0]

/-- The spin matrix `Σ³ = diag(σᶻ, σᶻ)` (block-diagonal Pauli-Z; diagonal). -/
def spinSigma3 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

/-- Uniform access to the spin matrices: `spinAt 0 = Σ¹`, `spinAt 1 = Σ²`, `spinAt 2 = Σ³`. -/
def spinAt (i : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  match i with
  | 0 => spinSigma1
  | 1 => spinSigma2
  | 2 => spinSigma3

/-! ## Hermiticity

Each `Σⁱ` is Hermitian, so spin along any axis is an observable. -/

/-- `Σ¹` is Hermitian: `(Σ¹)† = Σ¹`, so spin along `x` is an observable with real
    eigenvalues (`±ℏ/2`). -/
lemma spinSigma1_hermitian : spinSigma1.conjTranspose = spinSigma1 := by
  dirac_compute spinSigma1

/-- `Σ²` is Hermitian: `(Σ²)† = Σ²`; the `±i` entries sit in conjugate positions, so spin along
    `y` is an observable with real eigenvalues (`±ℏ/2`). -/
lemma spinSigma2_hermitian : spinSigma2.conjTranspose = spinSigma2 := by
  dirac_compute spinSigma2

/-- `Σ³` is Hermitian: `(Σ³)† = Σ³` (real diagonal), so spin along `z` is an observable with real
    eigenvalues (`±ℏ/2`). -/
lemma spinSigma3_hermitian : spinSigma3.conjTranspose = spinSigma3 := by
  dirac_compute spinSigma3

/-- `Σ¹` is self-adjoint as an operator, the physical-observable property in Mathlib's
    self-adjointness vocabulary. -/
lemma spinSigma1_isSelfAdjoint : IsSelfAdjoint spinSigma1 :=
  Matrix.IsHermitian.isSelfAdjoint spinSigma1_hermitian

/-- `Σ²` is self-adjoint as an operator. -/
lemma spinSigma2_isSelfAdjoint : IsSelfAdjoint spinSigma2 :=
  Matrix.IsHermitian.isSelfAdjoint spinSigma2_hermitian

/-- `Σ³` is self-adjoint as an operator. -/
lemma spinSigma3_isSelfAdjoint : IsSelfAdjoint spinSigma3 :=
  Matrix.IsHermitian.isSelfAdjoint spinSigma3_hermitian

/-! ## Spin one-half: `(Σⁱ)² = I`

Each spin matrix is an involution, so its eigenvalues are `±1`, i.e. the spin component
along any axis is `±ℏ/2`. -/

/-- `(Σ¹)² = I`: spin along `x` takes values `±ℏ/2`. -/
lemma spinSigma1_sq : spinSigma1 * spinSigma1 = 1 := by
  dirac_compute spinSigma1

/-- `(Σ²)² = I`: spin along `y` takes values `±ℏ/2`. -/
lemma spinSigma2_sq : spinSigma2 * spinSigma2 = 1 := by
  dirac_compute spinSigma2

/-- `(Σ³)² = I`: spin along `z` takes values `±ℏ/2`. -/
lemma spinSigma3_sq : spinSigma3 * spinSigma3 = 1 := by
  dirac_compute spinSigma3

/-! ## The `su(2)` spin algebra

The products `Σ¹Σ² = iΣ³` (and cyclic permutations) encode the angular-momentum algebra
`[Σⁱ, Σʲ] = 2i εⁱʲᵏ Σᵏ`. This is the statement that `S = (ℏ/2)Σ` has the angular-momentum
commutation relations `[Sⁱ, Sʲ] = iℏ εⁱʲᵏ Sᵏ`. -/

/-- `Σ¹Σ² = iΣ³`: the product form of the spin algebra. -/
lemma spinSigma_su2_12 : spinSigma1 * spinSigma2 = I • spinSigma3 := by
  dirac_compute spinSigma1, spinSigma2, spinSigma3

/-- `Σ²Σ³ = iΣ¹` (cyclic). -/
lemma spinSigma_su2_23 : spinSigma2 * spinSigma3 = I • spinSigma1 := by
  dirac_compute spinSigma2, spinSigma3, spinSigma1

/-- `Σ³Σ¹ = iΣ²` (cyclic). -/
lemma spinSigma_su2_31 : spinSigma3 * spinSigma1 = I • spinSigma2 := by
  dirac_compute spinSigma3, spinSigma1, spinSigma2

/-- Distinct spin matrices anticommute: `{Σ¹, Σ²} = 0`. -/
lemma spinSigma_anticomm_12 : spinSigma1 * spinSigma2 + spinSigma2 * spinSigma1 = 0 := by
  dirac_compute spinSigma1, spinSigma2

/-- Distinct spin matrices anticommute: `{Σ², Σ³} = 0`. -/
lemma spinSigma_anticomm_23 : spinSigma2 * spinSigma3 + spinSigma3 * spinSigma2 = 0 := by
  dirac_compute spinSigma2, spinSigma3

/-- Distinct spin matrices anticommute: `{Σ³, Σ¹} = 0`. -/
lemma spinSigma_anticomm_31 : spinSigma3 * spinSigma1 + spinSigma1 * spinSigma3 = 0 := by
  dirac_compute spinSigma3, spinSigma1

/-- The spin commutator `[Σ¹, Σ²] = 2i Σ³`. -/
lemma spinSigma_comm_12 :
    spinSigma1 * spinSigma2 - spinSigma2 * spinSigma1 = (2 * I) • spinSigma3 := by
  spin_compute spinSigma1, spinSigma2, spinSigma3

/-- The spin commutator `[Σ², Σ³] = 2i Σ¹`. -/
lemma spinSigma_comm_23 :
    spinSigma2 * spinSigma3 - spinSigma3 * spinSigma2 = (2 * I) • spinSigma1 := by
  spin_compute spinSigma1, spinSigma2, spinSigma3

/-- The spin commutator `[Σ³, Σ¹] = 2i Σ²`. -/
lemma spinSigma_comm_31 :
    spinSigma3 * spinSigma1 - spinSigma1 * spinSigma3 = (2 * I) • spinSigma2 := by
  spin_compute spinSigma1, spinSigma2, spinSigma3

/-! ## Spin commutes with the mass term

`[Σⁱ, β] = 0`: the spin matrices commute with `β = γ⁰`, so the mass term `βmc²` of the
Dirac Hamiltonian does not rotate spin. -/

/-- `[Σ¹, β] = 0`: spin along `x` commutes with the mass term. -/
lemma spinSigma1_comm_beta : spinSigma1 * diracBeta = diracBeta * spinSigma1 := by
  dirac_compute spinSigma1, diracBeta

/-- `[Σ², β] = 0`: spin along `y` commutes with the mass term. -/
lemma spinSigma2_comm_beta : spinSigma2 * diracBeta = diracBeta * spinSigma2 := by
  dirac_compute spinSigma2, diracBeta

/-- `[Σ³, β] = 0`: spin along `z` commutes with the mass term. -/
lemma spinSigma3_comm_beta : spinSigma3 * diracBeta = diracBeta * spinSigma3 := by
  dirac_compute spinSigma3, diracBeta

/-! ## Relation to the `α` matrices: `αⁱ = γ⁵ Σⁱ`

The velocity matrices `αⁱ` factor through the chirality matrix and the spin matrices. -/

/-- `α¹ = γ⁵ Σ¹`. -/
lemma diracAlpha_eq_gamma5_mul_spin1 : diracAlpha1 = gamma5 * spinSigma1 := by
  dirac_compute diracAlpha1, gamma5, spinSigma1

/-- `α² = γ⁵ Σ²`. -/
lemma diracAlpha_eq_gamma5_mul_spin2 : diracAlpha2 = gamma5 * spinSigma2 := by
  dirac_compute diracAlpha2, gamma5, spinSigma2

/-- `α³ = γ⁵ Σ³`. -/
lemma diracAlpha_eq_gamma5_mul_spin3 : diracAlpha3 = gamma5 * spinSigma3 := by
  dirac_compute diracAlpha3, gamma5, spinSigma3

/-! ## Spin–orbit coupling: `[Σⁱ, αʲ] = 2i εⁱʲᵏ αᵏ`

This is the algebraic heart of total-angular-momentum conservation. The orbital angular
momentum obeys `[Lⁱ, H_D] = iℏ εⁱʲᵏ c αʲ pᵏ ≠ 0`, and the spin obeys
`[(ℏ/2)Σⁱ, H_D] = -iℏ εⁱʲᵏ c αʲ pᵏ`; the two cancel precisely because of the commutators
below, leaving `[Jⁱ, H_D] = 0` for `J = L + (ℏ/2)Σ`. -/

/-- `[Σ¹, α²] = 2i α³`. -/
lemma spin_alpha_comm_12 :
    spinSigma1 * diracAlpha2 - diracAlpha2 * spinSigma1 = (2 * I) • diracAlpha3 := by
  spin_compute spinSigma1, diracAlpha2, diracAlpha3

/-- `[Σ², α³] = 2i α¹`. -/
lemma spin_alpha_comm_23 :
    spinSigma2 * diracAlpha3 - diracAlpha3 * spinSigma2 = (2 * I) • diracAlpha1 := by
  spin_compute spinSigma2, diracAlpha3, diracAlpha1

/-- `[Σ³, α¹] = 2i α²`. -/
lemma spin_alpha_comm_31 :
    spinSigma3 * diracAlpha1 - diracAlpha1 * spinSigma3 = (2 * I) • diracAlpha2 := by
  spin_compute spinSigma3, diracAlpha1, diracAlpha2

end Spectra.QuantumMechanics.Dirac

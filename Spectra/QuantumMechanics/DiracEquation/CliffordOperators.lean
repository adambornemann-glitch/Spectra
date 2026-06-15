/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.SpinorSpaceL2
/-!
# The Dirac matrices as bounded operators on `L²(ℝ³; ℂ⁴)`

The constant matrices `α¹, α², α³, β` act on the spinor Hilbert space `L²(ℝ³; ℂ⁴)` by the
bounded representation `matrixOp` from `SpinorSpaceL2.lean`. This file packages those four
operators — the *velocity operators* `αⁱ` and the *mass-direction operator* `β` — and lifts the
Clifford algebra from the matrix level to the operator level:

* each is bounded and self-adjoint (an observable);
* each squares to the identity;
* distinct `αⁱ` anticommute, and each `αⁱ` anticommutes with `β`.

These are the bounded building blocks of the Dirac Hamiltonian `H_D = c α·p + βmc²`: `β` and the
`αⁱ` are bounded, while the momentum `p = -i∇` is the unbounded part (treated separately). Because
`matrixOp` is a unital `*`-algebra representation, every relation here is an immediate consequence
of the corresponding matrix identity in `CliffordAlgebra.lean`.

NB: this packaging is currently standalone — `FreeHamiltonian.lean` builds `H_D` directly from
`matrixOp` and the raw matrices, so the named operators below have no downstream consumer yet.

## Main definitions

* `diracAlphaOp1`, `diracAlphaOp2`, `diracAlphaOp3` — the velocity operators `αⁱ` on `L²(ℝ³;ℂ⁴)`.
* `diracBetaOp` — the mass-direction operator `β` on `L²(ℝ³;ℂ⁴)`.

## Main statements

* `diracAlphaOp{1,2,3}_isSelfAdjoint`, `diracBetaOp_isSelfAdjoint` — all four are self-adjoint.
* `diracAlphaOp{1,2,3}_sq`, `diracBetaOp_sq` — each squares to the identity.
* `diracAlphaOp{12,13,23}_anticomm` — distinct velocity operators anticommute.
* `diracAlphaOp{1,2,3}_betaOp_anticomm` — each velocity operator anticommutes with `β`.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1
* [Reed, Simon, *Methods of Modern Mathematical Physics*][reed1975], Vol. II, §X.4

## Tags

Dirac equation, velocity operator, Clifford algebra, self-adjoint operator, bounded operator
-/
namespace Spectra.QuantumMechanics.Dirac

/-! ## The four bounded Dirac operators -/

/-- The velocity operator `α¹` acting on `L²(ℝ³; ℂ⁴)`. -/
noncomputable def diracAlphaOp1 : DiracSpinorL2 →L[ℂ] DiracSpinorL2 := matrixOp diracAlpha1

/-- The velocity operator `α²` acting on `L²(ℝ³; ℂ⁴)`. -/
noncomputable def diracAlphaOp2 : DiracSpinorL2 →L[ℂ] DiracSpinorL2 := matrixOp diracAlpha2

/-- The velocity operator `α³` acting on `L²(ℝ³; ℂ⁴)`. -/
noncomputable def diracAlphaOp3 : DiracSpinorL2 →L[ℂ] DiracSpinorL2 := matrixOp diracAlpha3

/-- The mass-direction operator `β` acting on `L²(ℝ³; ℂ⁴)`. -/
noncomputable def diracBetaOp : DiracSpinorL2 →L[ℂ] DiracSpinorL2 := matrixOp diracBeta

/-! ## Self-adjointness

Each Dirac operator is self-adjoint, hence a genuine observable on the spinor Hilbert space. -/

/-- `α¹` is self-adjoint. -/
lemma diracAlphaOp1_isSelfAdjoint : IsSelfAdjoint diracAlphaOp1 :=
  matrixOp_isSelfAdjoint_of_hermitian diracAlpha1_hermitian

/-- `α²` is self-adjoint. -/
lemma diracAlphaOp2_isSelfAdjoint : IsSelfAdjoint diracAlphaOp2 :=
  matrixOp_isSelfAdjoint_of_hermitian diracAlpha2_hermitian

/-- `α³` is self-adjoint. -/
lemma diracAlphaOp3_isSelfAdjoint : IsSelfAdjoint diracAlphaOp3 :=
  matrixOp_isSelfAdjoint_of_hermitian diracAlpha3_hermitian

/-- `β` is self-adjoint. -/
lemma diracBetaOp_isSelfAdjoint : IsSelfAdjoint diracBetaOp :=
  matrixOp_isSelfAdjoint_of_hermitian diracBeta_hermitian

/-! ## The operator Clifford algebra

Squares and anticommutators, lifted from `CliffordAlgebra.lean` through the representation
`matrixOp` (`matrixOp_mul`, `matrixOp_add`, `matrixOp_one`, `matrixOp_zero`). -/

/-- `(α¹)² = I` as an operator. -/
lemma diracAlphaOp1_sq : diracAlphaOp1.comp diracAlphaOp1 = ContinuousLinearMap.id ℂ DiracSpinorL2 := by
  unfold diracAlphaOp1
  rw [← matrixOp_mul, diracAlpha1_sq, matrixOp_one]

/-- `(α²)² = I` as an operator. -/
lemma diracAlphaOp2_sq : diracAlphaOp2.comp diracAlphaOp2 = ContinuousLinearMap.id ℂ DiracSpinorL2 := by
  unfold diracAlphaOp2
  rw [← matrixOp_mul, diracAlpha2_sq, matrixOp_one]

/-- `(α³)² = I` as an operator. -/
lemma diracAlphaOp3_sq : diracAlphaOp3.comp diracAlphaOp3 = ContinuousLinearMap.id ℂ DiracSpinorL2 := by
  unfold diracAlphaOp3
  rw [← matrixOp_mul, diracAlpha3_sq, matrixOp_one]

/-- `β² = I` as an operator. -/
lemma diracBetaOp_sq : diracBetaOp.comp diracBetaOp = ContinuousLinearMap.id ℂ DiracSpinorL2 := by
  unfold diracBetaOp
  rw [← matrixOp_mul, diracBeta_sq, matrixOp_one]

/-- `{α¹, α²} = 0` as operators. -/
lemma diracAlphaOp12_anticomm :
    diracAlphaOp1.comp diracAlphaOp2 + diracAlphaOp2.comp diracAlphaOp1 = 0 := by
  unfold diracAlphaOp1 diracAlphaOp2
  rw [← matrixOp_mul, ← matrixOp_mul, ← matrixOp_add, diracAlpha12_anticommute, matrixOp_zero]

/-- `{α¹, α³} = 0` as operators. -/
lemma diracAlphaOp13_anticomm :
    diracAlphaOp1.comp diracAlphaOp3 + diracAlphaOp3.comp diracAlphaOp1 = 0 := by
  unfold diracAlphaOp1 diracAlphaOp3
  rw [← matrixOp_mul, ← matrixOp_mul, ← matrixOp_add, diracAlpha13_anticommute, matrixOp_zero]

/-- `{α², α³} = 0` as operators. -/
lemma diracAlphaOp23_anticomm :
    diracAlphaOp2.comp diracAlphaOp3 + diracAlphaOp3.comp diracAlphaOp2 = 0 := by
  unfold diracAlphaOp2 diracAlphaOp3
  rw [← matrixOp_mul, ← matrixOp_mul, ← matrixOp_add, diracAlpha23_anticommute, matrixOp_zero]

/-- `{α¹, β} = 0` as operators: the momentum and mass terms anticommute. -/
lemma diracAlphaOp1_betaOp_anticomm :
    diracAlphaOp1.comp diracBetaOp + diracBetaOp.comp diracAlphaOp1 = 0 := by
  unfold diracAlphaOp1 diracBetaOp
  rw [← matrixOp_mul, ← matrixOp_mul, ← matrixOp_add, diracAlpha1_beta_anticommute, matrixOp_zero]

/-- `{α², β} = 0` as operators. -/
lemma diracAlphaOp2_betaOp_anticomm :
    diracAlphaOp2.comp diracBetaOp + diracBetaOp.comp diracAlphaOp2 = 0 := by
  unfold diracAlphaOp2 diracBetaOp
  rw [← matrixOp_mul, ← matrixOp_mul, ← matrixOp_add, diracAlpha2_beta_anticommute, matrixOp_zero]

/-- `{α³, β} = 0` as operators. -/
lemma diracAlphaOp3_betaOp_anticomm :
    diracAlphaOp3.comp diracBetaOp + diracBetaOp.comp diracAlphaOp3 = 0 := by
  unfold diracAlphaOp3 diracBetaOp
  rw [← matrixOp_mul, ← matrixOp_mul, ← matrixOp_add, diracAlpha3_beta_anticommute, matrixOp_zero]

end Spectra.QuantumMechanics.Dirac

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.SpinorSpaceL2
/-!
# The Dirac matrices as bounded operators on `L²(ℝ³; ℂ⁴)`

The constant matrices `α¹, α², α³, β` act on the spinor Hilbert space `L²(ℝ³; ℂ⁴)`
by the bounded representation `matrixOp` from `SpinorSpaceL2.lean`. This file packages
those four operators — the *velocity operators* `αⁱ` and the *mass-direction operator*
`β` — and lifts the Clifford algebra from the matrix level to the operator level:

* each is bounded and self-adjoint (an observable);
* each squares to the identity;
* distinct `αⁱ` anticommute, and each `αⁱ` anticommutes with `β`.

These are the bounded building blocks of the Dirac Hamiltonian `H_D = c α·p + βmc²`:
`β` and the `αⁱ` are bounded, while the momentum `p = -i∇` is the unbounded part
(treated separately). Because `matrixOp` is a unital `*`-algebra representation, every
relation here is an immediate consequence of the corresponding matrix identity in
`CliffordAlgebra.lean`.

## Implementation notes

Each operator relation is lifted from its matrix counterpart through the private helpers
`matrixOp_sq_eq_one_of` and `matrixOp_anticomm_of`, which turn a matrix identity
(`M * M = 1` or `M * N + N * M = 0`) into the corresponding operator identity via the
representation lemmas `matrixOp_mul`, `matrixOp_add`, `matrixOp_one`, `matrixOp_zero`.

The squares, anticommutators, and self-adjointness lemmas are tagged `@[simp]` so the
simplifier can discharge the Clifford relations automatically — e.g. when reducing
`H_D²` — mirroring `matrixOp_one`/`matrixOp_zero` in `SpinorSpaceL2.lean`.

NB: `FreeHamiltonian.lean` currently assembles `H_D` at the matrix-entry / `matrixOp M`
level — the kinetic term `α·p` is *unbounded*, so it is built from `weakGradient` and the
matrix entries `αᵏ_{ab}` (and the mass term as `matrixOp (mc² β)`), not from these bounded
operators. The four operators here are the operator-level Clifford algebra: the natural
building blocks for future operator-level statements — the operator dispersion
`(α·p)² = |p|²`, or a Foldy–Wouthuysen / spectral-equivalence transform diagonalizing `H_D` —
that would relate `H_D` to a block-diagonal form. Kept as the operator-algebra API for that
relativistic-QM development rather than folded into the current entry-level assembly.

## Main definitions

* `diracAlphaOp1`, `diracAlphaOp2`, `diracAlphaOp3` — the velocity operators `αⁱ`
  on `L²(ℝ³;ℂ⁴)`.
* `diracBetaOp` — the mass-direction operator `β` on `L²(ℝ³;ℂ⁴)`.

## Main statements

* `diracAlphaOp{1,2,3}_isSelfAdjoint`, `diracBetaOp_isSelfAdjoint` — all four are
  self-adjoint.
* `diracAlphaOp{1,2,3}_sq`, `diracBetaOp_sq` — each squares to the identity.
* `diracAlphaOp{12,13,23}_anticomm` — distinct velocity operators anticommute.
* `diracAlphaOp{1,2,3}_betaOp_anticomm` — each velocity operator anticommutes with `β`.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1
* [Bjorken, Drell, *Relativistic Quantum Mechanics*][bjorken1964], Chapter 1
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
@[simp] lemma diracAlphaOp1_isSelfAdjoint : IsSelfAdjoint diracAlphaOp1 :=
  matrixOp_isSelfAdjoint_of_hermitian diracAlpha1_hermitian

/-- `α²` is self-adjoint. -/
@[simp] lemma diracAlphaOp2_isSelfAdjoint : IsSelfAdjoint diracAlphaOp2 :=
  matrixOp_isSelfAdjoint_of_hermitian diracAlpha2_hermitian

/-- `α³` is self-adjoint. -/
@[simp] lemma diracAlphaOp3_isSelfAdjoint : IsSelfAdjoint diracAlphaOp3 :=
  matrixOp_isSelfAdjoint_of_hermitian diracAlpha3_hermitian

/-- `β` is self-adjoint. -/
@[simp] lemma diracBetaOp_isSelfAdjoint : IsSelfAdjoint diracBetaOp :=
  matrixOp_isSelfAdjoint_of_hermitian diracBeta_hermitian

/-! ## The operator Clifford algebra

Squares and anticommutators, lifted from `CliffordAlgebra.lean` through the representation
`matrixOp` (`matrixOp_mul`, `matrixOp_add`, `matrixOp_one`, `matrixOp_zero`). The two private
helpers below carry the single repeated proof pattern. -/

/-- Lift a matrix square-to-one identity `M * M = 1` to the operator level:
`(matrixOp M) ∘L (matrixOp M) = id`. -/
private lemma matrixOp_sq_eq_one_of {M : Matrix (Fin 4) (Fin 4) ℂ} (hM : M * M = 1) :
    (matrixOp M).comp (matrixOp M) = ContinuousLinearMap.id ℂ DiracSpinorL2 := by
  rw [← matrixOp_mul, hM, matrixOp_one]

/-- Lift a matrix anticommutation identity `M * N + N * M = 0` to the operator level:
`(matrixOp M) ∘L (matrixOp N) + (matrixOp N) ∘L (matrixOp M) = 0`. -/
private lemma matrixOp_anticomm_of {M N : Matrix (Fin 4) (Fin 4) ℂ}
    (hMN : M * N + N * M = 0) :
    (matrixOp M).comp (matrixOp N) + (matrixOp N).comp (matrixOp M) = 0 := by
  rw [← matrixOp_mul, ← matrixOp_mul, ← matrixOp_add, hMN, matrixOp_zero]

/-- `(α¹)² = I` as an operator. -/
@[simp] lemma diracAlphaOp1_sq :
    diracAlphaOp1.comp diracAlphaOp1 = ContinuousLinearMap.id ℂ DiracSpinorL2 :=
  matrixOp_sq_eq_one_of diracAlpha1_sq

/-- `(α²)² = I` as an operator. -/
@[simp] lemma diracAlphaOp2_sq :
    diracAlphaOp2.comp diracAlphaOp2 = ContinuousLinearMap.id ℂ DiracSpinorL2 :=
  matrixOp_sq_eq_one_of diracAlpha2_sq

/-- `(α³)² = I` as an operator. -/
@[simp] lemma diracAlphaOp3_sq :
    diracAlphaOp3.comp diracAlphaOp3 = ContinuousLinearMap.id ℂ DiracSpinorL2 :=
  matrixOp_sq_eq_one_of diracAlpha3_sq

/-- `β² = I` as an operator. -/
@[simp] lemma diracBetaOp_sq :
    diracBetaOp.comp diracBetaOp = ContinuousLinearMap.id ℂ DiracSpinorL2 :=
  matrixOp_sq_eq_one_of diracBeta_sq

/-- `{α¹, α²} = 0` as operators. -/
@[simp] lemma diracAlphaOp12_anticomm :
    diracAlphaOp1.comp diracAlphaOp2 + diracAlphaOp2.comp diracAlphaOp1 = 0 :=
  matrixOp_anticomm_of diracAlpha12_anticommute

/-- `{α¹, α³} = 0` as operators. -/
@[simp] lemma diracAlphaOp13_anticomm :
    diracAlphaOp1.comp diracAlphaOp3 + diracAlphaOp3.comp diracAlphaOp1 = 0 :=
  matrixOp_anticomm_of diracAlpha13_anticommute

/-- `{α², α³} = 0` as operators. -/
@[simp] lemma diracAlphaOp23_anticomm :
    diracAlphaOp2.comp diracAlphaOp3 + diracAlphaOp3.comp diracAlphaOp2 = 0 :=
  matrixOp_anticomm_of diracAlpha23_anticommute

/-- `{α¹, β} = 0` as operators: the momentum and mass terms anticommute. -/
@[simp] lemma diracAlphaOp1_betaOp_anticomm :
    diracAlphaOp1.comp diracBetaOp + diracBetaOp.comp diracAlphaOp1 = 0 :=
  matrixOp_anticomm_of diracAlpha1_beta_anticommute

/-- `{α², β} = 0` as operators. -/
@[simp] lemma diracAlphaOp2_betaOp_anticomm :
    diracAlphaOp2.comp diracBetaOp + diracBetaOp.comp diracAlphaOp2 = 0 :=
  matrixOp_anticomm_of diracAlpha2_beta_anticommute

/-- `{α³, β} = 0` as operators. -/
@[simp] lemma diracAlphaOp3_betaOp_anticomm :
    diracAlphaOp3.comp diracBetaOp + diracBetaOp.comp diracAlphaOp3 = 0 :=
  matrixOp_anticomm_of diracAlpha3_beta_anticommute

end Spectra.QuantumMechanics.Dirac

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.CliffordAlgebra
/-!
# The Relativistic Dispersion Relation

The whole point of the Clifford-algebra relations `αᵢ² = β² = I`, `{αᵢ, αⱼ} = 0`, and
`{αᵢ, β} = 0` is that they force the square of the Dirac Hamiltonian to reproduce the
relativistic energy–momentum relation. Writing the momentum-space symbol of
`H_D = c α·p + βmc²` (in units `ℏ = c = 1`) as the matrix

  `D(p, m) = p₁α₁ + p₂α₂ + p₃α₃ + mβ`,

this file proves

  `D(p, m)² = (|p|² + m²) · I`,

which is exactly `E² = |p|²c² + m²c⁴`. Every cross term `pᵢpⱼ{αᵢ, αⱼ}` and `pᵢm{αᵢ, β}`
cancels by anticommutation, and each square `αᵢ², β²` contributes its `I`; this is the
algebraic reason a spin-1/2 relativistic particle has the spectrum
`σ(H_D) = (-∞, -mc²] ∪ [mc², ∞)` with the mass gap `2mc²`.

## Main definitions

* `diracMomentumOp` — the momentum-space symbol `D(p, m) = α·p + βm`.
* `energyMomentumSq` — the scalar `|p|² + m²`.

## Main statements

* `diracMomentumOp_sq` — `D(p, m)² = (|p|² + m²) I`, the relativistic dispersion relation.
* `diracMomentumOp_hermitian` — `D(p, m)` is Hermitian for real `p, m`, so it is an observable.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1
* [Bjorken, Drell, *Relativistic Quantum Mechanics*][bjorkendrell1964], Chapter 1

## Tags

dispersion relation, mass shell, Clifford algebra, Dirac operator, energy-momentum relation
-/
open Complex Matrix
namespace Spectra.QuantumMechanics.Dirac

/-- Verify an entrywise identity for the Dirac symbol, whose entries are `ℝ`-linear
    combinations (via `Complex.ofReal`) of the momentum components and the mass. Like
    `dirac_compute`, but reduces `I² = -1` after `ring_nf` and closes with `ring`, so the
    squared-operator identity with real-coerced coefficients goes through. -/
macro "disp_compute" : tactic =>
  `(tactic|
    (ext a b
     fin_cases a <;> fin_cases b <;>
       simp [diracAlpha1, diracAlpha2, diracAlpha3, diracBeta, Matrix.mul_apply, Matrix.add_apply,
             Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, Matrix.neg_apply,
             Fin.sum_univ_four, Complex.I_mul_I] <;>
     ring_nf <;> (try simp only [Complex.I_sq]) <;> ring))

/-- The relativistic energy squared `|p|² + m²` (natural units `ℏ = c = 1`). -/
def energyMomentumSq (p : Fin 3 → ℝ) (m : ℝ) : ℝ :=
  p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + m ^ 2

/-- The momentum-space symbol of the Dirac Hamiltonian,
`D(p, m) = p₁α₁ + p₂α₂ + p₃α₃ + mβ`. -/
noncomputable def diracMomentumOp (p : Fin 3 → ℝ) (m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (p 0 : ℂ) • diracAlpha1 + (p 1 : ℂ) • diracAlpha2 + (p 2 : ℂ) • diracAlpha3 + (m : ℂ) • diracBeta

/-- **The relativistic dispersion relation**: `D(p, m)² = (|p|² + m²) I`.

The cross terms vanish by the Clifford anticommutation relations and the diagonal squares
each contribute the identity, so squaring the Dirac symbol returns the scalar `|p|² + m²`
times the identity — the matrix content of `E² = |p|²c² + m²c⁴`. -/
theorem diracMomentumOp_sq (p : Fin 3 → ℝ) (m : ℝ) :
    diracMomentumOp p m * diracMomentumOp p m = ((energyMomentumSq p m : ℝ) : ℂ) • 1 := by
  unfold diracMomentumOp energyMomentumSq
  disp_compute

/-- The Dirac symbol is Hermitian for real `p, m`: `D(p, m)† = D(p, m)`.

This makes `D` (hence the Dirac Hamiltonian) an observable; combined with
`diracMomentumOp_sq` it shows the eigenvalues are real and come in pairs `±√(|p|² + m²)`. -/
theorem diracMomentumOp_hermitian (p : Fin 3 → ℝ) (m : ℝ) :
    (diracMomentumOp p m).conjTranspose = diracMomentumOp p m := by
  unfold diracMomentumOp
  simp only [conjTranspose_add, conjTranspose_smul, diracAlpha1_hermitian, diracAlpha2_hermitian,
    diracAlpha3_hermitian, diracBeta_hermitian, RCLike.star_def, Complex.conj_ofReal]

end Spectra.QuantumMechanics.Dirac

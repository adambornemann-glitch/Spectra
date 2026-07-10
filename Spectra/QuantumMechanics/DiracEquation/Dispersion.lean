/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
* `energyMomentum` — the on-shell energy `E(p, m) = √(|p|² + m²)`.

## Main statements

* `diracMomentumOp_sq` — `D(p, m)² = (|p|² + m²) I`, the relativistic dispersion relation.
* `diracMomentumOp_hermitian` — `D(p, m)` is Hermitian for real `p, m`, so it is an observable.
* `energyMomentumSq_nonneg`, `energyMomentum_nonneg` — the scalar `|p|² + m²` and its root are
  nonnegative.
* `diracMomentumOp_factor` — the mass-shell factorisation `(D + E)(D − E) = 0`, exhibiting the
  eigenvalues `±E` that seed the negative-energy branch.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1
* [Bjorken, Drell, *Relativistic Quantum Mechanics*][bjorkendrell1964], Chapter 1
* [Peskin, Schroeder, *An Introduction to Quantum Field Theory*][peskin1995], Section 3.3

## Tags

dispersion relation, mass shell, Clifford algebra, Dirac operator, energy-momentum relation
-/
open Complex Matrix
namespace Spectra.QuantumMechanics.Dirac

/-- Verify an entrywise identity for the Dirac symbol, whose entries are `ℝ`-linear
    combinations (via `Complex.ofReal`) of the momentum components and the mass. Like
    `dirac_compute`, but reduces `I² = -1` after `ring_nf` and closes with `ring`, so the
    squared-operator identity with real-coerced coefficients goes through. -/
macro "dispCompute" : tactic =>
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
  (p 0 : ℂ) • diracAlpha1 + (p 1 : ℂ) • diracAlpha2 + (p 2 : ℂ) • diracAlpha3 +
    (m : ℂ) • diracBeta

/-- **The relativistic dispersion relation**: `D(p, m)² = (|p|² + m²) I`.

The cross terms vanish by the Clifford anticommutation relations and the diagonal squares
each contribute the identity, so squaring the Dirac symbol returns the scalar `|p|² + m²`
times the identity — the matrix content of `E² = |p|²c² + m²c⁴`. -/
theorem diracMomentumOp_sq (p : Fin 3 → ℝ) (m : ℝ) :
    diracMomentumOp p m * diracMomentumOp p m = ((energyMomentumSq p m : ℝ) : ℂ) • 1 := by
  unfold diracMomentumOp energyMomentumSq
  dispCompute

/-- The Dirac symbol is Hermitian for real `p, m`: `D(p, m)† = D(p, m)`.

This makes `D` (hence the Dirac Hamiltonian) an observable; combined with
`diracMomentumOp_sq` it shows the eigenvalues are real and come in pairs `±√(|p|² + m²)`. -/
theorem diracMomentumOp_hermitian (p : Fin 3 → ℝ) (m : ℝ) :
    (diracMomentumOp p m).conjTranspose = diracMomentumOp p m := by
  unfold diracMomentumOp
  simp only [conjTranspose_add, conjTranspose_smul, diracAlpha1_hermitian, diracAlpha2_hermitian,
    diracAlpha3_hermitian, diracBeta_hermitian, RCLike.star_def, Complex.conj_ofReal]

/-! ## The mass shell and its eigenprojection seed

`diracMomentumOp_sq` says `D(p,m)² = (|p|² + m²)·I`.  Writing `E(p,m) = √(|p|² + m²)` for the
positive root, this means `D` satisfies its characteristic equation `(D + E)(D − E) = 0`, so its
eigenvalues are exactly `±E`.  These are the seeds of the Step-(b) negative-energy wavepacket: the
negative-energy fibre is `ran(D − E·I)`, on which `D` acts as `−E`. -/

/-- The on-shell relativistic energy `E(p, m) = √(|p|² + m²)` (natural units `ℏ = c = 1`). -/
noncomputable def energyMomentum (p : Fin 3 → ℝ) (m : ℝ) : ℝ :=
  Real.sqrt (energyMomentumSq p m)

/-- The energy squared `|p|² + m²` is nonnegative, so it has a real square root. -/
theorem energyMomentumSq_nonneg (p : Fin 3 → ℝ) (m : ℝ) : 0 ≤ energyMomentumSq p m := by
  unfold energyMomentumSq; positivity

/-- The on-shell energy squares back to `|p|² + m²`: `E(p, m)² = |p|² + m²`. -/
@[simp] theorem energyMomentum_sq (p : Fin 3 → ℝ) (m : ℝ) :
    energyMomentum p m ^ 2 = energyMomentumSq p m :=
  Real.sq_sqrt (energyMomentumSq_nonneg p m)

/-- The on-shell energy `E(p, m) = √(|p|² + m²)` is nonnegative — the positive mass-shell root. -/
theorem energyMomentum_nonneg (p : Fin 3 → ℝ) (m : ℝ) : 0 ≤ energyMomentum p m :=
  Real.sqrt_nonneg _

/-- **Mass-shell factorisation**: `(D(p,m) + E)·(D(p,m) − E) = 0`, with `E = √(|p|² + m²)`.

Immediate from `D² = E²·I`: the Dirac symbol satisfies its own characteristic polynomial, so it
has no eigenvalues beyond `±E`.  In particular every vector of the form `w = (D − E·I)u` is a
negative-energy eigenvector, `D w = −E w` — the algebraic origin of the antiparticle branch
`(-∞, -mc²]` of the spectrum. -/
theorem diracMomentumOp_factor (p : Fin 3 → ℝ) (m : ℝ) :
    (diracMomentumOp p m + (energyMomentum p m : ℂ) • 1)
      * (diracMomentumOp p m - (energyMomentum p m : ℂ) • 1) = 0 := by
  have hcc : (energyMomentum p m : ℂ) * (energyMomentum p m : ℂ)
      = ((energyMomentumSq p m : ℝ) : ℂ) := by
    rw [← energyMomentum_sq p m]; push_cast; ring
  simp only [add_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul,
    smul_smul, diracMomentumOp_sq, hcc]
  abel

end Spectra.QuantumMechanics.Dirac

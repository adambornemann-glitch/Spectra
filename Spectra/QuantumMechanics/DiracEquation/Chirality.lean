/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.GammaTrace
/-!
# Chirality Projectors

The chirality matrix `γ⁵` introduced in `GammaTrace.lean` is a Hermitian involution, so it
splits spinor space into its `±1` eigenspaces. The associated orthogonal projectors

  `P_L = (1 - γ⁵)/2`,    `P_R = (1 + γ⁵)/2`

project onto the left-handed and right-handed components of a Dirac spinor. This file proves
that `P_L` and `P_R` are a complete pair of orthogonal Hermitian projectors, and records how
`γ⁵` acts on each summand.

## Physical interpretation

Chirality is the Lorentz-invariant handedness of a fermion. The Standard Model weak
interaction couples **only** to the left-handed projection `P_L ψ`, which is the origin of
parity violation. For a massless particle chirality coincides with helicity (spin along
momentum); the mass term `βmc²` mixes the two chiralities, which is why a Dirac mass requires
both `P_L ψ` and `P_R ψ`.

## Main definitions

* `chiralLeft` — the left-handed projector `P_L = (1 - γ⁵)/2`.
* `chiralRight` — the right-handed projector `P_R = (1 + γ⁵)/2`.

## Main statements

* `chiral_add` — completeness `P_L + P_R = 1`.
* `chiralLeft_idem`, `chiralRight_idem` — idempotency `P² = P`.
* `chiral_ortho_lr`, `chiral_ortho_rl` — orthogonality `P_L P_R = P_R P_L = 0`.
* `chiralLeft_hermitian`, `chiralRight_hermitian` — each projector is Hermitian.
* `gamma5_chiralRight`, `gamma5_chiralLeft` — `γ⁵ P_R = P_R`, `γ⁵ P_L = -P_L`.

## References

* [Peskin, Schroeder, *An Introduction to Quantum Field Theory*][peskin1995], Section 3.2
* [Srednicki, *Quantum Field Theory*][srednicki2007], Chapter 36

## Tags

chirality, projectors, gamma5, left-handed, right-handed, parity violation
-/
namespace Spectra.QuantumMechanics.Dirac

/-! ## The chirality projectors -/

/-- The left-handed chirality projector `P_L = (1 - γ⁵)/2`. -/
noncomputable def chiralLeft : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • (1 - gamma5)

/-- The right-handed chirality projector `P_R = (1 + γ⁵)/2`. -/
noncomputable def chiralRight : Matrix (Fin 4) (Fin 4) ℂ :=
  (2⁻¹ : ℂ) • (1 + gamma5)

/-! ## Completeness and idempotency -/

/-- Completeness: `P_L + P_R = I`. Every spinor splits as `ψ = P_L ψ + P_R ψ`. -/
lemma chiral_add : chiralLeft + chiralRight = 1 := by
  dirac_compute chiralLeft, chiralRight, gamma5

/-- `P_L` is idempotent: `P_L² = P_L`, the defining property of a projector. -/
lemma chiralLeft_idem : chiralLeft * chiralLeft = chiralLeft := by
  dirac_compute chiralLeft, gamma5

/-- `P_R` is idempotent: `P_R² = P_R`. -/
lemma chiralRight_idem : chiralRight * chiralRight = chiralRight := by
  dirac_compute chiralRight, gamma5

/-! ## Hermiticity -/

/-- `P_L` is Hermitian, hence an orthogonal projector (chirality is an observable). -/
lemma chiralLeft_hermitian : chiralLeft.conjTranspose = chiralLeft := by
  dirac_compute chiralLeft, gamma5

/-- `P_R` is Hermitian, hence an orthogonal projector. -/
lemma chiralRight_hermitian : chiralRight.conjTranspose = chiralRight := by
  dirac_compute chiralRight, gamma5

/-! ## Orthogonality -/

/-- The two chiralities are orthogonal: `P_L P_R = 0`. -/
lemma chiral_ortho_lr : chiralLeft * chiralRight = 0 := by
  dirac_compute chiralLeft, chiralRight, gamma5

/-- The two chiralities are orthogonal: `P_R P_L = 0`. Derived from `chiral_ortho_lr` by
    conjugate-transposing, using that both projectors are Hermitian. -/
lemma chiral_ortho_rl : chiralRight * chiralLeft = 0 := by
  have h := congrArg Matrix.conjTranspose chiral_ortho_lr
  rwa [Matrix.conjTranspose_mul, chiralLeft_hermitian, chiralRight_hermitian,
    Matrix.conjTranspose_zero] at h

/-! ## Action of `γ⁵` on the chiral subspaces -/

/-- `γ⁵ P_R = P_R`: the right-handed space is the `+1` eigenspace of `γ⁵`. -/
lemma gamma5_chiralRight : gamma5 * chiralRight = chiralRight := by
  dirac_compute chiralRight, gamma5

/-- `γ⁵ P_L = -P_L`: the left-handed space is the `-1` eigenspace of `γ⁵`. -/
lemma gamma5_chiralLeft : gamma5 * chiralLeft = -chiralLeft := by
  dirac_compute chiralLeft, gamma5

end Spectra.QuantumMechanics.Dirac

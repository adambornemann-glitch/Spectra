/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.DiracEquation.CliffordAlgebra
import Spectra.Spaces.Sobolev.WeakDerivative
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!
# The Dirac spinor Hilbert space `L²(ℝ³; ℂ⁴)`

A Dirac wavefunction is a square-integrable map `ℝ³ → ℂ⁴`. The natural state space is
the Hilbert space `L²(ℝ³; ℂ⁴)`, which is isometrically the `ℓ²`-direct sum of four
copies of the scalar space `L²(ℝ³)`:

  `L²(ℝ³; ℂ⁴) ≅ L²(ℝ³) ⊕ L²(ℝ³) ⊕ L²(ℝ³) ⊕ L²(ℝ³)`.

We take this `ℓ²`-sum model directly: `DiracSpinorL2 := PiLp 2 (fun _ : Fin 4 => l2R3)`, where
`l2R3` is the scalar space from `Spaces.Sobolev`. This makes all of the scalar Sobolev/Fourier
machinery available componentwise, which is what later files use to build the free Dirac operator.

The first piece of structure beyond the space itself is the action of a **constant** `4 × 4`
matrix `M` on spinor fields, `(M · ψ)ₐ(x) = Σ_b M_{ab} ψ_b(x)`. This is a *bounded* operator
`matrixOp M`, and it is self-adjoint exactly when `M` is Hermitian. In particular the Dirac mass
term `βmc²` is bounded and self-adjoint — the ingredient that lets `kato_rellich_bounded` add it
to the (unbounded) kinetic part.

## Main definitions

* `DiracSpinorL2` — the spinor Hilbert space `L²(ℝ³; ℂ⁴)`, defined as
  `PiLp 2 (fun _ : Fin 4 => l2R3)`.
* `matrixOp` — the bounded operator on `DiracSpinorL2` given by a constant `4 × 4` matrix.

## Main statements

* `DiracSpinorL2.inner_eq` — `⟪ψ, φ⟫ = Σ_a ⟪ψ_a, φ_a⟫`, the inner product
  componentwise.
* `matrixOp_apply` — `(matrixOp M ψ)_a = Σ_b M_{ab} • ψ_b`.
* `matrixOp_one`, `matrixOp_add`, `matrixOp_smul` — `matrixOp` is linear and unital.
* `matrixOp_mul` — `matrixOp (M * N) = matrixOp M ∘ matrixOp N`, so `matrixOp` is a
  representation of the matrix algebra.
* `matrixOp_adjoint` — `(matrixOp M)† = matrixOp Mᴴ`.
* `matrixOp_isSelfAdjoint_of_hermitian` — `matrixOp M` is self-adjoint when `M` is
  Hermitian.
* `matrixOp_diracBeta_isSelfAdjoint` — the mass-term matrix `β` gives a self-adjoint operator.
* `matrixOp_massTerm_isSelfAdjoint` — the full mass term `mc² · β` (real `mc²`) is
  self-adjoint; this is the ingredient the intro cites as enabling `kato_rellich_bounded`.

## Implementation notes

The spinor space is modelled as `PiLp 2 (fun _ : Fin 4 => l2R3)` — the honest `ℓ²`-sum of
four copies of the scalar `L²(ℝ³)` — rather than `EuclideanSpace ℂ (Fin 4)`-valued fields or
`L²(ℝ³) ⊗ ℂ⁴`. The `PiLp 2` model puts each spinor component in the *same* scalar space
`l2R3` that `Spaces.Sobolev` is built on, so the scalar Sobolev/Fourier machinery (weak
derivatives, the Fourier transform, the free Laplacian) is available componentwise with no
re-derivation, while still carrying the correct `ℓ²` inner product
`⟪ψ, φ⟫ = Σ_a ⟪ψ_a, φ_a⟫` (`DiracSpinorL2.inner_eq`).

`matrixOp M` is built by transporting the componentwise map through the identity continuous
linear equivalence `diracSpinorCLE : DiracSpinorL2 ≃L[ℂ] (Fin 4 → l2R3)` and assembling the
coordinate action with `ContinuousLinearMap.pi`/`ContinuousLinearMap.proj`
(`M ↦ pi (fun a => Σ_b M_{ab} • proj b)`). Routing through `diracSpinorCLE` this way lets us
reuse Mathlib's bounded `pi`/`proj` combinators — which give boundedness and continuity for
free — instead of hand-building a bounded map and separately discharging its operator-norm
bound; the equivalence is underlyingly the identity, so `matrixOp_apply` holds by `rfl`.

## References

* [Thaller, *The Dirac Equation*][thaller1992], Chapter 1
* [Reed, Simon, *Methods of Modern Mathematical Physics*][reed1975], Vol. II, §X.4

## Tags

Dirac equation, spinor, L2 space, bounded operator, self-adjoint, mass term
-/
open scoped InnerProductSpace
open Spectra.Sobolev

namespace Spectra.QuantumMechanics.Dirac

/-- The Dirac spinor Hilbert space `L²(ℝ³; ℂ⁴)`, modelled as the `ℓ²`-direct sum of four
copies of the scalar space `L²(ℝ³)`. A spinor field `ψ : DiracSpinorL2` has four components
`ψ a : l2R3` (`a : Fin 4`). -/
abbrev DiracSpinorL2 : Type := PiLp 2 (fun _ : Fin 4 => l2R3)

/-- The inner product on `L²(ℝ³; ℂ⁴)` is the sum of the four componentwise `L²` inner
products. -/
lemma DiracSpinorL2.inner_eq (ψ φ : DiracSpinorL2) :
    ⟪ψ, φ⟫_ℂ = ∑ a, ⟪ψ a, φ a⟫_ℂ :=
  PiLp.inner_apply ψ φ

/-- The continuous linear equivalence between the `ℓ²`-model and the plain product
`Fin 4 → l2R3`; underlyingly the identity, used to transport `ContinuousLinearMap.pi`/`proj`. -/
noncomputable def diracSpinorCLE : DiracSpinorL2 ≃L[ℂ] (Fin 4 → l2R3) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => l2R3)

/-- The action of a constant `4 × 4` complex matrix `M` on spinor fields:
`(matrixOp M ψ)_a = Σ_b M_{ab} • ψ_b`. A bounded operator, built from the coordinate
projections and inclusions. -/
noncomputable def matrixOp (M : Matrix (Fin 4) (Fin 4) ℂ) :
    DiracSpinorL2 →L[ℂ] DiracSpinorL2 :=
  diracSpinorCLE.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun a => ∑ b, (M a b) • ContinuousLinearMap.proj b)).comp
      diracSpinorCLE.toContinuousLinearMap)

@[simp] lemma matrixOp_apply (M : Matrix (Fin 4) (Fin 4) ℂ) (ψ : DiracSpinorL2) (a : Fin 4) :
    matrixOp M ψ a = ∑ b, M a b • ψ b :=
  rfl

/-! ## `matrixOp` is a unital `*`-algebra representation -/

/-- The identity matrix gives the identity operator. -/
@[simp] lemma matrixOp_one :
    matrixOp (1 : Matrix (Fin 4) (Fin 4) ℂ) = ContinuousLinearMap.id ℂ DiracSpinorL2 := by
  ext ψ a
  simp [Matrix.one_apply, ite_smul, Finset.sum_ite_eq]

/-- The zero matrix gives the zero operator. -/
@[simp] lemma matrixOp_zero :
    matrixOp (0 : Matrix (Fin 4) (Fin 4) ℂ) = 0 := by
  ext ψ a
  simp

/-- `matrixOp` is additive in the matrix. -/
lemma matrixOp_add (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    matrixOp (M + N) = matrixOp M + matrixOp N := by
  ext ψ a
  simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/-- `matrixOp` is compatible with scalar multiplication of the matrix. -/
lemma matrixOp_smul (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    matrixOp (c • M) = c • matrixOp M := by
  ext ψ a
  simp [Matrix.smul_apply, smul_smul, Finset.smul_sum]

/-- `matrixOp` is multiplicative: it sends matrix product to operator composition,
so it is a representation of the matrix algebra. -/
lemma matrixOp_mul (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    matrixOp (M * N) = (matrixOp M).comp (matrixOp N) := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  refine PiLp.ext fun a => ?_
  simp only [matrixOp_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

/-! ## Adjoint and self-adjointness -/

/-- The adjoint of `matrixOp M` is the operator of the conjugate-transpose matrix:
`(matrixOp M)† = matrixOp Mᴴ`. -/
lemma matrixOp_adjoint (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (matrixOp M).adjoint = matrixOp M.conjTranspose := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [DiracSpinorL2.inner_eq, matrixOp_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Matrix.conjTranspose_apply, starRingEnd_apply, star_star]
  rw [Finset.sum_comm]

/-- If the matrix `M` is Hermitian (`Mᴴ = M`), then `matrixOp M` is self-adjoint.
The Dirac mass term `βmc²` is of this form. -/
lemma matrixOp_isSelfAdjoint_of_hermitian {M : Matrix (Fin 4) (Fin 4) ℂ}
    (hM : M.conjTranspose = M) : IsSelfAdjoint (matrixOp M) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, matrixOp_adjoint, hM]

/-- The mass-term matrix `β` gives a bounded self-adjoint operator on `L²(ℝ³; ℂ⁴)`. -/
lemma matrixOp_diracBeta_isSelfAdjoint : IsSelfAdjoint (matrixOp diracBeta) :=
  matrixOp_isSelfAdjoint_of_hermitian diracBeta_hermitian

/-- The full mass term `mc² · β` (real `mc²`) is bounded and self-adjoint. -/
lemma matrixOp_massTerm_isSelfAdjoint (mc2 : ℝ) :
    IsSelfAdjoint (matrixOp ((mc2 : ℂ) • diracBeta)) := by
  refine matrixOp_isSelfAdjoint_of_hermitian ?_
  rw [Matrix.conjTranspose_smul, diracBeta_hermitian, RCLike.star_def, Complex.conj_ofReal]

end Spectra.QuantumMechanics.Dirac

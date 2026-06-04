/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Spectra/SimpleCheck.lean
-/
import Spectra.Uncertainty.SymmOperator
import Spectra.UnitaryEvolution.Stone.Bijection
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian

namespace QuantumMechanics.Instances
open InnerProductSpace Complex
open Yosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- # Simple check -/

/-- Rung 0: the trivial one-parameter group `U t = id`.  Its generator is `0`. -/
def trivialGroup : OneParameterUnitaryGroup (H := H) where
  U                 := fun _ => ContinuousLinearMap.id ℂ H
  unitary           := fun _ ψ φ => by simp
  group_law         := fun _ _ => by simp
  identity          := rfl
  strong_continuous := fun ψ => continuous_const

-- the machine accepts it and hands back a self-adjoint generator:
example : IsSelfAdjoint (generator (trivialGroup (H := H))) :=
  Bochner.generator_isSelfAdjoint _

-- and the whole bijection elaborates on a concrete input:
noncomputable example : {A : H →ₗ.[ℂ] H // IsSelfAdjoint A} :=
  StonesTheorem.stoneEquiv (trivialGroup (H := H))

/- # check 1 -/

/-- Any *bounded* self-adjoint `A` generates `U t = exp(i t A)`,
    assembled from the existing `expBounded` API. -/
noncomputable def boundedGroup (A : H →L[ℂ] H)
    (hA : ContinuousLinearMap.adjoint A = A) : OneParameterUnitaryGroup (H := H) where
  U := fun t => expBounded (I • A) t
  unitary := fun t ψ φ => by
    have hskew : ContinuousLinearMap.adjoint (I • A) = -(I • A) :=
      smul_I_skewSelfAdjoint A hA
    have h := (expBounded_skewAdjoint_unitary (I • A) hskew t).1
    calc ⟪expBounded (I • A) t ψ, expBounded (I • A) t φ⟫_ℂ
        = ⟪ψ, (expBounded (I • A) t).adjoint (expBounded (I • A) t φ)⟫_ℂ :=
          (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = ⟪ψ, ((expBounded (I • A) t).adjoint.comp (expBounded (I • A) t)) φ⟫_ℂ := rfl
      _ = ⟪ψ, (ContinuousLinearMap.id ℂ H) φ⟫_ℂ := by rw [h]
      _ = ⟪ψ, φ⟫_ℂ := by rw [ContinuousLinearMap.id_apply]
  group_law := fun s t => expBounded_add_smul (I • A) s t
  identity := by
    rw [@expBounded_at_zero']; abel
  strong_continuous := fun ψ => by
    have hc : Continuous (fun t : ℝ => expBounded (I • A) t) :=
      continuous_iff_continuousAt.mpr fun t =>
        (expBounded_hasDerivAt (I • A) t).continuousAt
    exact hc.clm_apply continuous_const

-- sanity: the construction still returns a self-adjoint generator
example (A : H →L[ℂ] H) (hA : ContinuousLinearMap.adjoint A = A) :
    IsSelfAdjoint (generator (boundedGroup A hA)) :=
  Bochner.generator_isSelfAdjoint _

/- # check 2 -/

abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- σ_z = diag(1, -1) as an operator on ℂ². -/
noncomputable def σz : Qubit →L[ℂ] Qubit :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)

lemma σz_isHermitian : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

lemma σz_selfAdjoint : ContinuousLinearMap.adjoint σz = σz := by
  have hstar : star (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] := by
    rw [Matrix.star_eq_conjTranspose]; exact σz_isHermitian
  rw [σz, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, hstar]

/-- Rung 2: the spin-precession group `exp(i t σ_z)` on ℂ². -/
noncomputable def spinPrecession : OneParameterUnitaryGroup (H := Qubit) :=
  boundedGroup σz σz_selfAdjoint

example : IsSelfAdjoint (generator spinPrecession) := Bochner.generator_isSelfAdjoint _

/- # check 3 -/

/-- A bounded operator as a partial operator on the full domain. -/
noncomputable def clmToPMap (T : Qubit →L[ℂ] Qubit) : Qubit →ₗ.[ℂ] Qubit where
  domain := ⊤
  toFun  := T.toLinearMap.comp (Submodule.subtype ⊤)

/-- A bounded Hermitian operator is a symmetric operator. -/
noncomputable def symmOpOfHermitian (T : Qubit →L[ℂ] Qubit)
    (hT : ContinuousLinearMap.adjoint T = T) : SymmetricOperator Qubit where
  toLinearPMap := clmToPMap T
  dense := by
    show Dense ((⊤ : Submodule ℂ Qubit) : Set Qubit)
    rw [Submodule.top_coe]; exact dense_univ
  symmetric := by
    intro x y
    show ⟪T (x : Qubit), (y : Qubit)⟫_ℂ = ⟪(x : Qubit), T (y : Qubit)⟫_ℂ
    rw [← hT, ContinuousLinearMap.adjoint_inner_left]
    simp_all only


/-- A Hermitian matrix yields a self-adjoint operator — the σ_z chain, generalised. -/
lemma toEuclideanCLM_selfAdjoint_of_isHermitian
    {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) M := by
  have hstar : star M = M := by rw [Matrix.star_eq_conjTranspose]; exact hM
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, hstar]

lemma σx_isHermitian : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

lemma σy_isHermitian : (!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

noncomputable def σx : SymmetricOperator Qubit :=
  symmOpOfHermitian (Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
    (toEuclideanCLM_selfAdjoint_of_isHermitian σx_isHermitian)

noncomputable def σy : SymmetricOperator Qubit :=
  symmOpOfHermitian (Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ))
    (toEuclideanCLM_selfAdjoint_of_isHermitian σy_isHermitian)


/- # check 4 -/

/-- Spin-up along z. -/
noncomputable def ψ₀ : Qubit := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)

lemma norm_ψ₀ : ‖ψ₀‖ = 1 := by
  simp [ψ₀, PiLp.norm_single]

/-- The Pauli commutator, as a matrix identity:  [σ_x, σ_y] = 2i σ_z. -/
lemma pauli_xy_commutator :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, -I; I, 0]
      - (!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0]
      = (2 * I) • !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons,
      Matrix.head_cons, zero_smul, Matrix.tail_cons, one_smul, Matrix.empty_vecMul, add_zero,
      zero_add, Matrix.empty_mul, Equiv.symm_apply_apply, neg_smul, Matrix.smul_cons, smul_eq_mul,
      mul_one, mul_zero, Matrix.smul_empty, Matrix.neg_cons, neg_zero, Matrix.neg_empty,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.sub_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero, sub_self,
      Matrix.smul_apply] <;> ring

/-- σ_z fixes spin-up:  σ_z · e₀ = e₀. -/
lemma σz_clm_ψ₀ :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) ψ₀ = ψ₀ := by
  ext i
  fin_cases i <;>
    simp [ψ₀, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec]

/-- Operator-level identity, all at the algebra-hom level — no application in sight. -/
lemma comm_operators_eq :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
        * Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      - Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ)
          * Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      = (2 * I) • Matrix.toEuclideanCLM (𝕜 := ℂ) (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ)),
      ← map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ)),
      ← map_sub (Matrix.toEuclideanCLM (𝕜 := ℂ)),
      pauli_xy_commutator,
      map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ))]

lemma comm_operators_ψ₀ :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ) ψ₀)
      - Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, -I; I, 0] : Matrix (Fin 2) (Fin 2) ℂ)
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ψ₀)
      = (2 * I) • ψ₀ := by
  have h := congrArg (fun T : Qubit →L[ℂ] Qubit => T ψ₀) comm_operators_eq
  simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
         ContinuousLinearMap.smul_apply, σz_clm_ψ₀] using h



end QuantumMechanics.Instances

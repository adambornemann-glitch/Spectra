/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Tensor.Power
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Sign

/-!
# The bosonic symmetrizer and fermionic antisymmetrizer

The projections onto the symmetric (bosonic) and antisymmetric (fermionic) subspaces of the
`n`-particle sector `HilbertTensorPower 𝕜 n H`:

`symProj = (n!)⁻¹ ∑_σ U_σ`,  `altProj = (n!)⁻¹ ∑_σ sign(σ) U_σ`,

where `U_σ = permUnitary 𝕜 H σ` is the permutation unitary of
`Spectra/Spaces/Tensor/Power.lean`. Both are **orthogonal projections**: self-adjoint
idempotent contractions. This is Fock Spaces milestone M2 step 1; the ranges (the bose/fermi
sectors themselves) are built on top of these projections in follow-up files.

## Conventions

Following Parthasarathy, the symmetric/antisymmetric subspaces carry the inner product
*restricted* from the full tensor power — no `n!` rescaling. Accordingly the projections
average (rather than sum) over the permutation group. Pure-tensor formulas are stated with
the action `σ ↦ x ∘ σ` (i.e. `tprod 𝕜 fun i => x (σ i)`); summing over the group makes the
`σ` vs `σ.symm` choice immaterial.

## Main definitions

* `Spectra.HilbertTensorPower.permCLM σ` — `permUnitary σ` as a continuous linear map.
* `Spectra.HilbertTensorPower.permSign 𝕜 σ` — the sign of `σ` as a scalar in `𝕜`.
* `Spectra.HilbertTensorPower.symProj 𝕜 n H` — the bosonic symmetrizer.
* `Spectra.HilbertTensorPower.altProj 𝕜 n H` — the fermionic antisymmetrizer.

## Main results

* `permUnitary_comp` / `permUnitary_one` / `permUnitary_symm` — the group law of the
  permutation action on the completed tensor power.
* `adjoint_permCLM` — `(U_σ)⋆ = U_{σ⁻¹}`.
* `symProj_tprod` / `altProj_tprod` — action on pure tensors.
* `permUnitary_symProj` / `permUnitary_altProj` — `U_τ P_± = (±1)^τ P_±` (invariance).
* `symProj_idem` / `altProj_idem` — idempotency (`P² = P`).
* `isSelfAdjoint_symProj` / `isSelfAdjoint_altProj` — self-adjointness.
* `norm_symProj_le` / `norm_altProj_le` — contractivity `‖P‖ ≤ 1`.
* `symProj_comp_altProj` / `altProj_comp_symProj` — mutual orthogonality for `2 ≤ n`.
-/

noncomputable section

open scoped TensorProduct Nat
open PiTensorProduct UniformSpace

namespace Spectra

variable (𝕜 : Type*) (n : ℕ) (H : Type*) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace HilbertTensorPower

variable {𝕜 n H}

/-! ## The group law of the permutation action -/

/-- The permutation action on the algebraic tensor power composes contravariantly in the
arguments and covariantly in the group: `σ ∘ τ` acts as `σ * τ`. -/
theorem permIsometry_comp (σ τ : Equiv.Perm (Fin n)) (t : ⨂[𝕜]^n H) :
    permIsometry 𝕜 H σ (permIsometry 𝕜 H τ t) = permIsometry 𝕜 H (σ * τ) t := by
  simp only [permIsometry_apply]
  rw [Equiv.Perm.mul_def]
  exact reindex_reindex τ σ t

/-- The identity permutation acts trivially on the algebraic tensor power. -/
theorem permIsometry_one (t : ⨂[𝕜]^n H) :
    permIsometry 𝕜 H (1 : Equiv.Perm (Fin n)) t = t := by
  rw [permIsometry_apply, Equiv.Perm.one_def, reindex_refl, LinearEquiv.refl_apply]

/-- **Group law** for the permutation unitaries: `U_σ U_τ = U_{στ}`. -/
theorem permUnitary_comp (σ τ : Equiv.Perm (Fin n)) (x : HilbertTensorPower 𝕜 n H) :
    permUnitary 𝕜 H σ (permUnitary 𝕜 H τ x) = permUnitary 𝕜 H (σ * τ) x := by
  refine Completion.induction_on x
    (isClosed_eq ((permUnitary 𝕜 H σ).continuous.comp (permUnitary 𝕜 H τ).continuous)
      (permUnitary 𝕜 H (σ * τ)).continuous) fun t => ?_
  simp only [permUnitary, LinearIsometryEquiv.completionMap_coe]
  rw [permIsometry_comp]

/-- The identity permutation acts trivially on the Hilbert tensor power. -/
@[simp]
theorem permUnitary_one_apply (x : HilbertTensorPower 𝕜 n H) :
    permUnitary 𝕜 H (1 : Equiv.Perm (Fin n)) x = x := by
  refine Completion.induction_on x
    (isClosed_eq (permUnitary 𝕜 H (1 : Equiv.Perm (Fin n))).continuous continuous_id)
    fun t => ?_
  simp only [permUnitary, LinearIsometryEquiv.completionMap_coe]
  rw [permIsometry_one]

/-- The permutation unitary of the identity is the identity. -/
theorem permUnitary_one :
    permUnitary 𝕜 H (1 : Equiv.Perm (Fin n))
      = LinearIsometryEquiv.refl 𝕜 (HilbertTensorPower 𝕜 n H) :=
  LinearIsometryEquiv.ext fun x => permUnitary_one_apply x

/-- The inverse of a permutation unitary is the unitary of the inverse permutation. -/
theorem permUnitary_symm (σ : Equiv.Perm (Fin n)) :
    (permUnitary 𝕜 H σ).symm = permUnitary 𝕜 H σ⁻¹ := by
  refine LinearIsometryEquiv.ext fun x => ?_
  apply (permUnitary 𝕜 H σ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, permUnitary_comp, mul_inv_cancel,
    permUnitary_one_apply]

/-- Moving a permutation unitary to the other slot of the inner product inverts it:
`⟪U_σ x, y⟫ = ⟪x, U_{σ⁻¹} y⟫`. -/
theorem inner_permUnitary_left (σ : Equiv.Perm (Fin n)) (x y : HilbertTensorPower 𝕜 n H) :
    inner 𝕜 (permUnitary 𝕜 H σ x) y = inner 𝕜 x (permUnitary 𝕜 H σ⁻¹ y) :=
  calc inner 𝕜 (permUnitary 𝕜 H σ x) y
      = inner 𝕜 (permUnitary 𝕜 H σ x) (permUnitary 𝕜 H σ (permUnitary 𝕜 H σ⁻¹ y)) := by
        rw [permUnitary_comp, mul_inv_cancel, permUnitary_one_apply]
    _ = inner 𝕜 x (permUnitary 𝕜 H σ⁻¹ y) :=
        (permUnitary 𝕜 H σ).inner_map_map x (permUnitary 𝕜 H σ⁻¹ y)

/-! ## The permutation unitaries as continuous linear maps -/

variable (𝕜 H) in
/-- The permutation unitary `permUnitary 𝕜 H σ` as a continuous linear map, ready for
summing and for taking adjoints. -/
def permCLM (σ : Equiv.Perm (Fin n)) :
    HilbertTensorPower 𝕜 n H →L[𝕜] HilbertTensorPower 𝕜 n H :=
  (permUnitary 𝕜 H σ).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem permCLM_apply (σ : Equiv.Perm (Fin n)) (x : HilbertTensorPower 𝕜 n H) :
    permCLM 𝕜 H σ x = permUnitary 𝕜 H σ x := rfl

/-- Permutation unitaries are contractions (in fact isometries). -/
theorem norm_permCLM_le (σ : Equiv.Perm (Fin n)) : ‖permCLM 𝕜 H σ‖ ≤ 1 :=
  (permUnitary 𝕜 H σ).toLinearIsometry.norm_toContinuousLinearMap_le

/-- The adjoint of a permutation unitary is the unitary of the inverse permutation. -/
theorem adjoint_permCLM (σ : Equiv.Perm (Fin n)) :
    ContinuousLinearMap.adjoint (permCLM 𝕜 H σ) = permCLM 𝕜 H σ⁻¹ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [permCLM_apply]
  rw [inner_permUnitary_left, inv_inv]

/-! ## The sign as a scalar -/

variable (𝕜) in
/-- The sign of a permutation as a scalar in `𝕜`. -/
def permSign (σ : Equiv.Perm (Fin n)) : 𝕜 := ((Equiv.Perm.sign σ : ℤ) : 𝕜)

/-- The scalar sign is multiplicative. -/
theorem permSign_mul (σ τ : Equiv.Perm (Fin n)) :
    permSign 𝕜 (σ * τ) = permSign 𝕜 σ * permSign 𝕜 τ := by
  simp only [permSign]
  rw [map_mul, Units.val_mul, Int.cast_mul]

/-- The scalar sign of an inverse. -/
@[simp]
theorem permSign_inv (σ : Equiv.Perm (Fin n)) : permSign 𝕜 σ⁻¹ = permSign 𝕜 σ := by
  simp only [permSign]
  rw [Equiv.Perm.sign_inv]

/-- The scalar sign squares to one. -/
theorem permSign_mul_self (σ : Equiv.Perm (Fin n)) :
    permSign 𝕜 σ * permSign 𝕜 σ = 1 := by
  simp only [permSign]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num

/-- The scalar sign has norm one. -/
theorem norm_permSign (σ : Equiv.Perm (Fin n)) : ‖permSign 𝕜 σ‖ = 1 := by
  simp only [permSign]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp

/-- The scalar sign is real: it is fixed by conjugation. -/
theorem conj_permSign (σ : Equiv.Perm (Fin n)) :
    (starRingEnd 𝕜) (permSign 𝕜 σ) = permSign 𝕜 σ := by
  simp only [permSign]
  exact map_intCast (starRingEnd 𝕜) _

/-! ## The symmetrizers -/

variable (𝕜 n H) in
/-- The **bosonic symmetrizer**: the average `(n!)⁻¹ ∑_σ U_σ` of the permutation unitaries.
An orthogonal projection (`symProj_idem`, `isSelfAdjoint_symProj`, `norm_symProj_le`); its
range is the symmetric (bosonic) `n`-particle sector. -/
def symProj : HilbertTensorPower 𝕜 n H →L[𝕜] HilbertTensorPower 𝕜 n H :=
  (n ! : 𝕜)⁻¹ • ∑ σ : Equiv.Perm (Fin n), permCLM 𝕜 H σ

variable (𝕜 n H) in
/-- The **fermionic antisymmetrizer**: the signed average `(n!)⁻¹ ∑_σ sign(σ) U_σ` of the
permutation unitaries. An orthogonal projection (`altProj_idem`, `isSelfAdjoint_altProj`,
`norm_altProj_le`); its range is the antisymmetric (fermionic) `n`-particle sector. -/
def altProj : HilbertTensorPower 𝕜 n H →L[𝕜] HilbertTensorPower 𝕜 n H :=
  (n ! : 𝕜)⁻¹ • ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • permCLM 𝕜 H σ

/-- The symmetrizer, applied pointwise. -/
theorem symProj_apply (x : HilbertTensorPower 𝕜 n H) :
    symProj 𝕜 n H x = (n ! : 𝕜)⁻¹ • ∑ σ : Equiv.Perm (Fin n), permUnitary 𝕜 H σ x := by
  simp only [symProj, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    permCLM_apply]

/-- The antisymmetrizer, applied pointwise. -/
theorem altProj_apply (x : HilbertTensorPower 𝕜 n H) :
    altProj 𝕜 n H x
      = (n ! : 𝕜)⁻¹ • ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • permUnitary 𝕜 H σ x := by
  simp only [altProj, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    permCLM_apply]

/-- The symmetrizer on a pure tensor averages over all permutations of the slots. -/
theorem symProj_tprod (x : Fin n → H) :
    symProj 𝕜 n H (tprod 𝕜 x)
      = (n ! : 𝕜)⁻¹ • ∑ σ : Equiv.Perm (Fin n), tprod 𝕜 fun i => x (σ i) := by
  rw [symProj_apply]
  congr 1
  exact Fintype.sum_bijective Inv.inv inv_bijective _ _ fun σ => by simp

/-- The antisymmetrizer on a pure tensor: the signed average over all permutations. -/
theorem altProj_tprod (x : Fin n → H) :
    altProj 𝕜 n H (tprod 𝕜 x)
      = (n ! : 𝕜)⁻¹ •
        ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • tprod 𝕜 fun i => x (σ i) := by
  rw [altProj_apply]
  congr 1
  exact Fintype.sum_bijective Inv.inv inv_bijective _ _ fun σ => by simp

/-! ## Invariance under the permutation action -/

/-- The symmetrizer's output is invariant under every permutation unitary. -/
theorem permUnitary_symProj (τ : Equiv.Perm (Fin n)) (x : HilbertTensorPower 𝕜 n H) :
    permUnitary 𝕜 H τ (symProj 𝕜 n H x) = symProj 𝕜 n H x := by
  rw [symProj_apply, map_smul, map_sum]
  congr 1
  simp only [permUnitary_comp]
  exact Fintype.sum_bijective (τ * ·) (Group.mulLeft_bijective τ) _ _ fun σ => rfl

/-- The symmetrizer is invariant under precomposition with a permutation unitary. -/
theorem symProj_permUnitary (τ : Equiv.Perm (Fin n)) (x : HilbertTensorPower 𝕜 n H) :
    symProj 𝕜 n H (permUnitary 𝕜 H τ x) = symProj 𝕜 n H x := by
  rw [symProj_apply, symProj_apply]
  congr 1
  simp only [permUnitary_comp]
  exact Fintype.sum_bijective (· * τ) (Group.mulRight_bijective τ) _ _ fun σ => rfl

/-- The antisymmetrizer's output transforms with the sign under permutation unitaries. -/
theorem permUnitary_altProj (τ : Equiv.Perm (Fin n)) (x : HilbertTensorPower 𝕜 n H) :
    permUnitary 𝕜 H τ (altProj 𝕜 n H x) = permSign 𝕜 τ • altProj 𝕜 n H x := by
  rw [altProj_apply, map_smul, map_sum]
  simp only [map_smul, permUnitary_comp]
  have key : ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • permUnitary 𝕜 H (τ * σ) x
      = ∑ σ : Equiv.Perm (Fin n), (permSign 𝕜 τ * permSign 𝕜 σ) • permUnitary 𝕜 H σ x := by
    refine Fintype.sum_bijective (τ * ·) (Group.mulLeft_bijective τ) _ _ fun σ => ?_
    congr 1
    rw [permSign_mul, ← mul_assoc, permSign_mul_self, one_mul]
  rw [key]
  simp only [mul_smul]
  rw [← Finset.smul_sum, smul_comm]

/-- The antisymmetrizer picks up the sign under precomposition with a permutation
unitary. -/
theorem altProj_permUnitary (τ : Equiv.Perm (Fin n)) (x : HilbertTensorPower 𝕜 n H) :
    altProj 𝕜 n H (permUnitary 𝕜 H τ x) = permSign 𝕜 τ • altProj 𝕜 n H x := by
  rw [altProj_apply, altProj_apply]
  simp only [permUnitary_comp]
  have key : ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • permUnitary 𝕜 H (σ * τ) x
      = ∑ σ : Equiv.Perm (Fin n), (permSign 𝕜 τ * permSign 𝕜 σ) • permUnitary 𝕜 H σ x := by
    refine Fintype.sum_bijective (· * τ) (Group.mulRight_bijective τ) _ _ fun σ => ?_
    congr 1
    rw [permSign_mul, mul_left_comm, permSign_mul_self, mul_one]
  rw [key]
  simp only [mul_smul]
  rw [← Finset.smul_sum, smul_comm]

/-! ## Idempotency -/

/-- The symmetrizer is idempotent, pointwise. -/
theorem symProj_symProj (x : HilbertTensorPower 𝕜 n H) :
    symProj 𝕜 n H (symProj 𝕜 n H x) = symProj 𝕜 n H x := by
  conv_lhs => rw [symProj_apply]
  simp only [permUnitary_symProj]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]

/-- **Idempotency** of the bosonic symmetrizer: `P₊ ∘ P₊ = P₊`. -/
theorem symProj_idem : symProj 𝕜 n H ∘L symProj 𝕜 n H = symProj 𝕜 n H :=
  ContinuousLinearMap.ext fun x => symProj_symProj x

/-- The bosonic symmetrizer is an idempotent element of the operator algebra. -/
theorem isIdempotentElem_symProj : IsIdempotentElem (symProj 𝕜 n H) := by
  change symProj 𝕜 n H * symProj 𝕜 n H = symProj 𝕜 n H
  rw [ContinuousLinearMap.mul_def]
  exact symProj_idem

/-- The antisymmetrizer is idempotent, pointwise. -/
theorem altProj_altProj (x : HilbertTensorPower 𝕜 n H) :
    altProj 𝕜 n H (altProj 𝕜 n H x) = altProj 𝕜 n H x := by
  conv_lhs => rw [altProj_apply]
  simp only [permUnitary_altProj, smul_smul, permSign_mul_self, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]

/-- **Idempotency** of the fermionic antisymmetrizer: `P₋ ∘ P₋ = P₋`. -/
theorem altProj_idem : altProj 𝕜 n H ∘L altProj 𝕜 n H = altProj 𝕜 n H :=
  ContinuousLinearMap.ext fun x => altProj_altProj x

/-- The fermionic antisymmetrizer is an idempotent element of the operator algebra. -/
theorem isIdempotentElem_altProj : IsIdempotentElem (altProj 𝕜 n H) := by
  change altProj 𝕜 n H * altProj 𝕜 n H = altProj 𝕜 n H
  rw [ContinuousLinearMap.mul_def]
  exact altProj_idem

/-! ## Self-adjointness -/

/-- The symmetrizer is symmetric for the inner product. -/
theorem inner_symProj_left (x y : HilbertTensorPower 𝕜 n H) :
    inner 𝕜 (symProj 𝕜 n H x) y = inner 𝕜 x (symProj 𝕜 n H y) := by
  rw [symProj_apply, symProj_apply, inner_smul_left, inner_smul_right, sum_inner,
    inner_sum, map_inv₀, map_natCast]
  congr 1
  calc ∑ σ : Equiv.Perm (Fin n), inner 𝕜 (permUnitary 𝕜 H σ x) y
      = ∑ σ : Equiv.Perm (Fin n), inner 𝕜 x (permUnitary 𝕜 H σ⁻¹ y) :=
        Finset.sum_congr rfl fun σ _ => inner_permUnitary_left σ x y
    _ = ∑ σ : Equiv.Perm (Fin n), inner 𝕜 x (permUnitary 𝕜 H σ y) :=
        Fintype.sum_bijective Inv.inv inv_bijective _ _ fun σ => rfl

/-- **Self-adjointness** of the bosonic symmetrizer. -/
theorem isSelfAdjoint_symProj : IsSelfAdjoint (symProj 𝕜 n H) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact fun x y => inner_symProj_left x y

/-- The antisymmetrizer is symmetric for the inner product. -/
theorem inner_altProj_left (x y : HilbertTensorPower 𝕜 n H) :
    inner 𝕜 (altProj 𝕜 n H x) y = inner 𝕜 x (altProj 𝕜 n H y) := by
  rw [altProj_apply, altProj_apply, inner_smul_left, inner_smul_right, sum_inner,
    inner_sum, map_inv₀, map_natCast]
  congr 1
  calc ∑ σ : Equiv.Perm (Fin n), inner 𝕜 (permSign 𝕜 σ • permUnitary 𝕜 H σ x) y
      = ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ * inner 𝕜 x (permUnitary 𝕜 H σ⁻¹ y) :=
        Finset.sum_congr rfl fun σ _ => by
          rw [inner_smul_left, conj_permSign, inner_permUnitary_left]
    _ = ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ * inner 𝕜 x (permUnitary 𝕜 H σ y) :=
        Fintype.sum_bijective Inv.inv inv_bijective _ _ fun σ => by rw [permSign_inv]
    _ = ∑ σ : Equiv.Perm (Fin n), inner 𝕜 x (permSign 𝕜 σ • permUnitary 𝕜 H σ y) :=
        Finset.sum_congr rfl fun σ _ => by rw [inner_smul_right]

/-- **Self-adjointness** of the fermionic antisymmetrizer. -/
theorem isSelfAdjoint_altProj : IsSelfAdjoint (altProj 𝕜 n H) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact fun x y => inner_altProj_left x y

/-! ## Contractivity -/

/-- The bosonic symmetrizer is a contraction: `‖P₊‖ ≤ 1`. -/
theorem norm_symProj_le : ‖symProj 𝕜 n H‖ ≤ 1 := by
  rw [symProj, norm_smul, norm_inv, RCLike.norm_natCast]
  calc (n ! : ℝ)⁻¹ * ‖∑ σ : Equiv.Perm (Fin n), permCLM 𝕜 H σ‖
      ≤ (n ! : ℝ)⁻¹ * (n ! : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖∑ σ : Equiv.Perm (Fin n), permCLM 𝕜 H σ‖
            ≤ ∑ σ : Equiv.Perm (Fin n), ‖permCLM 𝕜 H σ‖ := norm_sum_le _ _
          _ ≤ ∑ _σ : Equiv.Perm (Fin n), (1 : ℝ) :=
              Finset.sum_le_sum fun σ _ => norm_permCLM_le σ
          _ = (n ! : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
                nsmul_eq_mul, mul_one]
    _ = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)

/-- The fermionic antisymmetrizer is a contraction: `‖P₋‖ ≤ 1`. -/
theorem norm_altProj_le : ‖altProj 𝕜 n H‖ ≤ 1 := by
  rw [altProj, norm_smul, norm_inv, RCLike.norm_natCast]
  calc (n ! : ℝ)⁻¹ * ‖∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • permCLM 𝕜 H σ‖
      ≤ (n ! : ℝ)⁻¹ * (n ! : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ • permCLM 𝕜 H σ‖
            ≤ ∑ σ : Equiv.Perm (Fin n), ‖permSign 𝕜 σ • permCLM 𝕜 H σ‖ := norm_sum_le _ _
          _ ≤ ∑ _σ : Equiv.Perm (Fin n), (1 : ℝ) := by
              refine Finset.sum_le_sum fun σ _ => ?_
              rw [norm_smul, norm_permSign, one_mul]
              exact norm_permCLM_le σ
          _ = (n ! : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
                nsmul_eq_mul, mul_one]
    _ = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)

/-! ## Mutual orthogonality (`2 ≤ n`) -/

/-- For `2 ≤ n`, the signs of all permutations sum to zero: pairing `σ ↔ (swap) * σ`
against a fixed transposition cancels the sum. -/
theorem sum_permSign_eq_zero (hn : 2 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ = 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, i ≠ j :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hswap : permSign 𝕜 (Equiv.swap i j) = -1 := by
    rw [permSign, Equiv.Perm.sign_swap hij]
    simp
  have key : ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ
      = -∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ := by
    conv_lhs => rw [show (∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ)
        = ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 (Equiv.swap i j * σ) from
      (Fintype.sum_bijective (Equiv.swap i j * ·)
        (Group.mulLeft_bijective (Equiv.swap i j)) _ _ fun σ => rfl).symm]
    simp only [permSign_mul, hswap, neg_one_mul]
    exact Finset.sum_neg_distrib fun σ => permSign 𝕜 σ
  have h2 : (2 : 𝕜) * ∑ σ : Equiv.Perm (Fin n), permSign 𝕜 σ = 0 := by
    rw [two_mul]
    nth_rewrite 1 [key]
    rw [neg_add_cancel]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h two_ne_zero
  · exact h

/-- For `2 ≤ n`, symmetrizing an antisymmetrized state annihilates it: `P₊ ∘ P₋ = 0`. -/
theorem symProj_comp_altProj (hn : 2 ≤ n) :
    symProj 𝕜 n H ∘L altProj 𝕜 n H = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  change symProj 𝕜 n H (altProj 𝕜 n H x) = 0
  rw [symProj_apply]
  simp only [permUnitary_altProj]
  rw [← Finset.sum_smul, sum_permSign_eq_zero hn, zero_smul, smul_zero]

/-- For `2 ≤ n`, antisymmetrizing a symmetrized state annihilates it: `P₋ ∘ P₊ = 0`. -/
theorem altProj_comp_symProj (hn : 2 ≤ n) :
    altProj 𝕜 n H ∘L symProj 𝕜 n H = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  change altProj 𝕜 n H (symProj 𝕜 n H x) = 0
  rw [altProj_apply]
  simp only [permUnitary_symProj]
  rw [← Finset.sum_smul, sum_permSign_eq_zero hn, zero_smul, smul_zero]

end HilbertTensorPower

end Spectra

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Tensor.Hilbert

/-!
# Bounded functoriality of the Hilbert tensor product: `A ⊗̂ B`

Mathlib's `TensorProduct.map A B` is a bare linear map, and upgrading it to a *continuous*
linear map is an explicit TODO of `Analysis/InnerProductSpace/TensorProduct.lean`. This file
proves the operator-norm bound and extends through the completion, yielding the bounded
functoriality of `⊗̂` with the **cross-norm identity** `‖A ⊗̂ B‖ = ‖A‖ * ‖B‖`.

## The kernel

The heart of the file is the *orthonormal fiber representation*
(`exists_sum_tmul_orthonormal`): every algebraic tensor `t : E ⊗[𝕜] F` can be written
`t = ∑ j, x j ⊗ₜ g j` with `(g j)` a **finite orthonormal** family in `F`. Against such a
representation the tensor inner product is diagonal (`norm_sq_sum_tmul_orthonormal`,
Pythagoras: `‖∑ j, x j ⊗ₜ g j‖² = ∑ j, ‖x j‖²`), so

`‖(A ⊗ 1) t‖² = ∑ j ‖A (x j)‖² ≤ ‖A‖² ∑ j ‖x j‖² = ‖A‖² ‖t‖²`,

which is `norm_rTensor_apply_le`. The left factor follows by conjugating with the braiding
isometry, and `A ⊗ B = (A ⊗ 1) ∘ (1 ⊗ B)` combines the two.

## Main definitions

* `Spectra.HilbertTensor.mapCLM A B` — `TensorProduct.map` upgraded to a continuous linear
  map `E ⊗[𝕜] F →L[𝕜] G ⊗[𝕜] H` on the algebraic tensor products.
* `Spectra.HilbertTensor.mapL A B` — the extension `E ⊗̂[𝕜] F →L[𝕜] G ⊗̂[𝕜] H` through the
  completion: the bounded functoriality of the Hilbert tensor product.
* `ContinuousLinearMap.norm_completion` — `‖f.completion‖ = ‖f‖` (general-purpose companion
  to `ContinuousLinearMap.completion`; upstream candidate).

## Main results

* `Spectra.HilbertTensor.norm_map_apply_le` — `‖(A ⊗ B) t‖ ≤ ‖A‖ * ‖B‖ * ‖t‖`.
* `Spectra.HilbertTensor.norm_mapCLM` / `norm_mapL` — the cross-norm identity
  `‖A ⊗̂ B‖ = ‖A‖ * ‖B‖` (the bound is attained: test on pure tensors).
* `Spectra.HilbertTensor.mapL_tmul` — `(A ⊗̂ B) (x ⊗̂ₜ y) = A x ⊗̂ₜ B y`.
-/

noncomputable section

open scoped TensorProduct
open UniformSpace

/-! ## `‖f.completion‖ = ‖f‖`

General-purpose companion to `ContinuousLinearMap.completion`; upstream candidate. -/

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Extending a continuous linear map through the completions preserves the operator norm. -/
@[simp]
theorem norm_completion (f : E →L[𝕜] F) : ‖f.completion‖ = ‖f‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun x => ?_)
    (opNorm_le_bound _ (norm_nonneg f.completion) fun a => ?_)
  · refine Completion.induction_on x
      (isClosed_le (continuous_norm.comp f.completion.continuous)
        (continuous_const.mul continuous_norm)) fun a => ?_
    rw [completion_apply_coe, Completion.norm_coe, Completion.norm_coe]
    exact f.le_opNorm a
  · calc ‖f a‖ = ‖f.completion (a : Completion E)‖ := by
          rw [completion_apply_coe, Completion.norm_coe]
    _ ≤ ‖f.completion‖ * ‖(a : Completion E)‖ := f.completion.le_opNorm _
    _ = ‖f.completion‖ * ‖a‖ := by rw [Completion.norm_coe]

end ContinuousLinearMap

namespace Spectra.HilbertTensor

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ## Pythagoras against an orthonormal fiber -/

/-- Against an orthonormal second-factor family the tensor inner product is diagonal. -/
theorem inner_self_sum_tmul_orthonormal {n : ℕ} (x : Fin n → E) {g : Fin n → F}
    (hg : Orthonormal 𝕜 g) :
    inner 𝕜 (∑ j, x j ⊗ₜ[𝕜] g j) (∑ j, x j ⊗ₜ[𝕜] g j)
      = ((∑ j, ‖x j‖ ^ 2 : ℝ) : 𝕜) := by
  have horth := orthonormal_iff_ite.mp hg
  calc inner 𝕜 (∑ j, x j ⊗ₜ[𝕜] g j) (∑ k, x k ⊗ₜ[𝕜] g k)
      = ∑ j, ∑ k, inner 𝕜 (x j) (x k) * inner 𝕜 (g j) (g k) := by
        rw [sum_inner]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inner_sum]
        exact Finset.sum_congr rfl fun k _ => TensorProduct.inner_tmul 𝕜 _ _ _ _
    _ = ∑ j, inner 𝕜 (x j) (x j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single j
          (fun k _ hk => by rw [horth j k, if_neg fun h => hk h.symm, mul_zero])
          (fun h => absurd (Finset.mem_univ j) h)]
        rw [horth j j, if_pos rfl, mul_one]
    _ = ((∑ j, ‖x j‖ ^ 2 : ℝ) : 𝕜) := by
        push_cast
        exact Finset.sum_congr rfl fun j _ => inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (x j)

/-- **Pythagoras** in the tensor product: against an orthonormal second-factor family,
`‖∑ j, x j ⊗ₜ g j‖² = ∑ j, ‖x j‖²`. -/
theorem norm_sq_sum_tmul_orthonormal {n : ℕ} (x : Fin n → E) {g : Fin n → F}
    (hg : Orthonormal 𝕜 g) :
    ‖∑ j, x j ⊗ₜ[𝕜] g j‖ ^ 2 = ∑ j, ‖x j‖ ^ 2 := by
  have h := congrArg (RCLike.re (K := 𝕜)) (inner_self_sum_tmul_orthonormal x hg)
  rwa [inner_self_eq_norm_sq, RCLike.ofReal_re] at h

/-! ## The orthonormal fiber representation -/

/-- **Orthonormal fiber representation**: every algebraic tensor can be written as a finite
sum `∑ j, x j ⊗ₜ g j` with `(g j)` orthonormal. Obtained by expanding an arbitrary finite
pure-tensor representation against an orthonormal basis of the (finite-dimensional) span of
its second components.

Note the first factor `X` needs only a module structure — no inner product, no topology.
This generality is load-bearing: the tensor-power layer applies it with `X = ⨂[𝕜]^n H`
*before* that space carries any analytic structure. -/
theorem exists_sum_tmul_orthonormal {X : Type*} [AddCommGroup X] [Module 𝕜 X]
    (t : X ⊗[𝕜] F) :
    ∃ (n : ℕ) (x : Fin n → X) (g : Fin n → F),
      Orthonormal 𝕜 g ∧ t = ∑ j, x j ⊗ₜ[𝕜] g j := by
  classical
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset t
  set W : Submodule 𝕜 F := Submodule.span 𝕜 ((S.image Prod.snd : Finset F) : Set F) with _hW
  let g := stdOrthonormalBasis 𝕜 W
  refine ⟨Module.finrank 𝕜 W,
    fun j => ∑ p ∈ S, inner 𝕜 ((g j : F)) p.2 • p.1, fun j => (g j : F), ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    rw [← Submodule.coe_inner, orthonormal_iff_ite.mp g.orthonormal]
  · calc ∑ p ∈ S, p.1 ⊗ₜ[𝕜] p.2
        = ∑ p ∈ S, ∑ j, (inner 𝕜 ((g j : F)) p.2 • p.1) ⊗ₜ[𝕜] (g j : F) := ?_
      _ = ∑ j, ∑ p ∈ S, (inner 𝕜 ((g j : F)) p.2 • p.1) ⊗ₜ[𝕜] (g j : F) :=
          Finset.sum_comm
      _ = ∑ j, (∑ p ∈ S, inner 𝕜 ((g j : F)) p.2 • p.1) ⊗ₜ[𝕜] (g j : F) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 : p.2 ∈ W := Submodule.subset_span (by
      exact_mod_cast Finset.mem_image_of_mem Prod.snd hp)
    have hrepr : ∑ j, inner 𝕜 ((g j : F)) p.2 • (g j : F) = p.2 := by
      have h := congrArg (Submodule.subtype W) (g.sum_repr' (⟨p.2, hp2⟩ : W))
      simpa [Submodule.coe_inner] using h
    calc p.1 ⊗ₜ[𝕜] p.2
        = p.1 ⊗ₜ[𝕜] (∑ j, inner 𝕜 ((g j : F)) p.2 • (g j : F)) := by rw [hrepr]
      _ = ∑ j, p.1 ⊗ₜ[𝕜] (inner 𝕜 ((g j : F)) p.2 • (g j : F)) :=
          TensorProduct.tmul_sum _ _ _
      _ = ∑ j, (inner 𝕜 ((g j : F)) p.2 • p.1) ⊗ₜ[𝕜] (g j : F) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← TensorProduct.smul_tmul]

/-! ## Operator-norm bounds for `rTensor`, `lTensor`, `map` -/

/-- The right-tensoring bound: `‖(A ⊗ 1) t‖ ≤ ‖A‖ * ‖t‖`, via the orthonormal fiber
representation and Pythagoras. -/
theorem norm_rTensor_apply_le (A : E →L[𝕜] G) (t : E ⊗[𝕜] F) :
    ‖LinearMap.rTensor F (A : E →ₗ[𝕜] G) t‖ ≤ ‖A‖ * ‖t‖ := by
  obtain ⟨n, x, g, hg, rfl⟩ := exists_sum_tmul_orthonormal t
  rw [map_sum]
  simp only [LinearMap.rTensor_tmul, ContinuousLinearMap.coe_coe]
  have key : ‖∑ j, (A (x j)) ⊗ₜ[𝕜] g j‖ ^ 2 ≤ (‖A‖ * ‖∑ j, x j ⊗ₜ[𝕜] g j‖) ^ 2 := by
    rw [norm_sq_sum_tmul_orthonormal _ hg, mul_pow, norm_sq_sum_tmul_orthonormal x hg,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc ‖A (x j)‖ ^ 2 ≤ (‖A‖ * ‖x j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
      _ = ‖A‖ ^ 2 * ‖x j‖ ^ 2 := mul_pow _ _ 2
  have h := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

private theorem comm_lTensor_eq (B : F →ₗ[𝕜] H) (t : E ⊗[𝕜] F) :
    TensorProduct.comm 𝕜 E H (LinearMap.lTensor E B t)
      = LinearMap.rTensor E B (TensorProduct.comm 𝕜 E F t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The left-tensoring bound: `‖(1 ⊗ B) t‖ ≤ ‖B‖ * ‖t‖`, by conjugating the right-tensoring
bound with the braiding isometry. -/
theorem norm_lTensor_apply_le (B : F →L[𝕜] H) (t : E ⊗[𝕜] F) :
    ‖LinearMap.lTensor E (B : F →ₗ[𝕜] H) t‖ ≤ ‖B‖ * ‖t‖ := by
  have h : ‖LinearMap.lTensor E (B : F →ₗ[𝕜] H) t‖
      = ‖LinearMap.rTensor E (B : F →ₗ[𝕜] H) (TensorProduct.comm 𝕜 E F t)‖ := by
    rw [← comm_lTensor_eq, TensorProduct.norm_comm]
  rw [h]
  calc ‖LinearMap.rTensor E (B : F →ₗ[𝕜] H) (TensorProduct.comm 𝕜 E F t)‖
      ≤ ‖B‖ * ‖TensorProduct.comm 𝕜 E F t‖ := norm_rTensor_apply_le B _
    _ = ‖B‖ * ‖t‖ := by rw [TensorProduct.norm_comm]

/-- The tensor product of two continuous linear maps is bounded by the product of the
operator norms: `‖(A ⊗ B) t‖ ≤ ‖A‖ * ‖B‖ * ‖t‖`. -/
theorem norm_map_apply_le (A : E →L[𝕜] G) (B : F →L[𝕜] H) (t : E ⊗[𝕜] F) :
    ‖TensorProduct.map (A : E →ₗ[𝕜] G) (B : F →ₗ[𝕜] H) t‖ ≤ ‖A‖ * ‖B‖ * ‖t‖ := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply]
  calc ‖LinearMap.rTensor H (A : E →ₗ[𝕜] G) (LinearMap.lTensor E (B : F →ₗ[𝕜] H) t)‖
      ≤ ‖A‖ * ‖LinearMap.lTensor E (B : F →ₗ[𝕜] H) t‖ := norm_rTensor_apply_le A _
    _ ≤ ‖A‖ * (‖B‖ * ‖t‖) :=
        mul_le_mul_of_nonneg_left (norm_lTensor_apply_le B t) (norm_nonneg A)
    _ = ‖A‖ * ‖B‖ * ‖t‖ := (mul_assoc _ _ _).symm

/-! ## The continuous linear map `A ⊗ B` and its completion `A ⊗̂ B` -/

/-- `TensorProduct.map` of two continuous linear maps, upgraded to a continuous linear map
between the algebraic tensor products. -/
def mapCLM (A : E →L[𝕜] G) (B : F →L[𝕜] H) :
    (E ⊗[𝕜] F) →L[𝕜] (G ⊗[𝕜] H) :=
  LinearMap.mkContinuous (TensorProduct.map (A : E →ₗ[𝕜] G) (B : F →ₗ[𝕜] H))
    (‖A‖ * ‖B‖) (norm_map_apply_le A B)

@[simp]
theorem mapCLM_apply (A : E →L[𝕜] G) (B : F →L[𝕜] H) (t : E ⊗[𝕜] F) :
    mapCLM A B t = TensorProduct.map (A : E →ₗ[𝕜] G) (B : F →ₗ[𝕜] H) t := rfl

@[simp]
theorem mapCLM_tmul (A : E →L[𝕜] G) (B : F →L[𝕜] H) (x : E) (y : F) :
    mapCLM A B (x ⊗ₜ[𝕜] y) = A x ⊗ₜ[𝕜] B y := by
  rw [mapCLM_apply, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe]

/-- The **cross-norm identity** on the algebraic tensor product: `‖A ⊗ B‖ = ‖A‖ * ‖B‖`.
The `≤` is `norm_map_apply_le`; the `≥` tests against pure tensors. -/
theorem norm_mapCLM (A : E →L[𝕜] G) (B : F →L[𝕜] H) :
    ‖mapCLM A B‖ = ‖A‖ * ‖B‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (by positivity) _) ?_
  rcases eq_or_ne ‖B‖ 0 with hB | hB
  · rw [hB, mul_zero]
    exact norm_nonneg _
  · have hB' : 0 < ‖B‖ := lt_of_le_of_ne (norm_nonneg B) (Ne.symm hB)
    have hA : ‖A‖ ≤ ‖mapCLM A B‖ / ‖B‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hB']
      -- `‖A x‖ * ‖B‖ ≤ ‖mapCLM A B‖ * ‖x‖`, via the 𝕜-rescaled operator `(‖A x‖ : 𝕜) • B`
      have hsmul : ‖((‖A x‖ : 𝕜) • B : F →L[𝕜] H)‖ ≤ ‖mapCLM A B‖ * ‖x‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
        rw [ContinuousLinearMap.smul_apply, norm_smul, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _)]
        calc ‖A x‖ * ‖B y‖ = ‖(A x) ⊗ₜ[𝕜] (B y)‖ := (TensorProduct.norm_tmul _ _).symm
          _ = ‖mapCLM A B (x ⊗ₜ[𝕜] y)‖ := by rw [mapCLM_tmul]
          _ ≤ ‖mapCLM A B‖ * ‖x ⊗ₜ[𝕜] y‖ := (mapCLM A B).le_opNorm _
          _ = ‖mapCLM A B‖ * ‖x‖ * ‖y‖ := by
              rw [TensorProduct.norm_tmul, mul_assoc]
      rwa [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at hsmul
    calc ‖A‖ * ‖B‖ ≤ (‖mapCLM A B‖ / ‖B‖) * ‖B‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg B)
      _ = ‖mapCLM A B‖ := div_mul_cancel₀ _ hB

/-- The **bounded functoriality of the Hilbert tensor product**: `A ⊗̂ B`, the extension of
`TensorProduct.map A B` to the completions. -/
def mapL (A : E →L[𝕜] G) (B : F →L[𝕜] H) :
    (E ⊗̂[𝕜] F) →L[𝕜] (G ⊗̂[𝕜] H) :=
  (mapCLM A B).completion

@[simp]
theorem mapL_tmul (A : E →L[𝕜] G) (B : F →L[𝕜] H) (x : E) (y : F) :
    mapL A B (x ⊗̂ₜ[𝕜] y) = (A x) ⊗̂ₜ[𝕜] (B y) := by
  rw [mapL, tmul_def, ContinuousLinearMap.completion_apply_coe, mapCLM_tmul, tmul_def]

/-- The **cross-norm identity** for the Hilbert tensor product: `‖A ⊗̂ B‖ = ‖A‖ * ‖B‖`. -/
@[simp]
theorem norm_mapL (A : E →L[𝕜] G) (B : F →L[𝕜] H) :
    ‖mapL A B‖ = ‖A‖ * ‖B‖ := by
  rw [mapL, ContinuousLinearMap.norm_completion, norm_mapCLM]

end Spectra.HilbertTensor

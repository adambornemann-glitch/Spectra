/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Tensor.Power

/-!
# Functoriality of the Hilbert tensor power

A linear isometry equivalence `e : H ≃ₗᵢ[𝕜] H'` of one-particle spaces induces a linear
isometry equivalence of `n`-particle spaces, acting slotwise on pure tensors:
`congr e (⨂ₜ x i) = ⨂ₜ e (x i)`. This is the `n`-particle sector of the second-quantization
functor `Γ(U)`, and the input to the Krein–Fock lift of an involution of `H`.

The construction has two stages: Mathlib's `PiTensorProduct.congr` provides the algebraic
linear equivalence `(⨂[𝕜]^n H) ≃ₗ[𝕜] (⨂[𝕜]^n H')`, which the product formula for the
tensor-power inner product promotes to an isometry (`congrIsometry`); this then extends
through the completion via `LinearIsometryEquiv.completionMap`, exactly as `permUnitary`
does in `Spectra/Spaces/Tensor/Power.lean`.

## Main definitions

* `Spectra.HilbertTensorPower.congrIsometry e` — the algebraic tensor-power congruence
  `(⨂[𝕜]^n H) ≃ₗᵢ[𝕜] (⨂[𝕜]^n H')` along `e : H ≃ₗᵢ[𝕜] H'`.
* `Spectra.HilbertTensorPower.congr e` — the Hilbert tensor-power congruence
  `HilbertTensorPower 𝕜 n H ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 n H'`.

## Main results

* `congr_tprod` — `congr e (⨂ₜ x i) = ⨂ₜ e (x i)`.
* `congr_refl`, `congr_trans` (pointwise: `congr_congr`), `congr_symm` — the functor laws:
  `congr` sends identity to identity, composition to composition, inverse to inverse.
* `inner_congr_left` — `⟪congr e x, y⟫ = ⟪x, congr e.symm y⟫` (adjoint = inverse).
* `congr_permUnitary` — slotwise maps commute with the permutation unitaries, so `congr e`
  intertwines the bosonic/fermionic symmetrizers over the two one-particle spaces.
-/

noncomputable section

open scoped TensorProduct
open PiTensorProduct UniformSpace

namespace Spectra.HilbertTensorPower

variable {𝕜 : Type*} {n : ℕ} {H H' H'' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
  [NormedAddCommGroup H''] [InnerProductSpace 𝕜 H'']

/-! ## The algebraic layer -/

/-- `PiTensorProduct.congr` along a linear isometry equivalence of the factors preserves
the tensor-power inner product. -/
theorem inner_congr_congr (e : H ≃ₗᵢ[𝕜] H') (t s : ⨂[𝕜]^n H) :
    inner 𝕜 (PiTensorProduct.congr (fun _ : Fin n => e.toLinearEquiv) t)
        (PiTensorProduct.congr (fun _ : Fin n => e.toLinearEquiv) s)
      = inner 𝕜 t s := by
  refine t.induction_on ?_ ?_
  · intro r x
    refine s.induction_on ?_ ?_
    · intro r' y
      rw [map_smul, map_smul, inner_smul_left, inner_smul_right, inner_smul_left,
        inner_smul_right, PiTensorProduct.congr_tprod, PiTensorProduct.congr_tprod,
        TensorPower.inner_tprod_tprod, TensorPower.inner_tprod_tprod]
      simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.inner_map_map]
    · intro a b ha hb
      rw [map_add, inner_add_right, inner_add_right, ha, hb]
  · intro a b ha hb
    rw [map_add, inner_add_left, inner_add_left, ha, hb]

/-- The algebraic tensor-power congruence along `e : H ≃ₗᵢ[𝕜] H'`: Mathlib's
`PiTensorProduct.congr`, promoted to a linear isometry equivalence by
`inner_congr_congr`. -/
def congrIsometry (e : H ≃ₗᵢ[𝕜] H') : (⨂[𝕜]^n H) ≃ₗᵢ[𝕜] (⨂[𝕜]^n H') :=
  (PiTensorProduct.congr fun _ : Fin n => e.toLinearEquiv).isometryOfInner
    (inner_congr_congr e)

/-- `congrIsometry e` acts as the underlying `PiTensorProduct.congr`. -/
@[simp]
theorem congrIsometry_apply (e : H ≃ₗᵢ[𝕜] H') (t : ⨂[𝕜]^n H) :
    congrIsometry e t = PiTensorProduct.congr (fun _ : Fin n => e.toLinearEquiv) t := rfl

/-- `congrIsometry e` acts slotwise on pure tensors. -/
@[simp]
theorem congrIsometry_tprod (e : H ≃ₗᵢ[𝕜] H') (x : Fin n → H) :
    congrIsometry e (PiTensorProduct.tprod 𝕜 x)
      = PiTensorProduct.tprod 𝕜 fun i => e (x i) := by
  rw [congrIsometry_apply, PiTensorProduct.congr_tprod]
  rfl

/-- Algebraic functor law: `congrIsometry` of the identity is the identity (pointwise). -/
theorem congrIsometry_refl_apply (t : ⨂[𝕜]^n H) :
    congrIsometry (LinearIsometryEquiv.refl 𝕜 H) t = t := by
  refine t.induction_on ?_ ?_
  · intro r x
    simp only [map_smul, congrIsometry_tprod, LinearIsometryEquiv.coe_refl, id_eq]
  · intro a b ha hb
    rw [map_add, ha, hb]

/-- Algebraic functor law: `congrIsometry` sends composition to composition (pointwise). -/
theorem congrIsometry_congrIsometry (e : H ≃ₗᵢ[𝕜] H') (f : H' ≃ₗᵢ[𝕜] H'')
    (t : ⨂[𝕜]^n H) :
    congrIsometry f (congrIsometry e t) = congrIsometry (e.trans f) t := by
  refine t.induction_on ?_ ?_
  · intro r x
    simp only [map_smul, congrIsometry_tprod, LinearIsometryEquiv.trans_apply]
  · intro a b ha hb
    simp only [map_add, ha, hb]

/-! ## The completed congruence -/

/-- **Functoriality of the Hilbert tensor power**: a linear isometry equivalence
`e : H ≃ₗᵢ[𝕜] H'` of one-particle spaces induces a linear isometry equivalence of
`n`-particle spaces, acting slotwise on pure tensors. The `n`-particle sector of the
second-quantization functor `Γ`. -/
def congr (e : H ≃ₗᵢ[𝕜] H') :
    HilbertTensorPower 𝕜 n H ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 n H' :=
  (congrIsometry e).completionMap

/-- `congr e` restricted to the dense algebraic power is `congrIsometry e`. -/
theorem congr_coe (e : H ≃ₗᵢ[𝕜] H') (t : ⨂[𝕜]^n H) :
    congr e (t : HilbertTensorPower 𝕜 n H)
      = (congrIsometry e t : HilbertTensorPower 𝕜 n H') :=
  LinearIsometryEquiv.completionMap_coe _ t

/-- `congr e` acts slotwise on pure tensors: `congr e (⨂ₜ x i) = ⨂ₜ e (x i)`. -/
@[simp]
theorem congr_tprod (e : H ≃ₗᵢ[𝕜] H') (x : Fin n → H) :
    congr e (tprod 𝕜 x) = tprod 𝕜 fun i => e (x i) := by
  rw [tprod_def, congr_coe, congrIsometry_tprod, tprod_def]

/-- Two linear isometry equivalences of Hilbert tensor powers agree as soon as they agree
on the (dense) image of the algebraic tensor power. -/
theorem ext_of_coe {f g : HilbertTensorPower 𝕜 n H ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 n H'}
    (h : ∀ t : ⨂[𝕜]^n H,
      f (t : HilbertTensorPower 𝕜 n H) = g (t : HilbertTensorPower 𝕜 n H)) :
    f = g :=
  LinearIsometryEquiv.ext fun x =>
    Completion.induction_on x (isClosed_eq f.continuous g.continuous) h

/-! ## Functor laws -/

/-- Functor law (pointwise composition): `congr f (congr e x) = congr (e.trans f) x`. -/
theorem congr_congr (e : H ≃ₗᵢ[𝕜] H') (f : H' ≃ₗᵢ[𝕜] H'')
    (x : HilbertTensorPower 𝕜 n H) :
    congr f (congr e x) = congr (e.trans f) x := by
  refine Completion.induction_on x ?_ fun t => ?_
  · exact isClosed_eq ((congr f).continuous.comp (congr e).continuous)
      (congr (e.trans f)).continuous
  · rw [congr_coe, congr_coe, congr_coe, congrIsometry_congrIsometry]

/-- Functor law (bundled composition): `(congr e).trans (congr f) = congr (e.trans f)`. -/
theorem congr_trans (e : H ≃ₗᵢ[𝕜] H') (f : H' ≃ₗᵢ[𝕜] H'') :
    ((congr e).trans (congr f) :
        HilbertTensorPower 𝕜 n H ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 n H'')
      = congr (e.trans f) := by
  refine LinearIsometryEquiv.ext fun x => ?_
  rw [LinearIsometryEquiv.trans_apply, congr_congr]

/-- Functor law (identity): `congr` of the identity is the identity. -/
theorem congr_refl :
    congr (LinearIsometryEquiv.refl 𝕜 H)
      = LinearIsometryEquiv.refl 𝕜 (HilbertTensorPower 𝕜 n H) := by
  refine ext_of_coe fun t => ?_
  rw [congr_coe, congrIsometry_refl_apply]
  rfl

/-- Functor law (inverse): `(congr e).symm = congr e.symm`. -/
theorem congr_symm (e : H ≃ₗᵢ[𝕜] H') :
    ((congr e).symm : HilbertTensorPower 𝕜 n H' ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 n H)
      = congr e.symm := by
  refine LinearIsometryEquiv.ext fun y => ?_
  refine (congr e).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, congr_congr,
    LinearIsometryEquiv.symm_trans_self, congr_refl]
  rfl

/-- The inverse congruence acts slotwise by `e.symm` on pure tensors. -/
theorem congr_symm_tprod (e : H ≃ₗᵢ[𝕜] H') (y : Fin n → H') :
    (congr e).symm (tprod 𝕜 y) = tprod 𝕜 fun i => e.symm (y i) := by
  rw [congr_symm, congr_tprod]

/-- Moving `congr e` across the inner product inverts it:
`⟪congr e x, y⟫ = ⟪x, congr e.symm y⟫`. -/
theorem inner_congr_left (e : H ≃ₗᵢ[𝕜] H') (x : HilbertTensorPower 𝕜 n H)
    (y : HilbertTensorPower 𝕜 n H') :
    inner 𝕜 (congr e x) y = inner 𝕜 x (congr e.symm y) := by
  rw [LinearIsometryEquiv.inner_map_eq_flip, congr_symm]

/-! ## Compatibility with the permutation action -/

/-- Algebraic layer: slotwise maps commute with the permutation action on the algebraic
tensor power. -/
theorem congrIsometry_permIsometry (e : H ≃ₗᵢ[𝕜] H') (σ : Equiv.Perm (Fin n))
    (t : ⨂[𝕜]^n H) :
    congrIsometry e (permIsometry 𝕜 H σ t) = permIsometry 𝕜 H' σ (congrIsometry e t) := by
  refine t.induction_on ?_ ?_
  · intro r x
    simp only [map_smul, permIsometry_tprod, congrIsometry_tprod]
  · intro a b ha hb
    simp only [map_add, ha, hb]

/-- Slotwise maps commute with the permutation unitaries:
`congr e (U_σ ξ) = U_σ (congr e ξ)`. Consequently `congr e` intertwines the bosonic and
fermionic symmetrizers over the two one-particle spaces. -/
theorem congr_permUnitary (e : H ≃ₗᵢ[𝕜] H') (σ : Equiv.Perm (Fin n))
    (ξ : HilbertTensorPower 𝕜 n H) :
    congr e (permUnitary 𝕜 H σ ξ) = permUnitary 𝕜 H' σ (congr e ξ) := by
  refine Completion.induction_on ξ ?_ fun t => ?_
  · exact isClosed_eq ((congr e).continuous.comp (permUnitary 𝕜 H σ).continuous)
      ((permUnitary 𝕜 H' σ).continuous.comp (congr e).continuous)
  · simp only [permUnitary, LinearIsometryEquiv.completionMap_coe, congr_coe]
    rw [congrIsometry_permIsometry]

end Spectra.HilbertTensorPower

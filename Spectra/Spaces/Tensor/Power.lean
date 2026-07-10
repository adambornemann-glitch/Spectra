/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Tensor.PowerInner

/-!
# The Hilbert tensor power `HilbertTensorPower 𝕜 n H`

The completion of the algebraic tensor power `⨂[𝕜]^n H` in its inner-product norm
(`Spectra/Spaces/Tensor/PowerInner.lean`): the `n`-fold Hilbert tensor power, the space of
`n`-particle states over the one-particle space `H`. As with the binary `E ⊗̂[𝕜] F`, the
Hilbert-space structure is pure instance inheritance through `UniformSpace.Completion`.

## Main definitions

* `Spectra.HilbertTensorPower 𝕜 n H` — the completed `n`-fold tensor power.
* `Spectra.HilbertTensorPower.tprod` — the pure tensor `⨂ₜ x i` in the completion.
* `Spectra.HilbertTensorPower.permUnitary σ` — the unitary permutation action of
  `σ : Equiv.Perm (Fin n)`, extending `PiTensorProduct.reindex` through the completion.
  This is the raw material for the bosonic/fermionic symmetrizers.

## Main results

* `inner_tprod_tprod` / `norm_tprod` — `⟪⨂ₜ x, ⨂ₜ y⟫ = ∏ ⟪x i, y i⟫`, `‖⨂ₜ x‖ = ∏ ‖x i‖`.
* `dense_span_tprod` — pure tensors span densely.
* `permUnitary_tprod` — `σ` acts on pure tensors by permuting the factors.
-/

noncomputable section

open scoped TensorProduct
open PiTensorProduct UniformSpace

namespace Spectra

variable (𝕜 : Type*) (n : ℕ) (H : Type*) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The **Hilbert tensor power**: the completion of the algebraic `n`-fold tensor power
`⨂[𝕜]^n H` in the inner-product (cross) norm. The `n`-particle space over `H`. -/
abbrev HilbertTensorPower := Completion (⨂[𝕜]^n H)

-- Sanity: the Hilbert-space structure is found by instance resolution alone.
example : NormedAddCommGroup (HilbertTensorPower 𝕜 n H) := inferInstance
example : InnerProductSpace 𝕜 (HilbertTensorPower 𝕜 n H) := inferInstance
example : CompleteSpace (HilbertTensorPower 𝕜 n H) := inferInstance

namespace HilbertTensorPower

variable {n H}

/-- The pure tensor `⨂ₜ x i` in the Hilbert tensor power. -/
def tprod (x : Fin n → H) : HilbertTensorPower 𝕜 n H :=
  ((PiTensorProduct.tprod 𝕜 x : ⨂[𝕜]^n H) : HilbertTensorPower 𝕜 n H)

variable {𝕜}

theorem tprod_def (x : Fin n → H) :
    tprod 𝕜 x = ((PiTensorProduct.tprod 𝕜 x : ⨂[𝕜]^n H) : HilbertTensorPower 𝕜 n H) := rfl

/-- The inner product of pure tensors factorizes over the slots. -/
@[simp]
theorem inner_tprod_tprod (x y : Fin n → H) :
    inner 𝕜 (tprod 𝕜 x) (tprod 𝕜 y) = ∏ i, inner 𝕜 (x i) (y i) := by
  rw [tprod_def, tprod_def, Completion.inner_coe, TensorPower.inner_tprod_tprod]

/-- The cross norm on pure tensors: `‖⨂ₜ x i‖ = ∏ i, ‖x i‖`. -/
@[simp]
theorem norm_tprod (x : Fin n → H) : ‖tprod 𝕜 x‖ = ∏ i, ‖x i‖ := by
  rw [tprod_def, Completion.norm_coe, TensorPower.norm_tprod]

theorem denseRange_coe :
    DenseRange ((↑) : (⨂[𝕜]^n H) → HilbertTensorPower 𝕜 n H) :=
  Completion.denseRange_coe

theorem coe_mem_span_tprod (t : ⨂[𝕜]^n H) :
    (t : HilbertTensorPower 𝕜 n H) ∈
      Submodule.span 𝕜 (Set.range fun x : Fin n → H => tprod 𝕜 x) := by
  refine t.induction_on ?_ ?_
  · intro r x
    rw [Completion.coe_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨x, rfl⟩)
  · intro t₁ t₂ h₁ h₂
    rw [Completion.coe_add]
    exact Submodule.add_mem _ h₁ h₂

/-- Pure tensors span a dense subspace of the Hilbert tensor power. -/
theorem dense_span_tprod :
    Dense (Submodule.span 𝕜 (Set.range fun x : Fin n → H => tprod 𝕜 x) :
      Set (HilbertTensorPower 𝕜 n H)) :=
  Completion.denseRange_coe.mono (Set.range_subset_iff.mpr coe_mem_span_tprod)

/-! ## The permutation action -/

/-- The permutation action preserves the inner product (on the algebraic power). -/
theorem inner_reindex_reindex (σ : Equiv.Perm (Fin n)) (t s : ⨂[𝕜]^n H) :
    inner 𝕜 (reindex 𝕜 (fun _ => H) σ t) (reindex 𝕜 (fun _ => H) σ s) = inner 𝕜 t s := by
  refine t.induction_on ?_ ?_
  · intro r x
    refine s.induction_on ?_ ?_
    · intro r' y
      rw [map_smul, map_smul, inner_smul_left, inner_smul_right, inner_smul_left,
        inner_smul_right, reindex_tprod, reindex_tprod, TensorPower.inner_tprod_tprod,
        TensorPower.inner_tprod_tprod,
        Equiv.prod_comp σ.symm fun i => inner 𝕜 (x i) (y i)]
    · intro a b ha hb
      rw [map_add, inner_add_right, inner_add_right, ha, hb]
  · intro a b ha hb
    rw [map_add, inner_add_left, inner_add_left, ha, hb]

variable (𝕜 H) in
/-- The permutation action of `σ : Equiv.Perm (Fin n)` on the algebraic tensor power, as a
linear isometry equivalence. -/
def permIsometry (σ : Equiv.Perm (Fin n)) : (⨂[𝕜]^n H) ≃ₗᵢ[𝕜] (⨂[𝕜]^n H) :=
  (reindex 𝕜 (fun _ => H) σ).isometryOfInner (inner_reindex_reindex σ)

@[simp]
theorem permIsometry_apply (σ : Equiv.Perm (Fin n)) (t : ⨂[𝕜]^n H) :
    permIsometry 𝕜 H σ t = reindex 𝕜 (fun _ => H) σ t := rfl

theorem permIsometry_tprod (σ : Equiv.Perm (Fin n)) (x : Fin n → H) :
    permIsometry 𝕜 H σ (PiTensorProduct.tprod 𝕜 x)
      = PiTensorProduct.tprod 𝕜 fun i => x (σ.symm i) := by
  rw [permIsometry_apply, reindex_tprod]

variable (𝕜 H) in
/-- The **permutation unitary**: the action of `σ : Equiv.Perm (Fin n)` on the Hilbert
tensor power, permuting the factors of pure tensors. The raw material for the bosonic and
fermionic symmetrizers. -/
def permUnitary (σ : Equiv.Perm (Fin n)) :
    HilbertTensorPower 𝕜 n H ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 n H :=
  (permIsometry 𝕜 H σ).completionMap

@[simp]
theorem permUnitary_tprod (σ : Equiv.Perm (Fin n)) (x : Fin n → H) :
    permUnitary 𝕜 H σ (tprod 𝕜 x) = tprod 𝕜 fun i => x (σ.symm i) := by
  rw [permUnitary, tprod_def, LinearIsometryEquiv.completionMap_coe, permIsometry_tprod,
    tprod_def]

end HilbertTensorPower

end Spectra

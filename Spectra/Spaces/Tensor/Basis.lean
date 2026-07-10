/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Tensor.Hilbert
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The tensor Hilbert basis of `E ⊗̂[𝕜] F`

Hilbert bases of the factors tensor to a Hilbert basis of the Hilbert tensor product:
given `b : HilbertBasis ι 𝕜 E` and `c : HilbertBasis κ 𝕜 F`, the family
`(i, j) ↦ b i ⊗̂ₜ c j` is a Hilbert basis of `E ⊗̂[𝕜] F` indexed by `ι × κ`. This extends
Mathlib's finite-dimensional `OrthonormalBasis.tensorProduct` through the completion, and
is the workhorse for coordinate computations on the Hilbert tensor product (partial traces,
Fock sector expansions).

## Main definitions

* `Spectra.HilbertTensor.tensorHilbertBasis` — the tensor Hilbert basis
  `HilbertBasis (ι × κ) 𝕜 (E ⊗̂[𝕜] F)`.

## Main results

* `Spectra.HilbertTensor.orthonormal_tmul` — pure tensors of orthonormal families are
  orthonormal.
* `Spectra.HilbertTensor.dense_span_tensor` — pure tensors of basis vectors span densely.
  The proof runs a closed-comap argument once per factor: for a continuous linear map `T`
  into the closed span `M`, the submodule `T ⁻¹' M` is closed, so if it contains the range
  of a Hilbert basis it is everything.
* `Spectra.HilbertTensor.tensorHilbertBasis_apply` — `tensorHilbertBasis b c (i, j) = b i ⊗̂ₜ c j`.
-/

noncomputable section

open scoped TensorProduct
open UniformSpace

namespace Spectra.HilbertTensor

variable {𝕜 E F : Type*} {ι κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Pure tensors of orthonormal families are orthonormal in the Hilbert tensor product. -/
theorem orthonormal_tmul {v : ι → E} {w : κ → F}
    (hv : Orthonormal 𝕜 v) (hw : Orthonormal 𝕜 w) :
    Orthonormal 𝕜 fun p : ι × κ => v p.1 ⊗̂ₜ[𝕜] w p.2 := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, j⟩ ⟨k, l⟩
  rw [inner_tmul_tmul, orthonormal_iff_ite.mp hv, orthonormal_iff_ite.mp hw]
  by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2, Prod.ext_iff]

/-- Pure tensors of Hilbert-basis vectors span a dense subspace of the Hilbert tensor
product. -/
theorem dense_span_tensor (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    (Submodule.span 𝕜
      (Set.range fun p : ι × κ => b p.1 ⊗̂ₜ[𝕜] c p.2)).topologicalClosure = ⊤ := by
  set M := (Submodule.span 𝕜
    (Set.range fun p : ι × κ => b p.1 ⊗̂ₜ[𝕜] c p.2)).topologicalClosure with _hM
  have hMclosed : IsClosed (M : Set (E ⊗̂[𝕜] F)) :=
    Submodule.isClosed_topologicalClosure _
  -- Stage A: `b i ⊗̂ₜ y ∈ M` for every basis vector `b i` and every `y : F`.
  have hA : ∀ (i : ι) (y : F), b i ⊗̂ₜ[𝕜] y ∈ M := by
    intro i y
    have hspan : Submodule.span 𝕜 (Set.range c)
        ≤ M.comap (tmulL 𝕜 E F (b i)).toLinearMap := by
      rw [Submodule.span_le]
      rintro - ⟨j, rfl⟩
      exact Submodule.mem_comap.mpr
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i, j), rfl⟩))
    have hclosed : IsClosed
        ((M.comap (tmulL 𝕜 E F (b i)).toLinearMap : Submodule 𝕜 F) : Set F) :=
      hMclosed.preimage (tmulL 𝕜 E F (b i)).continuous
    have htop : (⊤ : Submodule 𝕜 F) ≤ M.comap (tmulL 𝕜 E F (b i)).toLinearMap := by
      rw [← c.dense_span]
      exact Submodule.topologicalClosure_minimal _ hspan hclosed
    exact Submodule.mem_comap.mp (htop Submodule.mem_top)
  -- Stage B: `x ⊗̂ₜ y ∈ M` for all `x`, `y`, by the same argument in the first factor.
  have hB : ∀ (x : E) (y : F), x ⊗̂ₜ[𝕜] y ∈ M := by
    intro x y
    have hspan : Submodule.span 𝕜 (Set.range b)
        ≤ M.comap ((tmulL 𝕜 E F).flip y).toLinearMap := by
      rw [Submodule.span_le]
      rintro - ⟨i, rfl⟩
      exact Submodule.mem_comap.mpr (hA i y)
    have hclosed : IsClosed
        ((M.comap ((tmulL 𝕜 E F).flip y).toLinearMap : Submodule 𝕜 E) : Set E) :=
      hMclosed.preimage ((tmulL 𝕜 E F).flip y).continuous
    have htop : (⊤ : Submodule 𝕜 E) ≤ M.comap ((tmulL 𝕜 E F).flip y).toLinearMap := by
      rw [← b.dense_span]
      exact Submodule.topologicalClosure_minimal _ hspan hclosed
    exact Submodule.mem_comap.mp (htop Submodule.mem_top)
  -- Conclude: `M` is closed and contains all pure tensors, whose span is dense.
  rw [eq_top_iff, ← span_tmul_topologicalClosure]
  refine Submodule.topologicalClosure_minimal _ ?_ hMclosed
  rw [Submodule.span_le]
  rintro - ⟨⟨x, y⟩, rfl⟩
  exact hB x y

/-- **The tensor Hilbert basis**: Hilbert bases of the factors tensor to a Hilbert basis of
the Hilbert tensor product, indexed by the product of the index types. -/
def tensorHilbertBasis (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    HilbertBasis (ι × κ) 𝕜 (E ⊗̂[𝕜] F) :=
  HilbertBasis.mk (orthonormal_tmul b.orthonormal c.orthonormal)
    (dense_span_tensor b c).ge

@[simp]
theorem tensorHilbertBasis_apply (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (p : ι × κ) :
    tensorHilbertBasis b c p = b p.1 ⊗̂ₜ[𝕜] c p.2 :=
  congrFun (HilbertBasis.coe_mk _ _) p

theorem tensorHilbertBasis_apply' (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (i : ι) (j : κ) :
    tensorHilbertBasis b c (i, j) = b i ⊗̂ₜ[𝕜] c j :=
  tensorHilbertBasis_apply b c (i, j)

end Spectra.HilbertTensor

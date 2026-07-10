/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# The Hilbert tensor product `E ⊗̂[𝕜] F`

Mathlib equips the *algebraic* tensor product `E ⊗[𝕜] F` of two inner product spaces with
the inner product `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫` (`TensorProduct.instInnerProductSpace`)
but stops short of completing it — the completed tensor product is an explicit TODO there.
This file assembles the completion: the **Hilbert tensor product**, the tensor product in the
category of Hilbert spaces.

## Main definitions

* `Spectra.HilbertTensor 𝕜 E F` (scoped notation `E ⊗̂[𝕜] F`) — the uniform completion of
  `E ⊗[𝕜] F`; a complete inner product space by inheritance
  (`UniformSpace.Completion.innerProductSpace`).
* `Spectra.HilbertTensor.tmul` (scoped notation `x ⊗̂ₜ[𝕜] y`) — the pure tensor, the image
  of `x ⊗ₜ[𝕜] y` under the (dense, isometric) coercion.
* `Spectra.HilbertTensor.tmulL` — the pure tensor bundled as a continuous bilinear map.
* `LinearIsometry.completionMap` / `LinearIsometryEquiv.completionMap` — functoriality of
  `UniformSpace.Completion` for linear (equi-)isometries (general-purpose; upstream
  candidates alongside `ContinuousLinearMap.completion`).
* `Spectra.HilbertTensor.map`, `congr`, `comm`, `lid`, `assoc` — isometric functoriality
  of `⊗̂`, extended from Mathlib's algebraic isometries through the completion.

## Main results

* `Spectra.HilbertTensor.inner_tmul_tmul` — `⟪x ⊗̂ₜ y, x' ⊗̂ₜ y'⟫ = ⟪x, x'⟫ * ⟪y, y'⟫`.
* `Spectra.HilbertTensor.norm_tmul` — `‖x ⊗̂ₜ y‖ = ‖x‖ * ‖y‖` (the Hilbert cross norm).
* `Spectra.HilbertTensor.dense_span_tmul` — pure tensors span a dense subspace, the
  workhorse for extending densely-defined constructions off pure tensors.

## Notes

`assoc` reassociates the *algebraic-level* completions
`(E ⊗[𝕜] F) ⊗̂[𝕜] G ≃ₗᵢ E ⊗̂[𝕜] (F ⊗[𝕜] G)`. The fully-completed reassociation
`(E ⊗̂ F) ⊗̂ G ≃ E ⊗̂ (F ⊗̂ G)` needs a dense-embedding bridge
(`Completion (A ⊗ B) ≃ Completion (A' ⊗ B)` for `A` dense in `A'`) and is deferred to the
tensor-power layer (Fock Spaces M1).

Bounded functoriality `A ⊗̂ B` for `A`, `B` continuous linear maps (with the cross-norm
identity `‖A ⊗̂ B‖ = ‖A‖ * ‖B‖`) and the tensor `HilbertBasis` land in follow-up files of
`Spectra/Spaces/Tensor/`.
-/

noncomputable section

open scoped TensorProduct
open UniformSpace

/-! ## Completion functoriality for linear isometries

General-purpose: `UniformSpace.Completion` is functorial for linear isometries and
linear isometry equivalences. Mathlib has `ContinuousLinearMap.completion`; these are the
isometric refinements. Upstream candidates. -/

section CompletionFunctorial

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace LinearIsometry

/-- A linear isometry between normed spaces extends to a linear isometry between their
completions. Functoriality of `UniformSpace.Completion` for linear isometries. -/
noncomputable def completionMap (f : E →ₗᵢ[𝕜] F) :
    Completion E →ₗᵢ[𝕜] Completion F where
  toLinearMap := (f.toContinuousLinearMap.completion :
    Completion E →L[𝕜] Completion F).toLinearMap
  norm_map' x := by
    refine Completion.induction_on x
      (isClosed_eq (continuous_norm.comp f.toContinuousLinearMap.completion.continuous)
        continuous_norm) fun a => ?_
    change ‖f.toContinuousLinearMap.completion (a : Completion E)‖ = ‖(a : Completion E)‖
    rw [ContinuousLinearMap.completion_apply_coe, Completion.norm_coe, Completion.norm_coe]
    exact f.norm_map a

@[simp]
theorem completionMap_coe (f : E →ₗᵢ[𝕜] F) (a : E) :
    f.completionMap (a : Completion E) = (f a : Completion F) :=
  ContinuousLinearMap.completion_apply_coe _ _

end LinearIsometry

namespace LinearIsometryEquiv

/-- A linear isometry equivalence between normed spaces extends to a linear isometry
equivalence between their completions. Functoriality of `UniformSpace.Completion` for
linear isometry equivalences. -/
noncomputable def completionMap (f : E ≃ₗᵢ[𝕜] F) :
    Completion E ≃ₗᵢ[𝕜] Completion F :=
  LinearIsometryEquiv.ofSurjective f.toLinearIsometry.completionMap <| by
    have hsub : Set.range ((↑) : F → Completion F) ⊆
        Set.range f.toLinearIsometry.completionMap := by
      rintro - ⟨b, rfl⟩
      exact ⟨(f.symm b : Completion E), by simp⟩
    have hdense : Dense (Set.range f.toLinearIsometry.completionMap) :=
      Completion.denseRange_coe.mono hsub
    have hclosed : IsClosed (Set.range f.toLinearIsometry.completionMap) :=
      f.toLinearIsometry.completionMap.isometry.isClosedEmbedding.isClosed_range
    rw [← Set.range_eq_univ, ← hclosed.closure_eq]
    exact hdense.closure_eq

@[simp]
theorem completionMap_coe (f : E ≃ₗᵢ[𝕜] F) (a : E) :
    f.completionMap (a : Completion E) = (f a : Completion F) :=
  f.toLinearIsometry.completionMap_coe a

end LinearIsometryEquiv

end CompletionFunctorial

/-! ## The Hilbert tensor product -/

namespace Spectra

variable (𝕜 E F G H : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The **Hilbert tensor product** of two inner product spaces: the uniform completion of
the algebraic tensor product `E ⊗[𝕜] F` in the Hilbert cross norm
(`⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`).

It is a complete inner product space — a Hilbert space — by inheritance:
`UniformSpace.Completion.innerProductSpace` supplies the inner product extending the
algebraic one, and completions are complete. -/
abbrev HilbertTensor := Completion (E ⊗[𝕜] F)

@[inherit_doc]
scoped notation:100 E " ⊗̂[" 𝕜 "] " F:100 => HilbertTensor 𝕜 E F

-- Sanity: the Hilbert-space structure is found by instance resolution alone.
example : NormedAddCommGroup (E ⊗̂[𝕜] F) := inferInstance
example : InnerProductSpace 𝕜 (E ⊗̂[𝕜] F) := inferInstance
example : CompleteSpace (E ⊗̂[𝕜] F) := inferInstance

namespace HilbertTensor

variable {𝕜 E F G H}

/-- The pure tensor in the Hilbert tensor product: the image of the algebraic pure tensor
`x ⊗ₜ[𝕜] y` under the isometric dense coercion into the completion. -/
def tmul (x : E) (y : F) : E ⊗̂[𝕜] F := ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : E ⊗̂[𝕜] F)

@[inherit_doc]
scoped notation:100 x " ⊗̂ₜ[" 𝕜 "] " y:100 => HilbertTensor.tmul (𝕜 := 𝕜) x y

theorem tmul_def (x : E) (y : F) :
    x ⊗̂ₜ[𝕜] y = ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : E ⊗̂[𝕜] F) := rfl

/-- The inner product of pure tensors factorizes:
`⟪x ⊗̂ₜ y, x' ⊗̂ₜ y'⟫ = ⟪x, x'⟫ * ⟪y, y'⟫`. -/
@[simp]
theorem inner_tmul_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x ⊗̂ₜ[𝕜] y) (x' ⊗̂ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := by
  rw [tmul_def, tmul_def, Completion.inner_coe, TensorProduct.inner_tmul]

/-- The Hilbert cross norm on pure tensors: `‖x ⊗̂ₜ y‖ = ‖x‖ * ‖y‖`. -/
@[simp]
theorem norm_tmul (x : E) (y : F) : ‖x ⊗̂ₜ[𝕜] y‖ = ‖x‖ * ‖y‖ := by
  rw [tmul_def, Completion.norm_coe, TensorProduct.norm_tmul]

/-! ### Bilinearity of the pure tensor -/

theorem add_tmul (x x' : E) (y : F) :
    (x + x') ⊗̂ₜ[𝕜] y = x ⊗̂ₜ[𝕜] y + x' ⊗̂ₜ[𝕜] y := by
  rw [tmul_def, TensorProduct.add_tmul, Completion.coe_add, tmul_def, tmul_def]

theorem tmul_add (x : E) (y y' : F) :
    x ⊗̂ₜ[𝕜] (y + y') = x ⊗̂ₜ[𝕜] y + x ⊗̂ₜ[𝕜] y' := by
  rw [tmul_def, TensorProduct.tmul_add, Completion.coe_add, tmul_def, tmul_def]

theorem smul_tmul (c : 𝕜) (x : E) (y : F) :
    (c • x) ⊗̂ₜ[𝕜] y = c • (x ⊗̂ₜ[𝕜] y) := by
  rw [tmul_def, ← TensorProduct.smul_tmul', Completion.coe_smul, tmul_def]

theorem tmul_smul (c : 𝕜) (x : E) (y : F) :
    x ⊗̂ₜ[𝕜] (c • y) = c • (x ⊗̂ₜ[𝕜] y) := by
  rw [tmul_def, TensorProduct.tmul_smul, Completion.coe_smul, tmul_def]

@[simp]
theorem zero_tmul (y : F) : (0 : E) ⊗̂ₜ[𝕜] y = 0 := by
  rw [tmul_def, TensorProduct.zero_tmul, Completion.coe_zero]

@[simp]
theorem tmul_zero (x : E) : x ⊗̂ₜ[𝕜] (0 : F) = 0 := by
  rw [tmul_def, TensorProduct.tmul_zero, Completion.coe_zero]

/-! ### The pure tensor as a continuous bilinear map -/

variable (𝕜 E F) in
/-- The pure tensor `(x, y) ↦ x ⊗̂ₜ y` bundled as a bilinear map. -/
def tmulₗ : E →ₗ[𝕜] F →ₗ[𝕜] E ⊗̂[𝕜] F :=
  LinearMap.mk₂ 𝕜 tmul add_tmul smul_tmul tmul_add tmul_smul

variable (𝕜 E F) in
/-- The pure tensor `(x, y) ↦ x ⊗̂ₜ y` bundled as a continuous bilinear map; its norm bound
is the cross-norm identity `‖x ⊗̂ₜ y‖ = ‖x‖ * ‖y‖`. -/
def tmulL : E →L[𝕜] F →L[𝕜] E ⊗̂[𝕜] F :=
  LinearMap.mkContinuous₂ (tmulₗ 𝕜 E F) 1 fun x y => by
    simp [tmulₗ]

@[simp]
theorem tmulL_apply (x : E) (y : F) : tmulL 𝕜 E F x y = x ⊗̂ₜ[𝕜] y := rfl

/-! ### Density of pure tensors -/

theorem denseRange_coe :
    DenseRange ((↑) : E ⊗[𝕜] F → E ⊗̂[𝕜] F) :=
  Completion.denseRange_coe

theorem coe_mem_span_tmul (t : E ⊗[𝕜] F) :
    (t : E ⊗̂[𝕜] F) ∈
      Submodule.span 𝕜 (Set.range fun p : E × F => p.1 ⊗̂ₜ[𝕜] p.2) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [Completion.coe_zero]
    exact Submodule.zero_mem _
  | tmul x y => exact Submodule.subset_span ⟨(x, y), rfl⟩
  | add s t hs ht =>
    rw [Completion.coe_add]
    exact Submodule.add_mem _ hs ht

/-- Pure tensors span a dense subspace of the Hilbert tensor product. This is the workhorse
lemma: constructions on `E ⊗̂[𝕜] F` are determined by their values on pure tensors. -/
theorem dense_span_tmul :
    Dense (Submodule.span 𝕜 (Set.range fun p : E × F => p.1 ⊗̂ₜ[𝕜] p.2) :
      Set (E ⊗̂[𝕜] F)) :=
  Completion.denseRange_coe.mono (Set.range_subset_iff.mpr coe_mem_span_tmul)

/-- The span of pure tensors has full topological closure. -/
theorem span_tmul_topologicalClosure :
    (Submodule.span 𝕜 (Set.range fun p : E × F => p.1 ⊗̂ₜ[𝕜] p.2)).topologicalClosure =
      (⊤ : Submodule 𝕜 (E ⊗̂[𝕜] F)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp dense_span_tmul

/-! ### Isometric functoriality -/

/-- The Hilbert tensor product of two linear isometries: the completion of
`TensorProduct.mapIsometry`. -/
def map (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) :
    (E ⊗̂[𝕜] F) →ₗᵢ[𝕜] (G ⊗̂[𝕜] H) :=
  (TensorProduct.mapIsometry f g).completionMap

@[simp]
theorem map_tmul (f : E →ₗᵢ[𝕜] G) (g : F →ₗᵢ[𝕜] H) (x : E) (y : F) :
    map f g (x ⊗̂ₜ[𝕜] y) = f x ⊗̂ₜ[𝕜] g y := by
  rw [map, tmul_def, LinearIsometry.completionMap_coe, TensorProduct.mapIsometry_apply,
    TensorProduct.map_tmul, tmul_def]
  rfl

/-- The Hilbert tensor product of two linear isometry equivalences: the completion of
`TensorProduct.congrIsometry`. -/
def congr (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (E ⊗̂[𝕜] F) ≃ₗᵢ[𝕜] (G ⊗̂[𝕜] H) :=
  (TensorProduct.congrIsometry f g).completionMap

@[simp]
theorem congr_tmul (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E) (y : F) :
    congr f g (x ⊗̂ₜ[𝕜] y) = f x ⊗̂ₜ[𝕜] g y := by
  rw [congr, tmul_def, LinearIsometryEquiv.completionMap_coe,
    TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul, tmul_def]
  rfl

variable (𝕜 E F) in
/-- The braiding of the Hilbert tensor product: `E ⊗̂ F ≃ₗᵢ F ⊗̂ E`. -/
def comm : (E ⊗̂[𝕜] F) ≃ₗᵢ[𝕜] (F ⊗̂[𝕜] E) :=
  (TensorProduct.commIsometry 𝕜 E F).completionMap

@[simp]
theorem comm_tmul (x : E) (y : F) :
    comm 𝕜 E F (x ⊗̂ₜ[𝕜] y) = y ⊗̂ₜ[𝕜] x := by
  rw [comm, tmul_def, LinearIsometryEquiv.completionMap_coe,
    TensorProduct.commIsometry_apply, TensorProduct.comm_tmul, tmul_def]

variable (𝕜 E) in
/-- The left unitor of the Hilbert tensor product: `𝕜 ⊗̂ E ≃ₗᵢ Completion E`. When `E` is
already complete, compose with `UniformSpace.Completion.linearIsometryEquiv`-style
identifications downstream. -/
def lid : (𝕜 ⊗̂[𝕜] E) ≃ₗᵢ[𝕜] Completion E :=
  (TensorProduct.lidIsometry 𝕜 E).completionMap

@[simp]
theorem lid_tmul (c : 𝕜) (x : E) :
    lid 𝕜 E (c ⊗̂ₜ[𝕜] x) = ((c • x : E) : Completion E) := by
  rw [lid, tmul_def, LinearIsometryEquiv.completionMap_coe,
    TensorProduct.lidIsometry_apply, TensorProduct.lid_tmul]

variable (𝕜 E F G) in
/-- Reassociation at the algebraic level of the factors:
`(E ⊗[𝕜] F) ⊗̂[𝕜] G ≃ₗᵢ E ⊗̂[𝕜] (F ⊗[𝕜] G)`.

The fully-completed reassociation `(E ⊗̂ F) ⊗̂ G ≃ E ⊗̂ (F ⊗̂ G)` requires a
dense-embedding bridge and is deferred to the tensor-power layer. -/
def assoc : ((E ⊗[𝕜] F) ⊗̂[𝕜] G) ≃ₗᵢ[𝕜] (E ⊗̂[𝕜] (F ⊗[𝕜] G)) :=
  (TensorProduct.assocIsometry 𝕜 E F G).completionMap

@[simp]
theorem assoc_tmul (x : E) (y : F) (z : G) :
    assoc 𝕜 E F G ((x ⊗ₜ[𝕜] y) ⊗̂ₜ[𝕜] z) = x ⊗̂ₜ[𝕜] (y ⊗ₜ[𝕜] z) := by
  rw [assoc, tmul_def, LinearIsometryEquiv.completionMap_coe,
    TensorProduct.assocIsometry_apply, TensorProduct.assoc_tmul, tmul_def]

end HilbertTensor

end Spectra

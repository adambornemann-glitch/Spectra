/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The bounded polar decomposition `T = U |T|`

For a bounded operator `T : H →L[ℂ] H` on a complex Hilbert space, this file constructs the modulus
`|T| = (T⋆T)^{1/2}` and the **bounded polar decomposition** `T = U |T|`, where `U` is the partial
isometry that is isometric on `closure (range |T|)` and zero on its orthogonal complement.

This is a genuine gap in Mathlib: `LinearIsometry.extend` (the natural tool) is **finite-dimensional
only**, so the partial isometry is built by hand from `LinearMap.extendOfNorm` (dense extension into
a complete space) composed with the orthogonal projection onto `K = closure (range |T|)`.

## Main definitions

* `Spectra.QuantumMechanics.Channels.absOp T` — the modulus `|T| = CFC.abs T = (T⋆T)^{1/2}`.
* `Spectra.QuantumMechanics.Channels.polarIsometry T` — the partial isometry `U` with `U |T| = T`.

## Main results

* `norm_absOp_apply` — `‖|T| x‖ = ‖T x‖`; the isometry that makes `U : |T|x ↦ Tx` well-defined.
* `polar_decomposition` — `U ∘ |T| = T`, i.e. `T = U |T|`.

## Context

First brick of the trace-class / von Neumann predual development (the discharge-first route to the
Tomita–Takesaki fundamental theorem): `|T|` feeds the trace norm `‖T‖₁ = tr |T|`, and `U` feeds the
cyclicity `tr (AB) = tr (BA)`. Upstreamable to Mathlib.
-/

open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The modulus `|T|` and the isometry `‖|T| x‖ = ‖T x‖` -/

/-- The modulus `|T| = (T⋆T)^{1/2}`, realized as `CFC.abs` on the C⋆-algebra `H →L[ℂ] H`. -/
noncomputable def absOp (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.abs T

lemma absOp_nonneg (T : H →L[ℂ] H) : 0 ≤ absOp T := CFC.abs_nonneg T

lemma absOp_isSelfAdjoint (T : H →L[ℂ] H) : IsSelfAdjoint (absOp T) :=
  (CFC.abs_nonneg T).isSelfAdjoint

/-- `|T| · |T| = T⋆ · T` (the C⋆-algebra product on `H →L[ℂ] H` is composition). -/
lemma absOp_mul_absOp (T : H →L[ℂ] H) : absOp T * absOp T = star T * T :=
  CFC.abs_mul_abs T

/-- `(|T|)⋆ ∘ |T| = T⋆ ∘ T`. -/
lemma adjoint_absOp_comp_absOp (T : H →L[ℂ] H) :
    (absOp T)† ∘L absOp T = T† ∘L T := by
  rw [← star_eq_adjoint, ← star_eq_adjoint, ← mul_def, ← mul_def,
    (absOp_isSelfAdjoint T).star_eq, absOp_mul_absOp]

/-- **The polar isometry identity** `‖|T| x‖ = ‖T x‖` — the heart of the bounded polar
decomposition, making `U : |T|x ↦ Tx` a well-defined isometry on `range |T|`. -/
lemma norm_absOp_apply (T : H →L[ℂ] H) (x : H) : ‖absOp T x‖ = ‖T x‖ := by
  rw [apply_norm_eq_sqrt_inner_adjoint_right, apply_norm_eq_sqrt_inner_adjoint_right,
    adjoint_absOp_comp_absOp]

/-! ## The partial isometry `U` and `T = U |T|`

`K := closure (range |T|)`; the isometry `|T|x ↦ Tx` extends (via `LinearMap.extendOfNorm`, since
`LinearIsometry.extend` is finite-dimensional only) to `K → H`, then
`U := (that) ∘ orthogonalProjection K`. -/

/-- `K = closure (range |T|)`, the initial space of the polar isometry. -/
noncomputable def polarRange (T : H →L[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range (absOp T).toLinearMap).topologicalClosure

instance (T : H →L[ℂ] H) : CompleteSpace (polarRange T) :=
  Submodule.topologicalClosure.completeSpace _

lemma absOp_mem_polarRange (T : H →L[ℂ] H) (x : H) : absOp T x ∈ polarRange T :=
  (LinearMap.range (absOp T).toLinearMap).le_topologicalClosure (LinearMap.mem_range_self _ x)

/-- Corestriction of `|T|` to `K`. -/
noncomputable def absOpCorestrict (T : H →L[ℂ] H) : H →ₗ[ℂ] polarRange T :=
  LinearMap.codRestrict _ (absOp T).toLinearMap (absOp_mem_polarRange T)

@[simp] lemma coe_absOpCorestrict (T : H →L[ℂ] H) (x : H) :
    (absOpCorestrict T x : H) = absOp T x := rfl

lemma norm_absOpCorestrict (T : H →L[ℂ] H) (x : H) : ‖absOpCorestrict T x‖ = ‖T x‖ := by
  rw [Submodule.coe_norm, coe_absOpCorestrict, norm_absOp_apply]

/-- `range |T|` is dense in `K = closure (range |T|)`. -/
lemma denseRange_absOpCorestrict (T : H →L[ℂ] H) : DenseRange (absOpCorestrict T) := by
  have himg : ((↑) : polarRange T → H) '' Set.range (absOpCorestrict T) = Set.range (absOp T) := by
    rw [← Set.range_comp]; rfl
  have hcl : (polarRange T : Set H) = closure (Set.range (absOp T)) := by
    rw [polarRange, Submodule.topologicalClosure_coe, LinearMap.coe_range]; rfl
  have hclosed : IsClosed ((polarRange T : Set H)) := by rw [hcl]; exact isClosed_closure
  have hce : Topology.IsClosedEmbedding ((↑) : polarRange T → H) :=
    Topology.IsClosedEmbedding.subtypeVal hclosed
  rw [DenseRange, dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun y => ?_
  have hy : (↑y : H) ∈ closure (((↑) : polarRange T → H) '' Set.range (absOpCorestrict T)) := by
    rw [himg, ← hcl]; exact y.2
  rw [hce.closure_image_eq] at hy
  obtain ⟨z, hz, hzeq⟩ := hy
  rwa [Subtype.val_injective hzeq] at hz

/-- The isometry `K → H`, `|T|x ↦ Tx`, as a continuous linear map. -/
noncomputable def polarPartial (T : H →L[ℂ] H) : polarRange T →L[ℂ] H :=
  (T : H →ₗ[ℂ] H).extendOfNorm (absOpCorestrict T)

lemma polarPartial_absOpCorestrict (T : H →L[ℂ] H) (x : H) :
    polarPartial T (absOpCorestrict T x) = T x :=
  LinearMap.extendOfNorm_eq (denseRange_absOpCorestrict T)
    ⟨1, fun y => le_of_eq (by rw [one_mul, norm_absOpCorestrict, ContinuousLinearMap.coe_coe])⟩ x

/-- **The polar partial isometry** `U : H →L[ℂ] H`, isometric on `K = closure (range |T|)`, zero on
`Kᗮ`, with `U |T| = T`. -/
noncomputable def polarIsometry (T : H →L[ℂ] H) : H →L[ℂ] H :=
  polarPartial T ∘L (polarRange T).orthogonalProjection

@[simp] lemma polarIsometry_absOp (T : H →L[ℂ] H) (x : H) :
    polarIsometry T (absOp T x) = T x := by
  have hmem : absOp T x ∈ polarRange T := absOp_mem_polarRange T x
  have hproj : (polarRange T).orthogonalProjection (absOp T x) = absOpCorestrict T x := by
    apply Subtype.ext
    rw [coe_absOpCorestrict, ← Submodule.starProjection_apply]
    exact Submodule.starProjection_eq_self_iff.2 hmem
  rw [polarIsometry, ContinuousLinearMap.comp_apply, hproj, polarPartial_absOpCorestrict]

/-- **Bounded polar decomposition** `T = U |T|`. -/
theorem polar_decomposition (T : H →L[ℂ] H) : polarIsometry T ∘L absOp T = T := by
  ext x; simp

end Spectra.QuantumMechanics.Channels

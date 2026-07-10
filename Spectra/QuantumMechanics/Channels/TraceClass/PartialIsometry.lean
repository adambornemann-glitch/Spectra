/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Channels.TraceClass.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.DenseEmbedding

/-!
# Stage A — partial-isometry properties of the polar decomposition, and the Hilbert–Schmidt swap

Infrastructure for the trace-class hard core (`tr`, cyclicity, triangle, completeness), building
on the bounded polar decomposition `T = U |T|` (`PolarDecomp.lean`).

## Main results

* `norm_polarPartial_eq` — `polarPartial T` is an **isometry on all of** `K = closure (range |T|)`
  (Mathlib's `extendOfNorm` only supplies the `≤` bound; the reverse is proved here by continuity
  from the dense range).
* `norm_polarIsometry_apply_le` / `norm_polarIsometry_le_one` — the partial isometry `U` is a
  contraction.
* `polarIsometry_adjoint_comp_self` — `U⋆ U = P_K`, the orthogonal projection onto `K`.
* `polarIsometry_adjoint_comp` — **`U⋆ T = |T|`**, the initial-space identity (load-bearing for the
  trace-norm duality attainment `tr (U⋆ T) = tr |T|` and the triangle inequality).
* `tsum_enorm_apply_sq_adjoint` — the Hilbert–Schmidt sum is adjoint-invariant:
  `∑ᵢ ‖A eᵢ‖² = ∑ᵢ ‖A⋆ eᵢ‖²` for any bounded `A` (drops the self-adjointness of
  `tsum_enorm_apply_sq_comm`).
-/

open ContinuousLinearMap RCLike
open scoped InnerProductSpace InnerProduct ENNReal NNReal

namespace Spectra.QuantumMechanics.Channels

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The Hilbert–Schmidt sum is adjoint-invariant -/

variable {ι : Type*}

/-- **Adjoint-invariance of the Hilbert–Schmidt sum.** For any bounded `A`,
`∑ᵢ ‖A eᵢ‖² = ∑ᵢ ‖A⋆ eᵢ‖²` (same basis). Generalizes `tsum_enorm_apply_sq_comm` by dropping
self-adjointness and relating `A` to `A⋆` in one basis
(Parseval + Tonelli + `⟪eⱼ, A eᵢ⟫ = conj ⟪eᵢ, A⋆ eⱼ⟫`). -/
theorem tsum_enorm_apply_sq_adjoint (A : H →L[ℂ] H) (b : HilbertBasis ι ℂ H) :
    ∑' i, (‖A (b i)‖₊ : ℝ≥0∞) ^ 2 = ∑' i, (‖(A†) (b i)‖₊ : ℝ≥0∞) ^ 2 := by
  have h_sym : ∀ i j, ‖⟪b j, A (b i)⟫_ℂ‖₊ = ‖⟪b i, (A†) (b j)⟫_ℂ‖₊ := by
    intro i j
    rw [← adjoint_inner_left A (b i) (b j), ← inner_conj_symm (b i) ((A†) (b j)),
      RCLike.nnnorm_conj]
  calc ∑' i, (‖A (b i)‖₊ : ℝ≥0∞) ^ 2
      = ∑' i, ∑' j, (‖⟪b j, A (b i)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := by simp_rw [tsum_enorm_inner_sq b]
    _ = ∑' j, ∑' i, (‖⟪b j, A (b i)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, (‖⟪b i, (A†) (b j)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun j => tsum_congr fun i =>
          congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞) ^ 2) (h_sym i j)
    _ = ∑' j, (‖(A†) (b j)‖₊ : ℝ≥0∞) ^ 2 :=
        tsum_congr fun j => (tsum_enorm_inner_sq b ((A†) (b j))).symm

/-! ## `polarPartial` is an isometry on `K = closure (range |T|)` -/

/-- **`polarPartial T` is norm-preserving on all of `K = closure (range |T|)`.** Mathlib's
`LinearMap.extendOfNorm` only yields `‖polarPartial T y‖ ≤ ‖y‖`; the reverse (equality) follows by
continuity from the dense range `range |T|`, where `‖polarPartial T (|T| x)‖ = ‖T x‖ = ‖|T| x‖`. -/
lemma norm_polarPartial_eq (T : H →L[ℂ] H) (y : polarRange T) :
    ‖polarPartial T y‖ = ‖y‖ := by
  have hcont₁ : Continuous fun z : polarRange T => ‖polarPartial T z‖ :=
    continuous_norm.comp (polarPartial T).continuous
  have hEq : (fun z : polarRange T => ‖polarPartial T z‖) = (fun z => ‖z‖) := by
    apply DenseRange.equalizer (denseRange_absOpCorestrict T) hcont₁ continuous_norm
    funext x
    simp only [Function.comp_apply, polarPartial_absOpCorestrict, norm_absOpCorestrict]
  exact congrFun hEq y

/-- `polarPartial T` packaged as a linear isometry `K →ₗᵢ[ℂ] H`, so that `inner_map_map` gives
inner-product preservation on `K`. -/
noncomputable def polarPartialₗᵢ (T : H →L[ℂ] H) : polarRange T →ₗᵢ[ℂ] H where
  toLinearMap := (polarPartial T).toLinearMap
  norm_map' := norm_polarPartial_eq T

@[simp] lemma coe_polarPartialₗᵢ (T : H →L[ℂ] H) (y : polarRange T) :
    polarPartialₗᵢ T y = polarPartial T y := rfl

lemma polarIsometry_apply_eq (T : H →L[ℂ] H) (w : H) :
    polarIsometry T w = polarPartialₗᵢ T ((polarRange T).orthogonalProjection w) := rfl

/-! ## The partial isometry `U` is a contraction -/

/-- `‖U x‖ ≤ ‖x‖`: `U = polarPartial ∘ orthogonalProjection`, isometric on `K` and a contraction on
the projection. -/
lemma norm_polarIsometry_apply_le (T : H →L[ℂ] H) (x : H) : ‖polarIsometry T x‖ ≤ ‖x‖ := by
  have hx : polarIsometry T x = polarPartial T ((polarRange T).orthogonalProjection x) := rfl
  rw [hx, norm_polarPartial_eq]
  exact (polarRange T).norm_orthogonalProjection_apply_le x

/-- `‖U‖ ≤ 1`. -/
lemma norm_polarIsometry_le_one (T : H →L[ℂ] H) : ‖polarIsometry T‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_polarIsometry_apply_le T x

/-! ## The initial-space identities `U⋆ U = P_K` and `U⋆ T = |T|` -/

/-- **`U⋆ U = P_K`**, the orthogonal (star) projection onto `K = closure (range |T|)`. Proof: `U`
preserves inner products on `K` (isometry `inner_map_map`), so
`⟪U z, U x⟫ = ⟪P_K z, P_K x⟫ = ⟪z, P_K x⟫` by self-adjointness + idempotence of `P_K`. -/
lemma polarIsometry_adjoint_comp_self (T : H →L[ℂ] H) :
    (polarIsometry T)† ∘L polarIsometry T = (polarRange T).starProjection := by
  have hsa : ((polarRange T).starProjection)† = (polarRange T).starProjection := by
    rw [← star_eq_adjoint]; exact isSelfAdjoint_starProjection (polarRange T)
  have hidem : (polarRange T).starProjection * (polarRange T).starProjection
      = (polarRange T).starProjection := (polarRange T).isIdempotentElem_starProjection
  refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun z => ?_
  rw [ContinuousLinearMap.comp_apply, adjoint_inner_right,
      polarIsometry_apply_eq T z, polarIsometry_apply_eq T x, LinearIsometry.inner_map_map,
      Submodule.coe_inner, ← Submodule.starProjection_apply, ← Submodule.starProjection_apply,
      ← adjoint_inner_right (polarRange T).starProjection z ((polarRange T).starProjection x),
      hsa, ← ContinuousLinearMap.mul_apply, hidem]

/-- **`U⋆ T = |T|`** — the initial-space identity. Since `T = U |T|` and `|T| x ∈ K`,
`U⋆ (T x) = U⋆ U (|T| x) = P_K (|T| x) = |T| x`. -/
lemma polarIsometry_adjoint_comp (T : H →L[ℂ] H) :
    (polarIsometry T)† ∘L T = absOp T := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ← polarIsometry_absOp T x, ← ContinuousLinearMap.comp_apply,
      polarIsometry_adjoint_comp_self,
      Submodule.starProjection_eq_self_iff.2 (absOp_mem_polarRange T x)]

end Spectra.QuantumMechanics.Channels

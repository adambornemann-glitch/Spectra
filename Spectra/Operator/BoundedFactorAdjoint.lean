/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Operator.Closable
/-!
# The bounded-factor adjoint law `(b ∘ A)⋆ = A⋆ ∘ b⁻¹`  (Route B Stage 1 / kill-spike KS3)

For a **unitary factor** `b : F ≃ₗᵢ[ℂ] G` and a densely-defined operator `A : E →ₗ.[ℂ] F`, the
adjoint of the composite `b ∘ A` (`LinearMap.compPMap`) is computed by moving the unitary to the
other side: `y ∈ D((b∘A)⋆) ↔ b⁻¹y ∈ D(A⋆)`, and there `(b∘A)⋆ y = A⋆(b⁻¹ y)`.

This is the **true** bounded-factor case of the composite-adjoint law — in contrast to the
both-unbounded `(AB)⋆ = B⋆A⋆`, which is false in general.  The pivot is elementary:
`⟪y, b(Ax)⟫ = ⟪b⁻¹y, Ax⟫` (unitarity), so the defining continuity/Riesz data of the two adjoints
coincide.  It is absent from both Mathlib and the rest of Spectra (RC4 audit), and is the
Stage-1 substrate of the Field-3 polar-uniqueness build: applied to the extended polar
decomposition `S = W ∘ Δ^{½}` it yields `S⋆ = Δ^{½} ∘ W⁻¹`.

## Main statements

* `mem_compPMap_adjoint_domain_iff` — `y ∈ D((b∘A)⋆) ↔ b.symm y ∈ D(A⋆)` (no density needed).
* `compPMap_adjoint_apply` — `(b∘A)⋆ y = A⋆ (b.symm y)` for densely-defined `A`.
-/

open scoped InnerProductSpace

namespace Spectra.Operator

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The elementary pivot: `⟪y, (b∘A)x⟫ = ⟪b⁻¹y, Ax⟫` (unitarity of `b`). -/
lemma inner_compPMap_eq (b : F ≃ₗᵢ[ℂ] G) (A : E →ₗ.[ℂ] F) (y : G) (x : A.domain) :
    ⟪y, (b.toLinearEquiv.toLinearMap.compPMap A) x⟫_ℂ = ⟪(b.symm y : F), A x⟫_ℂ := by
  have h1 : (b.toLinearEquiv.toLinearMap.compPMap A) x = b (A x) := rfl
  rw [h1]
  conv_lhs => rw [← b.apply_symm_apply y]
  exact b.inner_map_map _ _

/-- **Domain of the bounded-factor adjoint**: `y ∈ D((b∘A)⋆) ↔ b⁻¹y ∈ D(A⋆)`.  The defining
functionals `x ↦ ⟪y, b(Ax)⟫` and `x ↦ ⟪b⁻¹y, Ax⟫` are literally equal, so continuity of one is
continuity of the other. -/
theorem mem_compPMap_adjoint_domain_iff (b : F ≃ₗᵢ[ℂ] G) (A : E →ₗ.[ℂ] F) {y : G} :
    y ∈ (b.toLinearEquiv.toLinearMap.compPMap A).adjoint.domain
      ↔ (b.symm y : F) ∈ A.adjoint.domain := by
  rw [LinearPMap.mem_adjoint_domain_iff, LinearPMap.mem_adjoint_domain_iff]
  have hfun : ((innerₛₗ ℂ y).comp (b.toLinearEquiv.toLinearMap.compPMap A).toFun)
      = ((innerₛₗ ℂ (b.symm y : F)).comp A.toFun) := by
    ext x
    simp only [LinearMap.comp_apply]
    exact inner_compPMap_eq b A y x
  rw [hfun]
  rfl

/-- **The bounded-factor adjoint law** `(b∘A)⋆ = A⋆ ∘ b⁻¹` (value form): for densely-defined `A`,
`(b∘A)⋆ y = A⋆(b⁻¹ y)`.  Both sides represent the same functional `x ↦ ⟪y, b(Ax)⟫ = ⟪b⁻¹y, Ax⟫`,
and the adjoint value is unique over a dense domain. -/
theorem compPMap_adjoint_apply (b : F ≃ₗᵢ[ℂ] G) (A : E →ₗ.[ℂ] F)
    (hA : Dense (A.domain : Set E)) (y : G)
    (hy : y ∈ (b.toLinearEquiv.toLinearMap.compPMap A).adjoint.domain) :
    (b.toLinearEquiv.toLinearMap.compPMap A).adjoint ⟨y, hy⟩
      = A.adjoint ⟨(b.symm y : F), (mem_compPMap_adjoint_domain_iff b A).mp hy⟩ := by
  refine LinearPMap.adjoint_apply_eq (T := b.toLinearEquiv.toLinearMap.compPMap A) hA
    ⟨y, hy⟩ fun x => ?_
  rw [inner_compPMap_eq b A y x]
  exact LinearPMap.adjoint_isFormalAdjoint hA
    ⟨(b.symm y : F), (mem_compPMap_adjoint_domain_iff b A).mp hy⟩ x

end Spectra.Operator

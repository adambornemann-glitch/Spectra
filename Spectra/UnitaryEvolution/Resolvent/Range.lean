/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Resolvent/Core.lean
-/
import Spectra.UnitaryEvolution.Resolvent.Range.Orthogonal
import Spectra.UnitaryEvolution.Resolvent.Range.ClosedRange
import Spectra.UnitaryEvolution.Resolvent.Range.Surjectivity
/-!
# The Resolvent Operator

This file defines the resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint
generators and proves the fundamental bound `‖R(z)‖ ≤ 1/|Im(z)|`.

## Main definitions

* `resolvent`: The resolvent operator `R(z) = (A - zI)⁻¹` as a bounded linear map

## Main statements

* `resolvent_bound`: `‖R(z)‖ ≤ 1/|Im(z)|`

## Implementation notes

The resolvent is constructed via `LinearMap.mkContinuous` using the existence
and uniqueness from `self_adjoint_range_all_z` together with the lower bound
estimate which provides the continuity bound.
-/
namespace QuantumMechanics.Resolvent

open InnerProductSpace MeasureTheory Complex Filter Topology
open QuantumMechanics.Bochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vector `ψ ∈ dom(A)` solving `(A - z)ψ = φ`, for self-adjoint `A`, `Im z ≠ 0`. -/
private noncomputable def resolventSolution {A : H →ₗ.[ℂ] H}
    (z : ℂ) (hz : z.im ≠ 0)
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (φ : H) : H :=
  ((Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists : A.domain) : H)

private lemma resolventSolution_mem {A : H →ₗ.[ℂ] H}
    (z : ℂ) (hz : z.im ≠ 0)
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (φ : H) :
    resolventSolution z hz hsym hplus hminus φ ∈ A.domain :=
  (Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists : A.domain).property

private lemma resolventSolution_eq {A : H →ₗ.[ℂ] H}
    (z : ℂ) (hz : z.im ≠ 0)
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (φ : H) :
    A ⟨resolventSolution z hz hsym hplus hminus φ, resolventSolution_mem z hz hsym hplus hminus φ⟩
      - z • resolventSolution z hz hsym hplus hminus φ = φ :=
  Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists

private lemma resolventSolution_add {A : H →ₗ.[ℂ] H}
    (z : ℂ) (hz : z.im ≠ 0)
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (φ₁ φ₂ : H) :
    resolventSolution z hz hsym hplus hminus (φ₁ + φ₂)
      = resolventSolution z hz hsym hplus hminus φ₁ + resolventSolution z hz hsym hplus hminus φ₂ := by
  set a := resolventSolution z hz hsym hplus hminus φ₁
  set b := resolventSolution z hz hsym hplus hminus φ₂
  have ha_mem := resolventSolution_mem z hz hsym hplus hminus φ₁
  have hb_mem := resolventSolution_mem z hz hsym hplus hminus φ₂
  have ha_eq := resolventSolution_eq z hz hsym hplus hminus φ₁
  have hb_eq := resolventSolution_eq z hz hsym hplus hminus φ₂
  have hab_mem : a + b ∈ A.domain := A.domain.add_mem ha_mem hb_mem
  -- a + b is a solution for φ₁ + φ₂, so uniqueness identifies it with the chosen one
  have hab_eq : A ⟨a + b, hab_mem⟩ - z • (a + b) = φ₁ + φ₂ := by
    have op_add : A ⟨a + b, hab_mem⟩ = A ⟨a, ha_mem⟩ + A ⟨b, hb_mem⟩ := by
      rw [← A.map_add]; rfl
    rw [op_add, smul_add]
    rw [show A ⟨a, ha_mem⟩ + A ⟨b, hb_mem⟩ - (z • a + z • b)
          = (A ⟨a, ha_mem⟩ - z • a) + (A ⟨b, hb_mem⟩ - z • b) by abel]
    rw [ha_eq, hb_eq]
  have huniq := (self_adjoint_range_all_z hsym hplus hminus z hz (φ₁ + φ₂)).unique
    (resolventSolution_eq z hz hsym hplus hminus (φ₁ + φ₂)) hab_eq
  exact congrArg Subtype.val huniq

private lemma resolventSolution_smul {A : H →ₗ.[ℂ] H}
    (z : ℂ) (hz : z.im ≠ 0)
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (c : ℂ) (φ : H) :
    resolventSolution z hz hsym hplus hminus (c • φ)
      = c • resolventSolution z hz hsym hplus hminus φ := by
  set s := resolventSolution z hz hsym hplus hminus φ
  have hs_mem := resolventSolution_mem z hz hsym hplus hminus φ
  have hs_eq := resolventSolution_eq z hz hsym hplus hminus φ
  have hcs_mem : c • s ∈ A.domain := A.domain.smul_mem c hs_mem
  have hcs_eq : A ⟨c • s, hcs_mem⟩ - z • (c • s) = c • φ := by
    have op_smul : A ⟨c • s, hcs_mem⟩ = c • A ⟨s, hs_mem⟩ := by
      rw [← A.map_smul]; rfl
    rw [op_smul, smul_comm z c, ← smul_sub, hs_eq]
  have huniq := (self_adjoint_range_all_z hsym hplus hminus z hz (c • φ)).unique
    (resolventSolution_eq z hz hsym hplus hminus (c • φ)) hcs_eq
  exact congrArg Subtype.val huniq

private lemma resolventSolution_norm_le {A : H →ₗ.[ℂ] H}
    (z : ℂ) (hz : z.im ≠ 0)
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (φ : H) :
    ‖resolventSolution z hz hsym hplus hminus φ‖ ≤ (1 / |z.im|) * ‖φ‖ := by
  have hmem := resolventSolution_mem z hz hsym hplus hminus φ
  have heq := resolventSolution_eq z hz hsym hplus hminus φ
  have hbound := lower_bound_estimate hsym z hz (resolventSolution z hz hsym hplus hminus φ) hmem
  rw [heq] at hbound
  have him : 0 < |z.im| := abs_pos.mpr hz
  calc ‖resolventSolution z hz hsym hplus hminus φ‖
      = (1 / |z.im|) * (|z.im| * ‖resolventSolution z hz hsym hplus hminus φ‖) := by field_simp
    _ ≤ (1 / |z.im|) * ‖φ‖ := by
        apply mul_le_mul_of_nonneg_left hbound
        positivity

/-- The resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint `A` and `Im(z) ≠ 0`. -/
noncomputable def resolvent {A : H →ₗ.[ℂ] H}
    (z : ℂ) (hz : z.im ≠ 0)
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := resolventSolution z hz hsym hplus hminus
      map_add' := resolventSolution_add z hz hsym hplus hminus
      map_smul' := fun c φ => by simpa using resolventSolution_smul z hz hsym hplus hminus c φ }
    (1 / |z.im|)
    (resolventSolution_norm_le z hz hsym hplus hminus)

/-- The resolvent satisfies `‖R(z)‖ ≤ 1/|Im(z)|`. -/
theorem resolvent_bound {A : H →ₗ.[ℂ] H}
    (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) :
    ‖resolvent z hz hsym hplus hminus‖ ≤ 1 / |z.im| := by
  have h_pointwise : ∀ φ : H, ‖resolvent z hz hsym hplus hminus φ‖ ≤ (1 / |z.im|) * ‖φ‖ := by
    intro φ
    let ψ_sub : A.domain := Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists
    let ψ := (ψ_sub : H)
    have h_domain : ψ ∈ A.domain := ψ_sub.property
    have h_eq : A ψ_sub - z • ψ = φ :=
      Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists
    have h_lower := lower_bound_estimate hsym z hz ψ h_domain
    rw [h_eq] at h_lower
    have h_im_pos : 0 < |z.im| := abs_pos.mpr hz
    have h_ψ_bound : ‖ψ‖ ≤ ‖φ‖ / |z.im| := by
      have h_mul : |z.im| * ‖ψ‖ ≤ ‖φ‖ := h_lower
      calc ‖ψ‖
          = (|z.im|)⁻¹ * (|z.im| * ‖ψ‖) := by field_simp
        _ ≤ (|z.im|)⁻¹ * ‖φ‖ := by
            apply mul_le_mul_of_nonneg_left h_mul
            exact inv_nonneg.mpr (abs_nonneg _)
        _ = ‖φ‖ / |z.im| := by rw [inv_mul_eq_div]
    have h_res_eq : resolvent z hz hsym hplus hminus φ = ψ := rfl
    calc ‖resolvent z hz hsym hplus hminus φ‖
        = ‖ψ‖ := by rw [h_res_eq]
      _ ≤ ‖φ‖ / |z.im| := h_ψ_bound
      _ = (1 / |z.im|) * ‖φ‖ := by ring
  apply ContinuousLinearMap.opNorm_le_bound
  · apply div_nonneg
    · norm_num
    · exact abs_nonneg _
  · exact h_pointwise

end QuantumMechanics.Resolvent

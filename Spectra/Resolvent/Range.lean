/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Range.Orthogonal
import Spectra.Resolvent.Range.ClosedRange
import Spectra.Resolvent.Range.Surjectivity
/-!
# The Resolvent Operator

This file defines the resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint generators,
proves the fundamental bound `‖R(z)‖ ≤ 1/|Im(z)|`, and establishes `R(z)` as an honest right
inverse of `A - zI` on its range.

## Main definitions

* `resolvent`: The resolvent operator `R(z) = (A - zI)⁻¹` as a bounded linear map

## Main statements

* `resolvent_bound`: `‖R(z)‖ ≤ 1/|Im(z)|`
* `resolvent_apply_mem_domain`: `R(z) φ ∈ dom(A)`
* `resolvent_sub_smul_apply`: `(A - z)(R(z) φ) = φ`, the right-inverse property

## Implementation notes

The resolvent is constructed via `LinearMap.mkContinuous` using the existence
and uniqueness from `self_adjoint_range_all_z` together with the lower bound
estimate which provides the continuity bound. `resolvent_bound` then reuses
`LinearMap.mkContinuous_norm_le` directly against that same bound rather than
re-deriving it, so the operator norm and the constructor's continuity bound
are the same number by construction.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/
open Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

variable {A : H →ₗ.[ℂ] H} (z : ℂ) (hz : z.im ≠ 0) (hsym : A.IsFormalAdjoint A)
  (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
  (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)

/-- The vector `ψ ∈ dom(A)` solving `(A - z)ψ = φ`, for symmetric `A` with deficiency indices
`(0, 0)` (witnessed by `hplus`/`hminus`) and `Im z ≠ 0`. Exposed as public API (rather than kept
`private`) so downstream files needing the same "solve `(A - z)ψ = φ` and extract `ψ`" pattern —
e.g. `Identities.lean`'s `resolvent_identity`/`resolvent_adjoint` — can reuse this trio instead of
re-deriving it from `self_adjoint_range_all_z`'s `Classical.choose`/`choose_spec` each time. -/
noncomputable def resolventSolution (φ : H) : H :=
  ((Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists : A.domain) : H)

/-- `resolventSolution z hz hsym hplus hminus φ` lies in the domain of `A`. -/
lemma resolventSolution_mem (φ : H) :
    resolventSolution z hz hsym hplus hminus φ ∈ A.domain :=
  (Classical.choose (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists : A.domain).property

/-- `resolventSolution` solves the resolvent equation: `(A - z)ψ = φ`. -/
lemma resolventSolution_eq (φ : H) :
    A ⟨resolventSolution z hz hsym hplus hminus φ,
        resolventSolution_mem z hz hsym hplus hminus φ⟩
      - z • resolventSolution z hz hsym hplus hminus φ = φ :=
  Classical.choose_spec (self_adjoint_range_all_z hsym hplus hminus z hz φ).exists

/-- `resolventSolution` is additive in its target `φ`. -/
private lemma resolventSolution_add (φ₁ φ₂ : H) :
    resolventSolution z hz hsym hplus hminus (φ₁ + φ₂)
      = resolventSolution z hz hsym hplus hminus φ₁
          + resolventSolution z hz hsym hplus hminus φ₂ := by
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

/-- `resolventSolution` respects scalar multiplication of its target `φ`. -/
private lemma resolventSolution_smul (c : ℂ) (φ : H) :
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

/-- The resolvent bound at the vector level:
`‖resolventSolution …‖ ≤ (1/|Im z|)·‖φ‖`. -/
private lemma resolventSolution_norm_le (φ : H) :
    ‖resolventSolution z hz hsym hplus hminus φ‖ ≤ (1 / |z.im|) * ‖φ‖ := by
  have hmem := resolventSolution_mem z hz hsym hplus hminus φ
  have heq := resolventSolution_eq z hz hsym hplus hminus φ
  have hbound := lower_bound_estimate hsym z (resolventSolution z hz hsym hplus hminus φ) hmem
  rw [heq] at hbound
  have _him : 0 < |z.im| := abs_pos.mpr hz
  calc ‖resolventSolution z hz hsym hplus hminus φ‖
      = (1 / |z.im|) * (|z.im| * ‖resolventSolution z hz hsym hplus hminus φ‖) := by field_simp
    _ ≤ (1 / |z.im|) * ‖φ‖ := by
        apply mul_le_mul_of_nonneg_left hbound
        positivity

/-- The resolvent operator `R(z) = (A - zI)⁻¹` for self-adjoint `A` and `Im(z) ≠ 0`. -/
noncomputable def resolvent : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := resolventSolution z hz hsym hplus hminus
      map_add' := resolventSolution_add z hz hsym hplus hminus
      map_smul' := fun c φ => by simpa using resolventSolution_smul z hz hsym hplus hminus c φ }
    (1 / |z.im|)
    (resolventSolution_norm_le z hz hsym hplus hminus)

/-- The resolvent satisfies `‖R(z)‖ ≤ 1/|Im(z)|`. -/
theorem resolvent_bound :
    ‖resolvent z hz hsym hplus hminus‖ ≤ 1 / |z.im| :=
  LinearMap.mkContinuous_norm_le _ (by positivity)
    (resolventSolution_norm_le z hz hsym hplus hminus)

/-- `R(z) φ` lies in `dom A` — the resolvent is a *right* inverse landing in the domain.
(Restatement of `resolventSolution_mem`, since `R(z) φ` is defeq to it.) -/
theorem resolvent_apply_mem_domain (φ : H) :
    resolvent z hz hsym hplus hminus φ ∈ A.domain :=
  resolventSolution_mem z hz hsym hplus hminus φ

/-- `(A - z)(R(z) φ) = φ` — the resolvent is a right inverse of `A - z`. -/
theorem resolvent_sub_smul_apply (φ : H) :
    A ⟨resolvent z hz hsym hplus hminus φ,
        resolvent_apply_mem_domain z hz hsym hplus hminus φ⟩
      - z • (resolvent z hz hsym hplus hminus φ) = φ :=
  resolventSolution_eq z hz hsym hplus hminus φ

end Spectra.Resolvent

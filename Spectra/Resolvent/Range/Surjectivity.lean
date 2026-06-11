/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Resolvent/Range/Surjectivity.lean
-/
import Spectra.Resolvent.Range.Orthogonal
import Spectra.Resolvent.Range.ClosedRange

open InnerProductSpace MeasureTheory Complex Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

/-- The range of (A - zI) forms a submodule. -/
def rangeSubmodule {A : H →ₗ.[ℂ] H} (z : ℂ) : Submodule ℂ H where
  carrier := Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H))
  add_mem' := by
    intro a b ha hb
    obtain ⟨ψa, hψa⟩ := ha
    obtain ⟨ψb, hψb⟩ := hb
    refine ⟨⟨(ψa : H) + (ψb : H), A.domain.add_mem ψa.property ψb.property⟩, ?_⟩
    have op_add := A.map_add ψa ψb
    simp only [← hψa, ← hψb]
    calc A ⟨(ψa : H) + (ψb : H), _⟩ - z • ((ψa : H) + (ψb : H))
        = (A ψa + A ψb) - z • ((ψa : H) + (ψb : H)) := by congr 1
      _ = (A ψa + A ψb) - (z • (ψa : H) + z • (ψb : H)) := by rw [smul_add]
      _ = (A ψa - z • (ψa : H)) + (A ψb - z • (ψb : H)) := by abel
  zero_mem' := ⟨⟨0, A.domain.zero_mem⟩, by simp only [smul_zero, sub_zero]; exact A.map_zero⟩
  smul_mem' := by
    intro c a ha
    obtain ⟨ψ, hψ⟩ := ha
    refine ⟨⟨c • (ψ : H), A.domain.smul_mem c ψ.property⟩, ?_⟩
    have op_smul := A.map_smul c ψ
    simp only [← hψ]
    calc A ⟨c • (ψ : H), _⟩ - z • (c • (ψ : H))
        = c • A ψ - z • (c • (ψ : H)) := by congr 1
      _ = c • A ψ - c • (z • (ψ : H)) := by rw [smul_comm z c]
      _ = c • (A ψ - z • (ψ : H)) := by rw [smul_sub]

/-- The range of (A - zI) is dense when Im(z) ≠ 0. -/
lemma range_sub_smul_dense {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H))) := by
  let M := rangeSubmodule (A := A) z
  have hM_eq : (M : Set H) = Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H)) := rfl
  have h_M_orth : Mᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro χ hχ
    apply orthogonal_range_eq_zero hsym hplus hminus z hz χ
    intro ψ
    have h_mem : A ψ - z • (ψ : H) ∈ M := ⟨ψ, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal h_mem hχ
  have h_M_top : M.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    rw [h_M_orth]
    exact Submodule.bot_orthogonal_eq_top
  have h_M_dense : Dense (M : Set H) := by
    rw [dense_iff_closure_eq]
    have h_coe : closure (M : Set H) = (M.topologicalClosure : Set H) :=
      (Submodule.topologicalClosure_coe M).symm
    rw [h_coe, h_M_top]
    rfl
  rw [← hM_eq]
  exact h_M_dense

/-! ### Uniqueness from lower bound -/

omit [CompleteSpace H] in
lemma resolvent_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (z : ℂ) (hz : z.im ≠ 0)
    (ψ : H) (hψ : ψ ∈ A.domain) (h : A ⟨ψ, hψ⟩ - z • ψ = 0) : ψ = 0 := by
  have hb := lower_bound_estimate hsym z hz ψ hψ
  rw [h, norm_zero] at hb
  have him : 0 < |z.im| := abs_pos.mpr hz
  have h0 : ‖ψ‖ ≤ 0 := by nlinarith [norm_nonneg ψ]
  exact norm_eq_zero.mp (le_antisymm h0 (norm_nonneg ψ))

omit [CompleteSpace H] in
/-- Solutions to (A - zI)ψ = φ are unique when Im(z) ≠ 0. -/
lemma solution_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (hz : z.im ≠ 0) (φ : H)
    (ψ ψ' : A.domain)
    (hψ : A ψ - z • (ψ : H) = φ)
    (hψ' : A ψ' - z • (ψ' : H) = φ) : ψ = ψ' := by
  have hχ : A ⟨(ψ:H) - ψ', sub_mem ψ.2 ψ'.2⟩ - z • ((ψ:H) - ψ') = 0 := by
    have op_eq : A ⟨(ψ:H) - ψ', sub_mem ψ.2 ψ'.2⟩ = A ψ - A ψ' := by
      convert A.map_sub ψ ψ' using 1
    calc A ⟨(ψ:H) - ψ', sub_mem ψ.2 ψ'.2⟩ - z • ((ψ:H) - ψ')
        = (A ψ - A ψ') - z • ((ψ:H) - ψ') := by rw [op_eq]
      _ = (A ψ - z • (ψ:H)) - (A ψ' - z • (ψ':H)) := by rw [smul_sub]; abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ
  have := resolvent_unique hsym z hz _ (sub_mem ψ.2 ψ'.2) hχ
  exact Subtype.ext (sub_eq_zero.mp this)

/-! ### Main theorem -/

/-- **Main Theorem**: For self-adjoint `A` and `Im(z) ≠ 0`, the equation
    `(A - zI)ψ = φ` has a unique solution for every `φ`. -/
lemma self_adjoint_range_all_z
    {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A)
    (hplus : ∀ φ : H, ∃ ψ : A.domain, A ψ + I • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : A.domain, A ψ - I • (ψ : H) = φ)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∀ φ : H, ∃! (ψ : A.domain), A ψ - z • (ψ : H) = φ := by
  intro φ
  have h_range_closed := range_sub_smul_closed hsym hminus z hz
  have h_dense := range_sub_smul_dense hsym hplus hminus z hz
  have h_eq_univ : Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H)) = Set.univ := by
    have h_closure := h_dense.closure_eq
    rw [IsClosed.closure_eq h_range_closed] at h_closure
    exact h_closure
  have h_exists : ∃ (ψ : A.domain), A ψ - z • (ψ : H) = φ := by
    have : φ ∈ Set.univ := Set.mem_univ φ
    rw [← h_eq_univ] at this
    exact Set.mem_range.mp this
  obtain ⟨ψ, hψ⟩ := h_exists
  exact ⟨ψ, hψ, fun ψ' hψ' => (solution_unique hsym z hz φ ψ ψ' hψ hψ').symm⟩

end Spectra.Resolvent

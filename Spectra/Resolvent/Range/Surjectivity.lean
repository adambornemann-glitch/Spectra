/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Range.Orthogonal
import Spectra.Resolvent.Range.ClosedRange

/-!
# Surjectivity of `A - zI` off the Real Axis

This file proves the keystone lemma of the resolvent stack: for a densely-defined symmetric
operator `A` (`hsym : A.IsFormalAdjoint A`) whose deficiency indices both vanish — witnessed by
surjectivity of `A + iI` and `A - iI` onto all of `H` (`hplus`/`hminus`) — the equation
`(A - zI)ψ = φ` has a *unique* solution `ψ ∈ dom A` for every `φ : H` and every `z` off the real
axis, not just at `z = ±i`.

This is the classical Reed–Simon VIII.3 criterion for self-adjointness, specialized to its
existence-and-uniqueness consequence. The reduction from *all* `z` with `Im(z) ≠ 0` down to the two
hypotheses at exactly `z = ±i` works because:

* **Density** (`range_sub_smul_dense`): a vector `χ` orthogonal to `ran(A - zI)` satisfies a weak
  eigenvalue equation `⟪Aψ, χ⟫ = z̄⟪ψ, χ⟫`; testing this equation against vectors supplied by
  `hplus`/`hminus` at `±i` forces `z̄ = z`, contradicting `Im(z) ≠ 0` unless `χ = 0`. So `ran(A -
  zI)ᗮ = ⊥`, i.e. the range is dense — for *every* `z` off the axis, from data at only `±i`.
* **Closedness** (`range_sub_smul_closed`, from `ClosedRange.lean`): the lower bound `|Im z| · ‖ψ‖
  ≤ ‖(A - zI)ψ‖` turns Cauchy images into Cauchy preimages, and the limit is placed in `dom A` by
  routing through the bounded resolvent at `i` — again reusing only the `±i` data.
* Dense + closed = all of `H`, giving existence; the same lower bound gives uniqueness
  (`resolvent_unique`/`solution_unique`).

Together these assemble into `self_adjoint_range_all_z`. Note the hypothesis is symmetry
(`IsFormalAdjoint`) plus the two deficiency-index conditions, not `IsSelfAdjoint A` outright —
the classical theorem is that this existence-and-uniqueness conclusion is in fact *equivalent* to
`A` being self-adjoint (see `Mathlib.Analysis.InnerProductSpace.LinearPMap.isSelfAdjoint_def`), but
that equivalence itself is not what this file proves.

## Main definitions

* `rangeSubmodule` — the range of `A - zI` as a `Submodule ℂ H`.

## Main statements

* `range_sub_smul_dense` — `ran(A - zI)` is dense in `H` when `Im(z) ≠ 0`.
* `resolvent_unique` — kernel triviality: `(A - zI)ψ = 0` forces `ψ = 0`.
* `solution_unique` — solutions of `(A - zI)ψ = φ` are unique.
* `self_adjoint_range_all_z` — existence and uniqueness of solutions to `(A - zI)ψ = φ`, for every
  `φ : H` and every `z` off the real axis.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Section VIII.3
-/

open Complex
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
    have op_add : A ⟨(ψa : H) + (ψb : H), A.domain.add_mem ψa.property ψb.property⟩
        = A ψa + A ψb := A.map_add ψa ψb
    simp only [← hψa, ← hψb]
    calc A ⟨(ψa : H) + (ψb : H), _⟩ - z • ((ψa : H) + (ψb : H))
        = (A ψa + A ψb) - z • ((ψa : H) + (ψb : H)) := by rw [op_add]
      _ = (A ψa + A ψb) - (z • (ψa : H) + z • (ψb : H)) := by rw [smul_add]
      _ = (A ψa - z • (ψa : H)) + (A ψb - z • (ψb : H)) := by abel
  zero_mem' := ⟨⟨0, A.domain.zero_mem⟩, by simp only [smul_zero, sub_zero]; exact A.map_zero⟩
  smul_mem' := by
    intro c a ha
    obtain ⟨ψ, hψ⟩ := ha
    refine ⟨⟨c • (ψ : H), A.domain.smul_mem c ψ.property⟩, ?_⟩
    have op_smul : A ⟨c • (ψ : H), A.domain.smul_mem c ψ.property⟩ = c • A ψ := A.map_smul c ψ
    simp only [← hψ]
    calc A ⟨c • (ψ : H), _⟩ - z • (c • (ψ : H))
        = c • A ψ - z • (c • (ψ : H)) := by rw [op_smul]
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
/-- If `(A - zI)ψ = 0` for `ψ ∈ dom A` and `Im(z) ≠ 0`, then `ψ = 0`. -/
lemma resolvent_unique {A : H →ₗ.[ℂ] H} (hsym : A.IsFormalAdjoint A) (z : ℂ) (hz : z.im ≠ 0)
    (ψ : H) (hψ : ψ ∈ A.domain) (h : A ⟨ψ, hψ⟩ - z • ψ = 0) : ψ = 0 := by
  have hb := lower_bound_estimate hsym z ψ hψ
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
    have hsub_eq : (⟨(ψ : H) - ψ', sub_mem ψ.2 ψ'.2⟩ : A.domain) = ψ - ψ' := by
      apply Subtype.ext
      rfl
    have op_eq : A ⟨(ψ : H) - ψ', sub_mem ψ.2 ψ'.2⟩ = A ψ - A ψ' := by
      rw [hsub_eq, A.map_sub]
    calc A ⟨(ψ:H) - ψ', sub_mem ψ.2 ψ'.2⟩ - z • ((ψ:H) - ψ')
        = (A ψ - A ψ') - z • ((ψ:H) - ψ') := by rw [op_eq]
      _ = (A ψ - z • (ψ:H)) - (A ψ' - z • (ψ':H)) := by rw [smul_sub]; abel
      _ = φ - φ := by rw [hψ, hψ']
      _ = 0 := sub_self φ
  have := resolvent_unique hsym z hz _ (sub_mem ψ.2 ψ'.2) hχ
  exact Subtype.ext (sub_eq_zero.mp this)

/-! ### Main theorem -/

/-- **Main Theorem**: for symmetric `A` (`hsym`) with deficiency indices `(0, 0)` — witnessed by
`hplus`/`hminus`, the surjectivity of `A ± iI` onto `H` — and `Im(z) ≠ 0`, the equation
`(A - zI)ψ = φ` has a unique solution `ψ ∈ dom A` for every `φ : H`. This is the existence half of
the classical Reed–Simon criterion; the hypothesis is symmetry plus deficiency-index surjectivity,
not `IsSelfAdjoint A` directly (compare `Mathlib`'s `isSelfAdjoint_def`). -/
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

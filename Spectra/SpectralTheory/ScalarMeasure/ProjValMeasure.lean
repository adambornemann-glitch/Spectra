/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: ScalarMeasure/ProjValMeasure.lean
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Order.Basic
/-!
# Projection-Valued Measures

This file defines the structure of a **projection-valued measure** (PVM) on a
Hilbert space and develops its basic API.

A projection-valued measure assigns to each measurable set `B ⊆ Ω` an
orthogonal projection `E(B)` on a Hilbert space `H`, subject to:

  (i)   `E(B)` is self-adjoint and idempotent for all `B`
  (ii)  `E(∅) = 0` and `E(Ω) = I`
  (iii) `E(B₁ ∩ B₂) = E(B₁) E(B₂)` for all measurable `B₁, B₂`
  (iv)  `E` is σ-additive in the strong operator topology

From these axioms we derive: commutativity of projections, the complement
formula `E(Bᶜ) = I - E(B)`, monotonicity, the norm bound `‖E(B)‖ ≤ 1`,
and the **scalar spectral measure** `μ_ψ(B) = ⟨E(B)ψ, ψ⟩` which is a
positive finite Borel measure for each `ψ ∈ H`.

## Design notes

All set arguments carry `MeasurableSet` hypotheses — a PVM is defined on
the σ-algebra, not on arbitrary subsets. The σ-additivity axiom is stated
as pointwise (strong operator) convergence of partial sums, which is the
natural topology for operator-valued measures and avoids requiring a
topology on the operator space itself.

The scalar measure is the primary interface between the PVM and Mathlib's
measure theory library: integration against a PVM is defined (in §5) by
reducing to integration against scalar measures via polarization.

## References

* Reed & Simon, *Methods of Modern Mathematical Physics I*, §VII.2
* Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*, Chapter 4

## Tags

projection-valued measure, spectral measure, orthogonal projection
-/
noncomputable section

open Complex MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace QuantumMechanics.SpectralTheory

/-! ### The PVM structure -/

/-- A **projection-valued measure** on a measurable space `Ω` valued in
bounded operators on a Hilbert space `H`.

Each measurable set is assigned an orthogonal projection, with the
projections satisfying multiplicativity and σ-additivity in the strong
operator topology. -/
structure ProjectionValuedMeasure (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (Ω : Type*) [MeasurableSpace Ω] where
  proj : Set Ω → (H →L[ℂ] H)
  proj_of_not_measurable : ∀ B, ¬MeasurableSet B → proj B = 0
  proj_self_adjoint : ∀ B, MeasurableSet B → (proj B).adjoint = proj B
  proj_idempotent : ∀ B, MeasurableSet B →
    (proj B).comp (proj B) = proj B
  proj_empty : proj ∅ = 0
  proj_univ : proj Set.univ = ContinuousLinearMap.id ℂ H
  proj_inter : ∀ B₁ B₂, MeasurableSet B₁ → MeasurableSet B₂ →
    proj (B₁ ∩ B₂) = (proj B₁).comp (proj B₂)
  proj_iUnion : ∀ (B : ℕ → Set Ω),
    (∀ k, MeasurableSet (B k)) →
    (Pairwise fun i j => Disjoint (B i) (B j)) →
    ∀ ψ : H,
      Tendsto
        (fun n => (Finset.range n).sum (fun k => proj (B k) ψ))
        atTop (𝓝 (proj (⋃ k, B k) ψ))

variable {Ω : Type*} [MeasurableSpace Ω]

namespace ProjectionValuedMeasure

/-! ### Notation -/

/-- Convenient notation: `E B` for `E.proj B`. -/
scoped notation:max E "⦃" B "⦄" => ProjectionValuedMeasure.proj E B

/-! ### Basic algebraic consequences -/

section Algebraic

variable (E : ProjectionValuedMeasure H Ω)

/-- Commutativity of projections: `E(B₁) E(B₂) = E(B₂) E(B₁)`.
Follows immediately from `E(B₁ ∩ B₂) = E(B₂ ∩ B₁)`. -/
lemma proj_comm (B₁ B₂ : Set Ω) (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    (E.proj B₁).comp (E.proj B₂) = (E.proj B₂).comp (E.proj B₁) := by
  rw [← E.proj_inter B₁ B₂ h₁ h₂, ← E.proj_inter B₂ B₁ h₂ h₁, Set.inter_comm]

/-- The complement formula: `E(Bᶜ) = I - E(B)`.
From `E(B) + E(Bᶜ) = E(Ω) = I` applied to the disjoint decomposition
`Ω = B ∪ Bᶜ`. -/
lemma proj_compl (B : Set Ω) (hB : MeasurableSet B) :
    E.proj Bᶜ = ContinuousLinearMap.id ℂ H - E.proj B := by
  ext ψ
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  suffices h : E.proj Bᶜ ψ + E.proj B ψ = ψ from eq_sub_of_add_eq h
  let f : ℕ → Set Ω := fun | 0 => B | 1 => Bᶜ | _ + 2 => ∅
  have hmeas : ∀ k, MeasurableSet (f k) :=
    fun | 0 => hB | 1 => hB.compl | _ + 2 => MeasurableSet.empty
  have hdisj : Pairwise fun i j => Disjoint (f i) (f j) := by
    intro i j hij
    match i, j with
    | 0, 0 | 1, 1 => exact absurd rfl hij
    | 0, 1 => exact disjoint_compl_right
    | 1, 0 => exact disjoint_compl_left
    | 0, _ + 2 | 1, _ + 2 => exact disjoint_bot_right
    | _ + 2, 0 | _ + 2, 1 | _ + 2, _ + 2 => exact disjoint_bot_left
  have huniv : ⋃ k, f k = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ∈ B
    · exact ⟨0, hx⟩
    · exact ⟨1, Set.mem_compl hx⟩
  have htend := E.proj_iUnion f hmeas hdisj ψ
  rw [huniv, E.proj_univ, ContinuousLinearMap.id_apply] at htend
  have hstab : ∀ n, 2 ≤ n →
    (Finset.range n).sum (fun k => E.proj (f k) ψ) = E.proj Bᶜ ψ + E.proj B ψ := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Finset.sum_range_add,
      Finset.sum_eq_zero (fun k _ => show E.proj (f (2 + k)) ψ = 0 by
      rw [show 2 + k = k + 2 from by omega]
      simp [f, E.proj_empty, ContinuousLinearMap.zero_apply]),
        add_zero];
      simp [Finset.sum_range_succ, f, add_comm]
  have htend' : Tendsto (fun n => (Finset.range n).sum fun k => E.proj (f k) ψ) atTop
    (𝓝 (E.proj Bᶜ ψ + E.proj B ψ)) := by
    rw [Filter.tendsto_def]
    intro U hU
    exact eventually_atTop.mpr ⟨2, fun n hn => by
      rw [← Set.mem_preimage]
      simp; rw [hstab n hn]
      exact mem_of_mem_nhds hU⟩
  exact tendsto_nhds_unique htend' htend


/-- Difference formula: `E(B₁ \ B₂) = E(B₁) - E(B₁ ∩ B₂)` for measurable sets. -/
lemma proj_diff (B₁ B₂ : Set Ω) (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    E.proj (B₁ \ B₂) = E.proj B₁ - (E.proj B₁).comp (E.proj B₂) := by
  rw [Set.diff_eq, E.proj_inter B₁ B₂ᶜ h₁ h₂.compl, E.proj_compl B₂ h₂]
  ext ψ
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
             ContinuousLinearMap.id_apply, map_sub]

/-- Projections for disjoint sets are orthogonal: `E(B₁) E(B₂) = 0`
when `B₁ ∩ B₂ = ∅`. -/
lemma proj_orthogonal (B₁ B₂ : Set Ω) (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂)
    (h_disj : Disjoint B₁ B₂) :
    (E.proj B₁).comp (E.proj B₂) = 0 := by
  rw [← E.proj_inter B₁ B₂ h₁ h₂]
  have : B₁ ∩ B₂ = ∅ := Set.disjoint_iff_inter_eq_empty.mp h_disj
  rw [this, E.proj_empty]

/-- Finite additivity: `E(B₁ ∪ B₂) = E(B₁) + E(B₂)` for disjoint measurable sets. -/
lemma proj_union_disjoint (B₁ B₂ : Set Ω)
    (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂)
    (h_disj : Disjoint B₁ B₂) :
    E.proj (B₁ ∪ B₂) = E.proj B₁ + E.proj B₂ := by
  ext ψ
  simp only [ContinuousLinearMap.add_apply]
  let f : ℕ → Set Ω := fun | 0 => B₁ | 1 => B₂ | _ + 2 => ∅
  have hmeas : ∀ k, MeasurableSet (f k) :=
    fun | 0 => h₁ | 1 => h₂ | _ + 2 => MeasurableSet.empty
  have hdisj : Pairwise fun i j => Disjoint (f i) (f j) := by
    intro i j hij
    match i, j with
    | 0, 0 | 1, 1 => exact absurd rfl hij
    | 0, 1 => exact h_disj
    | 1, 0 => exact h_disj.symm
    | 0, _ + 2 | 1, _ + 2 => exact disjoint_bot_right
    | _ + 2, 0 | _ + 2, 1 | _ + 2, _ + 2 => exact disjoint_bot_left
  have hunion : ⋃ k, f k = B₁ ∪ B₂ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨k, hk⟩
      match k with
      | 0 => exact Or.inl hk
      | 1 => exact Or.inr hk
      | _ + 2 => exact or_iff_not_and_not.mpr fun a => hk
    · rintro (hx | hx)
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
  have htend := E.proj_iUnion f hmeas hdisj ψ
  rw [hunion] at htend
  have hstab : ∀ n, 2 ≤ n →
      (Finset.range n).sum (fun k => E.proj (f k) ψ) = E.proj B₁ ψ + E.proj B₂ ψ := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Finset.sum_range_add,
      Finset.sum_eq_zero (fun k _ => show E.proj (f (2 + k)) ψ = 0 by
        rw [show 2 + k = k + 2 from by omega]
        simp [f, E.proj_empty, ContinuousLinearMap.zero_apply]),
      add_zero]
    simp [Finset.sum_range_succ, f]
  have htend' : Tendsto (fun n => (Finset.range n).sum fun k => E.proj (f k) ψ) atTop
    (𝓝 (E.proj B₁ ψ + E.proj B₂ ψ)) :=
  tendsto_atTop_of_eventually_const (i₀ := 2) (fun n hn => hstab n hn)
  exact tendsto_nhds_unique htend htend'

/-- Monotonicity for subsets: `E(B₁) ≤ E(B₂)` when `B₁ ⊆ B₂`, in the
sense that `E(B₂) - E(B₁)` is a positive operator. Here we state the
concrete version: `⟨E(B₁)ψ, ψ⟩ ≤ ⟨E(B₂)ψ, ψ⟩`. -/
lemma proj_monotone (B₁ B₂ : Set Ω) (h₁ : MeasurableSet B₁)
    (h₂ : MeasurableSet B₂) (h_sub : B₁ ⊆ B₂) (ψ : H) :
    (⟪ E.proj B₁ ψ, ψ⟫_ℂ).re ≤ (⟪E.proj B₂ ψ, ψ⟫_ℂ).re := by
  have h_diff_meas : MeasurableSet (B₂ \ B₁) := h₂.diff h₁
  -- B₁ ⊆ B₂ implies E(B₂) ∘ E(B₁) = E(B₁)
  have h_comp : (E.proj B₂).comp (E.proj B₁) = E.proj B₁ := by
    rw [← E.proj_inter B₂ B₁ h₂ h₁, Set.inter_eq_right.mpr h_sub]
  -- So E(B₂ \ B₁) = E(B₂) - E(B₁)
  have h_diff_eq : E.proj (B₂ \ B₁) = E.proj B₂ - E.proj B₁ := by
    rw [E.proj_diff B₂ B₁ h₂ h₁, h_comp]
  -- For the projection P = E(B₂ \ B₁): ⟨Pψ, ψ⟩ = ‖Pψ‖²
  set P := E.proj (B₂ \ B₁)
  have h_sa : P.adjoint = P := E.proj_self_adjoint _ h_diff_meas
  have h_idem : P.comp P = P := E.proj_idempotent _ h_diff_meas
  have h_Pψ_eq : P ψ = P (P ψ) := by
    have := congrFun (congrArg DFunLike.coe h_idem) ψ
    rw [ContinuousLinearMap.comp_apply] at this; exact this.symm
  -- ⟨Pψ, ψ⟩ = ⟨P(Pψ), ψ⟩ = ⟨Pψ, P†ψ⟩ = ⟨Pψ, Pψ⟩
  have inner_eq : ⟪P ψ, ψ⟫_ℂ = ⟪P ψ, P ψ⟫_ℂ := by
    conv_lhs => rw [h_Pψ_eq]
    rw [← ContinuousLinearMap.adjoint_inner_right P (P ψ) ψ, h_sa]
  -- Expand: re⟨Pψ, ψ⟩ = re⟨E(B₂)ψ, ψ⟩ - re⟨E(B₁)ψ, ψ⟩
  have diff_eq : (⟪P ψ, ψ⟫_ℂ).re =
      (⟪E.proj B₂ ψ, ψ⟫_ℂ).re - (⟪E.proj B₁ ψ, ψ⟫_ℂ).re := by
    simp only [P, h_diff_eq, ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re]
  -- Combine: ‖Pψ‖² = re⟨E(B₂)ψ, ψ⟩ - re⟨E(B₁)ψ, ψ⟩ ≥ 0
  have h_nonneg : 0 ≤ (⟪P ψ, ψ⟫_ℂ).re := by
    rw [inner_eq]; exact inner_self_nonneg (𝕜 := ℂ)
  linarith


end Algebraic

/-! ### Projection properties in terms of inner products -/

section InnerProduct

variable (E : ProjectionValuedMeasure H Ω)

/-- The inner product `⟨E(B)ψ, ψ⟩` is real and non-negative. -/
lemma proj_inner_self_nonneg (B : Set Ω) (hB : MeasurableSet B) (ψ : H) :
    0 ≤ (⟪E.proj B ψ, ψ⟫_ℂ).re := by
  have h_idem := E.proj_idempotent B hB
  have h_sa := E.proj_self_adjoint B hB
  have : ⟪E.proj B ψ, ψ⟫_ℂ = ⟪E.proj B ψ, E.proj B ψ⟫_ℂ := by
    conv_lhs => rw [show E.proj B ψ = (E.proj B).comp (E.proj B) ψ from
      (congrFun (congrArg DFunLike.coe h_idem) ψ).symm]
    rw [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_right (E.proj B) _ ψ, h_sa]
  rw [this]; exact inner_self_nonneg (𝕜 := ℂ)

/-- The inner product `⟨E(B)ψ, ψ⟩` is real (imaginary part vanishes). -/
lemma proj_inner_self_real (B : Set Ω) (hB : MeasurableSet B) (ψ : H) :
    (⟪E.proj B ψ, ψ⟫_ℂ).im = 0 := by
  have h_idem := E.proj_idempotent B hB
  have h_sa := E.proj_self_adjoint B hB
  have : ⟪E.proj B ψ, ψ⟫_ℂ = ⟪E.proj B ψ, E.proj B ψ⟫_ℂ := by
    conv_lhs => rw [show E.proj B ψ = (E.proj B).comp (E.proj B) ψ from
      (congrFun (congrArg DFunLike.coe h_idem) ψ).symm]
    rw [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_right (E.proj B) _ ψ, h_sa]
  rw [this, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `⟨E(B)ψ, ψ⟩ ≤ ‖ψ‖²`. -/
lemma proj_inner_self_le_norm_sq (B : Set Ω) (hB : MeasurableSet B) (ψ : H) :
    (⟪E.proj B ψ, ψ⟫_ℂ).re ≤ ‖ψ‖ ^ 2 := by
  have h := E.proj_monotone B Set.univ hB MeasurableSet.univ (Set.subset_univ B) ψ
  rw [E.proj_univ, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K] at h
  simp [Complex.ofReal_re, ← Complex.ofReal_pow] at h; exact h

/-- `E(B)ψ = ψ` iff `⟨E(B)ψ, ψ⟩ = ‖ψ‖²`. -/
lemma proj_eq_self_iff_inner (B : Set Ω) (hB : MeasurableSet B) (ψ : H) :
    E.proj B ψ = ψ ↔ (⟪E.proj B ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
  constructor
  · intro h; rw [h, inner_self_eq_norm_sq_to_K]; norm_cast
  · intro h
    -- E(Bᶜ)ψ = ψ - E(B)ψ
    have hc_eq : E.proj Bᶜ ψ = ψ - E.proj B ψ := by
      have := congrFun (congrArg DFunLike.coe (E.proj_compl B hB)) ψ
      simpa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] using this
    -- ⟨E(Bᶜ)ψ, ψ⟩ = ⟨E(Bᶜ)ψ, E(Bᶜ)ψ⟩ (self-adj + idem)
    have inner_eq : ⟪E.proj Bᶜ ψ, ψ⟫_ℂ = ⟪E.proj Bᶜ ψ, E.proj Bᶜ ψ⟫_ℂ := by
      conv_lhs => rw [show E.proj Bᶜ ψ = (E.proj Bᶜ).comp (E.proj Bᶜ) ψ from
        (congrFun (congrArg DFunLike.coe (E.proj_idempotent Bᶜ hB.compl)) ψ).symm]
      rw [ContinuousLinearMap.comp_apply,
          ← ContinuousLinearMap.adjoint_inner_right (E.proj Bᶜ) _ ψ,
          E.proj_self_adjoint Bᶜ hB.compl]
    -- E(Bᶜ)ψ = 0 via inner_self_eq_zero
    have hc_zero : E.proj Bᶜ ψ = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), ← inner_eq]
      apply Complex.ext
      · -- re: ⟨ψ,ψ⟩ - ⟨E(B)ψ,ψ⟩ = ‖ψ‖² - ‖ψ‖² = 0
        rw [hc_eq, inner_sub_left, Complex.sub_re, Complex.zero_re]
        have : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        linarith
      · rw [Complex.zero_im]; exact E.proj_inner_self_real Bᶜ hB.compl ψ
    -- 0 = ψ - E(B)ψ → E(B)ψ = ψ
    exact (sub_eq_zero.mp (hc_eq.symm.trans hc_zero)).symm

/-- `⟨E(Ω)ψ, ψ⟩ = ‖ψ‖²`. -/
lemma proj_univ_inner (ψ : H) :
    ⟪E.proj Set.univ ψ, ψ⟫_ℂ = ↑(‖ψ‖ ^ 2) := by
  rw [E.proj_univ]
  simp [ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K]


/-- `‖E(B)ψ‖² = re⟨E(B)ψ, ψ⟩` — the idempotent/self-adjoint trick that
appears throughout the PVM API, factored into a single lemma. -/
lemma proj_norm_sq_eq_inner (B : Set Ω) (hB : MeasurableSet B) (ψ : H) :
    ‖E.proj B ψ‖ ^ 2 = (⟪E.proj B ψ, ψ⟫_ℂ).re := by
  have h_eq : ⟪E.proj B ψ, ψ⟫_ℂ = ⟪E.proj B ψ, E.proj B ψ⟫_ℂ := by
    conv_lhs => rw [show E.proj B ψ = (E.proj B).comp (E.proj B) ψ from
      (congrFun (congrArg DFunLike.coe (E.proj_idempotent B hB)) ψ).symm]
    rw [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_right (E.proj B) _ ψ,
        E.proj_self_adjoint B hB]
  rw [h_eq, inner_self_eq_norm_sq_to_K]; norm_cast

end InnerProduct

/-! ### Operator norm bound -/

section Norm

variable (E : ProjectionValuedMeasure H Ω)

/-- The range of `E(B)` equals its fixed-point set. -/
lemma proj_range_eq_ker_compl (B : Set Ω) (hB : MeasurableSet B) :
    ∀ ψ : H, E.proj B (E.proj B ψ) = E.proj B ψ := by
  intro ψ
  have h := E.proj_idempotent B hB
  exact congrFun (congrArg DFunLike.coe h) ψ

/-- `‖E(B)ψ‖ ≤ ‖ψ‖` for all `ψ`. -/
lemma proj_norm_le (B : Set Ω) (hB : MeasurableSet B) (ψ : H) :
    ‖E.proj B ψ‖ ≤ ‖ψ‖ := by
  nontriviality H
  rw [← Real.sqrt_sq (norm_nonneg (E.proj B ψ)), ← Real.sqrt_sq (norm_nonneg ψ)]
  apply Real.sqrt_le_sqrt
  have inner_eq : ⟪E.proj B ψ, ψ⟫_ℂ = ⟪E.proj B ψ, E.proj B ψ⟫_ℂ := by
    conv_lhs => rw [show E.proj B ψ = (E.proj B).comp (E.proj B) ψ from
      (congrFun (congrArg DFunLike.coe (E.proj_idempotent B hB)) ψ).symm]
    rw [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_right (E.proj B) _ ψ,
        E.proj_self_adjoint B hB]
  have : ‖E.proj B ψ‖ ^ 2 = (⟪E.proj B ψ, ψ⟫_ℂ).re := by
    rw [inner_eq, inner_self_eq_norm_sq_to_K]; norm_cast
  linarith [E.proj_inner_self_le_norm_sq B hB ψ]

/-- The operator norm of `E(B)` is at most 1. -/
lemma proj_opNorm_le_one (B : Set Ω) (hB : MeasurableSet B) :
    ‖E.proj B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  simp [one_mul, E.proj_norm_le B hB ψ]


end Norm

/-! ### The scalar spectral measure -/

section ScalarMeasure

variable (E : ProjectionValuedMeasure H Ω)

/-- The **scalar spectral measure** associated to a PVM and a vector `ψ`,
defined by `μ_ψ(B) = ⟨E(B)ψ, ψ⟩`.

This is a finite positive Borel measure with `μ_ψ(Ω) = ‖ψ‖²`. It is the
primary interface between PVMs and Mathlib's measure-theoretic integration. -/
noncomputable def scalarMeasure (ψ : H) : Measure Ω :=
  Measure.ofMeasurable
    (fun B _hB => ENNReal.ofReal (⟪E.proj B ψ, ψ⟫_ℂ).re)
    (by simp [E.proj_empty, inner_zero_left])
    (by
  intro f hf hd
  have h_nonneg : ∀ k, 0 ≤ (⟪E.proj (f k) ψ, ψ⟫_ℂ).re :=
    fun k => E.proj_inner_self_nonneg (f k) (hf k) ψ
  -- Step 1: Real partial sums of ⟨E(fk)ψ, ψ⟩ converge
  have htend := E.proj_iUnion f hf hd ψ
  have h_re : Tendsto
    (fun n => ∑ k ∈ Finset.range n, (⟪E.proj (f k) ψ, ψ⟫_ℂ).re)
    atTop (𝓝 (⟪E.proj (⋃ k, f k) ψ, ψ⟫_ℂ).re) := by
    have h_inner := htend.inner (tendsto_const_nhds (x := ψ)) (𝕜 := ℂ)
    have h_sum : ∀ n, ⟪∑ k ∈ Finset.range n, E.proj (f k) ψ, ψ⟫_ℂ =
        ∑ k ∈ Finset.range n, ⟪E.proj (f k) ψ, ψ⟫_ℂ := by
      intro n; induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, inner_add_left, ih, Finset.sum_range_succ]
    simp_rw [h_sum] at h_inner
    have h_comp := (Complex.continuous_re.tendsto _).comp h_inner
    exact Tendsto.congr (fun n => by
      simp only [Function.comp]
      induction (Finset.range n) using Finset.cons_induction with
      | empty => simp
      | cons a s ha ih => simp only [Finset.cons_eq_insert, re_sum]) h_comp
  -- Step 2: ENNReal partial sums converge (ofReal commutes with nonneg finite sums)
  have h_ennreal : Tendsto
      (fun n => ∑ k ∈ Finset.range n, ENNReal.ofReal (⟪E.proj (f k) ψ, ψ⟫_ℂ).re)
      atTop (𝓝 (ENNReal.ofReal (⟪E.proj (⋃ k, f k) ψ, ψ⟫_ℂ).re)) := by
    simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => h_nonneg k)]
    exact (ENNReal.continuous_ofReal.tendsto _).comp h_re
  -- Step 3: tsum = iSup of monotone partial sums = limit
  rw [ENNReal.tsum_eq_iSup_nat]
  have h_mono : Monotone (fun n => ∑ k ∈ Finset.range n,
      ENNReal.ofReal (⟪E.proj (f k) ψ, ψ⟫_ℂ).re) :=
    fun _ _ h => Finset.sum_le_sum_of_subset (Finset.range_mono h)
  exact (tendsto_nhds_unique (tendsto_atTop_iSup h_mono) h_ennreal).symm)


/-- The scalar measure of `B` equals `⟨E(B)ψ, ψ⟩` (as a real number). -/
lemma scalarMeasure_apply (ψ : H) (B : Set Ω) (hB : MeasurableSet B) :
    (E.scalarMeasure ψ B).toReal = (⟪E.proj B ψ, ψ⟫_ℂ).re := by
  simp only [scalarMeasure, Measure.ofMeasurable_apply B hB]
  exact ENNReal.toReal_ofReal (E.proj_inner_self_nonneg B hB ψ)


/-- The scalar measure of the full space equals `‖ψ‖²`. -/
lemma scalarMeasure_univ (ψ : H) :
    (E.scalarMeasure ψ Set.univ).toReal = ‖ψ‖ ^ 2 := by
  rw [E.scalarMeasure_apply ψ Set.univ MeasurableSet.univ, E.proj_univ]
  simp only [ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K]
  norm_cast


/-- The scalar measure is a finite measure. -/
instance scalarMeasure_isFinite (ψ : H) :
    IsFiniteMeasure (E.scalarMeasure ψ) where
  measure_univ_lt_top := by
    simp only [scalarMeasure, Measure.ofMeasurable_apply _ MeasurableSet.univ]
    exact ENNReal.ofReal_lt_top

/-- The scalar measure is monotone. -/
theorem scalarMeasure_mono (ψ : H) (B₁ B₂ : Set Ω)
    (_h₁ : MeasurableSet B₁) (_h₂ : MeasurableSet B₂) (h_sub : B₁ ⊆ B₂) :
    E.scalarMeasure ψ B₁ ≤ E.scalarMeasure ψ B₂ :=
  OuterMeasureClass.measure_mono (E.scalarMeasure ψ) h_sub


/-- Quadratic scaling: `μ_{cψ} = |c|² · μ_ψ`. -/
theorem scalarMeasure_smul (c : ℂ) (ψ : H) :
    E.scalarMeasure (c • ψ) = ‖c‖₊ ^ 2 • E.scalarMeasure ψ := by
  ext B hB
  simp only [scalarMeasure, Measure.ofMeasurable_apply B hB, Measure.smul_apply]
  -- Key: re⟨E(B)(cψ), cψ⟩ = ‖c‖² · re⟨E(B)ψ, ψ⟩
  have self_inner : ∀ x : H, ⟪E.proj B x, x⟫_ℂ = ⟪E.proj B x, E.proj B x⟫_ℂ := by
    intro x
    conv_lhs => rw [show E.proj B x = (E.proj B).comp (E.proj B) x from
      (congrFun (congrArg DFunLike.coe (E.proj_idempotent B hB)) x).symm]
    rw [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_right (E.proj B) _ x,
        E.proj_self_adjoint B hB]
  have key : (⟪E.proj B (c • ψ), c • ψ⟫_ℂ).re = ‖c‖ ^ 2 * (⟪E.proj B ψ, ψ⟫_ℂ).re := by
    rw [self_inner, self_inner, map_smul, inner_self_eq_norm_sq_to_K,
        inner_self_eq_norm_sq_to_K]
    simp only [coe_algebraMap]
    rw [norm_smul]
    simp only [ofReal_mul]
    norm_cast
    exact mul_pow ‖c‖ ‖E⦃B⦄ ψ‖ 2
  -- Lift to ENNReal
  rw [key, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [ENNReal.ofReal_pow (norm_nonneg c)]
  simp only [ofReal_norm]; abel


/-- The scalar measure vanishes iff `E(B)ψ = 0`. -/
theorem scalarMeasure_eq_zero_iff (ψ : H) (B : Set Ω) (hB : MeasurableSet B) :
    E.scalarMeasure ψ B = 0 ↔ E.proj B ψ = 0 := by
  simp only [scalarMeasure, Measure.ofMeasurable_apply B hB]
  constructor
  · intro h
    have h_nonneg := E.proj_inner_self_nonneg B hB ψ
    rw [ENNReal.ofReal_eq_zero] at h
    have h_re : (⟪E.proj B ψ, ψ⟫_ℂ).re = 0 := le_antisymm h h_nonneg
    have h_im := E.proj_inner_self_real B hB ψ
    have self_inner : ⟪E.proj B ψ, ψ⟫_ℂ = ⟪E.proj B ψ, E.proj B ψ⟫_ℂ := by
      conv_lhs => rw [show E.proj B ψ = (E.proj B).comp (E.proj B) ψ from
        (congrFun (congrArg DFunLike.coe (E.proj_idempotent B hB)) ψ).symm]
      rw [ContinuousLinearMap.comp_apply,
          ← ContinuousLinearMap.adjoint_inner_right (E.proj B) _ ψ,
          E.proj_self_adjoint B hB]
    have h_zero : ⟪E.proj B ψ, E.proj B ψ⟫_ℂ = 0 := by
      rw [← self_inner]; exact Complex.ext h_re h_im
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp h_zero
  · intro h; simp [h, inner_zero_left]

end ScalarMeasure

/-! ### Continuity from above -/

section ContinuityFromAbove

variable (E : ProjectionValuedMeasure H Ω)


/-- **Continuity from above**: if `B` is an antitone sequence of measurable
sets, then `E(Bₙ)ψ → E(⋂ₙ Bₙ)ψ` in the strong operator topology.

This is the key ingredient for right-continuity of the resolution of the
identity and for `cdf_tendsto_bot`. -/
lemma proj_tendsto_of_antitone (B : ℕ → Set Ω) (hB : ∀ k, MeasurableSet (B k))
    (h_anti : Antitone B) (ψ : H) :
    Tendsto (fun n => E.proj (B n) ψ) atTop (𝓝 (E.proj (⋂ n, B n) ψ)) := by
  set A := ⋂ n, B n with hA_def
  have hA : MeasurableSet A := MeasurableSet.iInter hB
  have hA_sub : ∀ n, A ⊆ B n := fun n => Set.iInter_subset B n
  -- Telescope pieces: Cₖ = Bₖ \ B(k+1)
  set C : ℕ → Set Ω := fun k => B k \ B (k + 1)
  have hC_meas : ∀ k, MeasurableSet (C k) := fun k => (hB k).diff (hB (k + 1))
  -- Cₖ are pairwise disjoint
  have hC_disj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_sdiff_left.mono_right
        (Set.diff_subset.trans (h_anti (Nat.succ_le_of_lt h)))
    · exact (Set.disjoint_sdiff_left.mono_right
        (Set.diff_subset.trans (h_anti (Nat.succ_le_of_lt h)))).symm
  -- ⋃ₖ Cₖ = B 0 \ A
  have hC_union : ⋃ k, C k = B 0 \ A := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_diff, hA_def, Set.mem_iInter]
    constructor
    · rintro ⟨k, hxk, hxk1⟩
      exact ⟨h_anti (Nat.zero_le k) hxk, fun h => hxk1 (h (k + 1))⟩
    · rintro ⟨hx0, hxA⟩
      push Not at hxA
      obtain ⟨m, hm⟩ := hxA
      -- x ∈ B 0 but x ∉ B m, so there exists k with x ∈ B k \ B(k+1)
      have : ∃ k, x ∈ B k ∧ x ∉ B (k + 1) := by
        by_contra hall
        push Not at hall
        have : ∀ n, x ∈ B n := by
          intro n; induction n with
          | zero => exact hx0
          | succ n ih => exact hall n ih
        exact hm (this m)
      exact this
  -- σ-additivity: partial sums → E(⋃ Cₖ)ψ
  have htend_C := E.proj_iUnion C hC_meas hC_disj ψ
  rw [hC_union] at htend_C
  -- Telescoping: Σₖ<n E(Cₖ)ψ = E(B 0)ψ - E(Bₙ)ψ
  have h_telesc : ∀ n, (Finset.range n).sum (fun k => E.proj (C k) ψ) =
      E.proj (B 0) ψ - E.proj (B n) ψ := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hCn : E.proj (C n) ψ = E.proj (B n) ψ - E.proj (B (n + 1)) ψ := by
        have h := E.proj_diff (B n) (B (n + 1)) (hB n) (hB (n + 1))
        rw [← E.proj_inter (B n) (B (n + 1)) (hB n) (hB (n + 1)),
            Set.inter_eq_right.mpr (h_anti (Nat.le_succ n))] at h
        exact congrFun (congrArg DFunLike.coe h) ψ
      rw [hCn]; abel
  -- Combine: E(B 0)ψ - E(Bₙ)ψ → E(B 0 \ A)ψ = E(B 0)ψ - E(A)ψ
  have htend_sub : Tendsto (fun n => E.proj (B 0) ψ - E.proj (B n) ψ) atTop
      (𝓝 (E.proj (B 0) ψ - E.proj A ψ)) := by
    have h_diff_eq : E.proj (B 0 \ A) ψ = E.proj (B 0) ψ - E.proj A ψ := by
      have h := E.proj_diff (B 0) A (hB 0) hA
      rw [← E.proj_inter (B 0) A (hB 0) hA, Set.inter_eq_right.mpr (hA_sub 0)] at h
      exact congrFun (congrArg DFunLike.coe h) ψ
    rw [← h_diff_eq]
    exact htend_C.congr (fun n => (h_telesc n))
  -- Extract: E(Bₙ)ψ → E(A)ψ from c - E(Bₙ)ψ → c - E(A)ψ
  have h_eq : (fun n => E.proj (B n) ψ) =
      (fun n => E.proj (B 0) ψ - (E.proj (B 0) ψ - E.proj (B n) ψ)) := by
    ext n; simp [sub_sub_cancel]
  rw [h_eq, show E.proj A ψ =
      E.proj (B 0) ψ - (E.proj (B 0) ψ - E.proj A ψ) from by simp [sub_sub_cancel]]
  exact tendsto_const_nhds.sub htend_sub



end ContinuityFromAbove

/-! ### The cross spectral measure (sesquilinear version) -/

section CrossMeasure

variable (E : ProjectionValuedMeasure H Ω)

/-- The **cross spectral measure** `μ_{ψ,φ}(B) = ⟨E(B)ψ, φ⟩`, defined
as a complex measure via polarization of the scalar measure.

We use the polarization identity:
  `⟨E(B)ψ, φ⟩ = ¼ ∑_{k=0}^{3} iᵏ ⟨E(B)(ψ + iᵏφ), ψ + iᵏφ⟩`

This is a bounded complex measure with `|μ_{ψ,φ}|(Ω) ≤ ‖ψ‖ · ‖φ‖`. -/
lemma cross_measure_polarization (ψ φ : H) (B : Set Ω) (_hB : MeasurableSet B) :
    ⟪E.proj B ψ, φ⟫_ℂ =
      (1 / 4 : ℂ) * (
        ⟪E.proj B (ψ + φ), ψ + φ⟫_ℂ
        - ⟪E.proj B (ψ - φ), ψ - φ⟫_ℂ
        - I * ⟪E.proj B (ψ + I • φ), ψ + I • φ⟫_ℂ
        + I * ⟪E.proj B (ψ - I • φ), ψ - I • φ⟫_ℂ
      ) := by
  have hI : (starRingEnd ℂ) I = -I := by
    change star I = -I
    simp [Complex.conj_I]
  simp only [map_add, map_sub, map_smul,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, hI]
  ring_nf; simp only [Complex.I_sq]
  ring

/-- Countable additivity of the cross measure in the weak sense:
`⟨E(⋃ₖ Bₖ)ψ, φ⟩ = ∑ₖ ⟨E(Bₖ)ψ, φ⟩` for pairwise disjoint `Bₖ`. -/
lemma cross_measure_sigma_additive
    (B : ℕ → Set Ω) (hB : ∀ k, MeasurableSet (B k))
    (h_disj : Pairwise fun i j => Disjoint (B i) (B j))
    (ψ φ : H) :
    Tendsto
      (fun n => (Finset.range n).sum (fun k => ⟪E.proj (B k) ψ, φ⟫_ℂ))
      atTop (𝓝 ⟪E.proj (⋃ k, B k) ψ, φ⟫_ℂ) := by
  have htend := E.proj_iUnion B hB h_disj ψ
  have h_inner := htend.inner (tendsto_const_nhds (x := φ)) (𝕜 := ℂ)
  have h_sum : ∀ n, ⟪∑ k ∈ Finset.range n, E.proj (B k) ψ, φ⟫_ℂ =
      ∑ k ∈ Finset.range n, ⟪E.proj (B k) ψ, φ⟫_ℂ := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, inner_add_left, ih, Finset.sum_range_succ]
  simp_rw [h_sum] at h_inner
  exact h_inner

end CrossMeasure

/-! ### Morphisms of PVMs -/

section Pushforward

variable {Ω' : Type*} [MeasurableSpace Ω']


open Classical in
/-- The **pushforward** of a PVM along a measurable function `f : Ω → Ω'`,
defined by `(f_* E)(B) = E(f⁻¹(B))`.

This is the mechanism for transferring spectral measures through the
Möbius map in the Cayley transform construction. -/
noncomputable def pushforward (E : ProjectionValuedMeasure H Ω) (f : Ω → Ω')
    (hf : Measurable f) : ProjectionValuedMeasure H Ω' where
  proj B := if MeasurableSet B then E.proj (f ⁻¹' B) else 0
  proj_of_not_measurable B hB := if_neg hB
  proj_self_adjoint B hB := by
    simp only [if_pos hB]; exact E.proj_self_adjoint _ (hf hB)
  proj_idempotent B hB := by
    simp only [if_pos hB]; exact E.proj_idempotent _ (hf hB)
  proj_empty := by
    simp only [if_pos MeasurableSet.empty, Set.preimage_empty, E.proj_empty]
  proj_univ := by
    simp only [if_pos MeasurableSet.univ, Set.preimage_univ, E.proj_univ]
  proj_inter B₁ B₂ h₁ h₂ := by
    simp only [if_pos h₁, if_pos h₂, if_pos (h₁.inter h₂), Set.preimage_inter]
    exact E.proj_inter _ _ (hf h₁) (hf h₂)
  proj_iUnion B hB h_disj ψ := by
    have hU : MeasurableSet (⋃ k, B k) := MeasurableSet.iUnion hB
    simp only [if_pos hU]
    have key : ∀ k, (if MeasurableSet (B k) then E.proj (f ⁻¹' B k) else 0) =
        E.proj (f ⁻¹' B k) := fun k => if_pos (hB k)
    simp only [key, Set.preimage_iUnion]
    exact E.proj_iUnion (fun k => f ⁻¹' B k)
      (fun k => hf (hB k))
      (fun i j hij => Disjoint.preimage f (h_disj hij))
      ψ


/-- Pushforward preserves the scalar measure: `μ_ψ^{f_*E} = f_*μ_ψ^E`. -/
lemma pushforward_scalarMeasure (E : ProjectionValuedMeasure H Ω)
    (f : Ω → Ω') (hf : Measurable f) (ψ : H) :
    (E.pushforward f hf).scalarMeasure ψ = Measure.map f (E.scalarMeasure ψ) := by
  ext B hB
  rw [Measure.map_apply hf hB]
  have h_proj : (E.pushforward f hf).proj B = E.proj (f ⁻¹' B) := by
    simp [pushforward, if_pos hB]
  simp only [scalarMeasure, Measure.ofMeasurable_apply _ hB,
             Measure.ofMeasurable_apply _ (hf hB), h_proj]


end Pushforward

end ProjectionValuedMeasure

/-! ### Real-valued PVMs (for self-adjoint operators) -/

section RealPVM

variable (E : ProjectionValuedMeasure H Ω)

/-- A PVM on `ℝ` — the type relevant for self-adjoint operators. We define
the **resolution of the identity** (cumulative distribution) function. -/
noncomputable def ProjectionValuedMeasure.cdf
    (E : ProjectionValuedMeasure H ℝ) (lambda : ℝ) : H →L[ℂ] H :=
  E.proj (Set.Iic lambda)

/-- Absorption: `E(B₂) ∘ E(B₁) = E(B₁)` when `B₁ ⊆ B₂`. -/
lemma proj_comp_of_subset (B₁ B₂ : Set Ω) (h₁ : MeasurableSet B₁)
    (h₂ : MeasurableSet B₂) (h_sub : B₁ ⊆ B₂) :
    (E.proj B₂).comp (E.proj B₁) = E.proj B₁ := by
  rw [← E.proj_inter B₂ B₁ h₂ h₁, Set.inter_eq_right.mpr h_sub]


/-- For nested measurable sets: `E(B₂) - E(B₁) = E(B₂ \ B₁)`. -/
lemma proj_sub_of_subset (B₁ B₂ : Set Ω) (h₁ : MeasurableSet B₁)
    (h₂ : MeasurableSet B₂) (h_sub : B₁ ⊆ B₂) :
    E.proj B₂ - E.proj B₁ = E.proj (B₂ \ B₁) := by
  have h := E.proj_diff B₂ B₁ h₂ h₁
  rw [h]; simp only [sub_right_inj]
  exact Eq.symm (proj_comp_of_subset E B₁ B₂ h₁ h₂ h_sub)

/-- The intersection of `Iic (λ₀ + 1/(n+1))` is `Iic λ₀`. -/
lemma iInter_Iic_add_inv (lambda₀ : ℝ) :
    ⋂ n : ℕ, Set.Iic (lambda₀ + 1 / (↑n + 1)) = Set.Iic lambda₀ := by
  ext x; simp only [Set.mem_iInter, Set.mem_Iic]
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hxl : 0 < x - lambda₀ := sub_pos.mpr hlt
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (x - lambda₀))
    have hn1 : (0 : ℝ) < ↑n + 1 := by positivity
    have : 1 / (↑n + 1 : ℝ) < x - lambda₀ := by
      rw [div_lt_comm₀ hn1 hxl]
      linarith
    linarith [h n]
  · intro h n
    have : (0 : ℝ) < 1 / (↑n + 1) := by positivity
    linarith

/-- Norm-monotonicity of projection differences: if `A ⊆ B ⊆ C` then
`‖E(B)ψ - E(A)ψ‖ ≤ ‖E(C)ψ - E(A)ψ‖`. -/
lemma proj_norm_diff_mono (B₁ B₂ B₃ : Set Ω) (h₁ : MeasurableSet B₁)
    (h₂ : MeasurableSet B₂) (h₃ : MeasurableSet B₃)
    (h₁₂ : B₁ ⊆ B₂) (h₂₃ : B₂ ⊆ B₃) (ψ : H) :
    ‖E.proj B₂ ψ - E.proj B₁ ψ‖ ≤ ‖E.proj B₃ ψ - E.proj B₁ ψ‖ := by
  -- E(B₂)ψ - E(B₁)ψ = E(B₂\B₁)ψ, E(B₃)ψ - E(B₁)ψ = E(B₃\B₁)ψ
  have hd₂ : E.proj B₂ ψ - E.proj B₁ ψ = E.proj (B₂ \ B₁) ψ := by
    have h := E.proj_diff B₂ B₁ h₂ h₁
    rw [← E.proj_inter B₂ B₁ h₂ h₁, Set.inter_eq_right.mpr h₁₂] at h
    exact congrFun (congrArg DFunLike.coe h.symm) ψ
  have hd₃ : E.proj B₃ ψ - E.proj B₁ ψ = E.proj (B₃ \ B₁) ψ := by
    have h := E.proj_diff B₃ B₁ h₃ h₁
    rw [← E.proj_inter B₃ B₁ h₃ h₁, Set.inter_eq_right.mpr (h₁₂.trans h₂₃)] at h
    exact congrFun (congrArg DFunLike.coe h.symm) ψ
  -- ‖E(B₂\B₁)ψ‖ ≤ ‖E(B₃\B₁)ψ‖ via norm-squared monotonicity
  have hsub : B₂ \ B₁ ⊆ B₃ \ B₁ := Set.diff_subset_diff_left h₂₃
  rw [hd₂, hd₃]
  have h_sq_le : ‖E.proj (B₂ \ B₁) ψ‖ ^ 2 ≤ ‖E.proj (B₃ \ B₁) ψ‖ ^ 2 := by
    have eq₁ : ‖E.proj (B₂ \ B₁) ψ‖ ^ 2 = (⟪E.proj (B₂ \ B₁) ψ, ψ⟫_ℂ).re := by
      have h_eq : ⟪E.proj (B₂ \ B₁) ψ, ψ⟫_ℂ = ⟪E.proj (B₂ \ B₁) ψ, E.proj (B₂ \ B₁) ψ⟫_ℂ := by
        conv_lhs => rw [show E.proj (B₂ \ B₁) ψ = (E.proj (B₂ \ B₁)).comp (E.proj (B₂ \ B₁)) ψ from
          (congrFun (congrArg DFunLike.coe (E.proj_idempotent _ (h₂.diff h₁))) ψ).symm]
        rw [ContinuousLinearMap.comp_apply,
            ← ContinuousLinearMap.adjoint_inner_right (E.proj (B₂ \ B₁)) _ ψ,
            E.proj_self_adjoint _ (h₂.diff h₁)]
      rw [h_eq, inner_self_eq_norm_sq_to_K]; norm_cast
    have eq₂ : ‖E.proj (B₃ \ B₁) ψ‖ ^ 2 = (⟪E.proj (B₃ \ B₁) ψ, ψ⟫_ℂ).re := by
      have h_eq : ⟪E.proj (B₃ \ B₁) ψ, ψ⟫_ℂ = ⟪E.proj (B₃ \ B₁) ψ, E.proj (B₃ \ B₁) ψ⟫_ℂ := by
        conv_lhs => rw [show E.proj (B₃ \ B₁) ψ = (E.proj (B₃ \ B₁)).comp (E.proj (B₃ \ B₁)) ψ from
          (congrFun (congrArg DFunLike.coe (E.proj_idempotent _ (h₃.diff h₁))) ψ).symm]
        rw [ContinuousLinearMap.comp_apply,
            ← ContinuousLinearMap.adjoint_inner_right (E.proj (B₃ \ B₁)) _ ψ,
            E.proj_self_adjoint _ (h₃.diff h₁)]
      rw [h_eq, inner_self_eq_norm_sq_to_K]; norm_cast
    rw [eq₁, eq₂]
    exact E.proj_monotone _ _ (h₂.diff h₁) (h₃.diff h₁) hsub ψ
  have h1 := norm_nonneg (E.proj (B₂ \ B₁) ψ)
  have h2 := norm_nonneg (E.proj (B₃ \ B₁) ψ)
  nlinarith [sq_nonneg (‖E.proj (B₃ \ B₁) ψ‖ - ‖E.proj (B₂ \ B₁) ψ‖)]


/-- The resolution of the identity is right-continuous in the strong operator
topology. -/
lemma ProjectionValuedMeasure.cdf_right_continuous
    (E : ProjectionValuedMeasure H ℝ) (lambda₀ : ℝ) (ψ : H) :
    Tendsto (fun lambda => E.cdf lambda ψ) (𝓝[≥] lambda₀) (𝓝 (E.cdf lambda₀ ψ)) := by
  simp only [cdf]
  -- Sequential approximation: Bₙ = Iic(λ₀ + 1/(n+1)), antitone, ⋂ = Iic λ₀
  set B : ℕ → Set ℝ := fun n => Set.Iic (lambda₀ + 1 / (↑n + 1))
  have hB_meas : ∀ k, MeasurableSet (B k) := fun _ => isClosed_Iic.measurableSet
  have hB_anti : Antitone B := by
    intro m n hmn
    apply Set.Iic_subset_Iic.mpr
    have hm : (0 : ℝ) < ↑m + 1 := by positivity
    have hn : (0 : ℝ) < ↑n + 1 := by positivity
    have : 1 / (↑n + 1 : ℝ) ≤ 1 / (↑m + 1 : ℝ) := by
      rw [div_le_div_iff₀ hn hm];
      simp only [one_mul, add_le_add_iff_right, Nat.cast_le]
      exact String.Pos.Raw.mk_le_mk.mp hmn
    linarith
  have hB_inter : ⋂ n, B n = Set.Iic lambda₀ := iInter_Iic_add_inv lambda₀
  -- Sequential convergence: E(Bₙ)ψ → E(Iic λ₀)ψ
  have htend_seq := E.proj_tendsto_of_antitone B hB_meas hB_anti ψ
  rw [hB_inter] at htend_seq
  rw [Metric.tendsto_atTop] at htend_seq
  -- ε-δ argument for 𝓝[≥] convergence
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨N, hN⟩ := htend_seq ε hε
  rw [mem_nhdsWithin]
  refine ⟨Set.Iio (lambda₀ + 1 / (↑N + 1)), isOpen_Iio,
         Set.mem_Iio.mpr (by linarith [show (0 : ℝ) < 1 / (↑N + 1) from by positivity]), ?_⟩
  intro lambda ⟨hlt, hge⟩
  show E.proj (Set.Iic lambda) ψ ∈ U
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖E.proj (Set.Iic lambda) ψ - E.proj (Set.Iic lambda₀) ψ‖
      ≤ ‖E.proj (B N) ψ - E.proj (Set.Iic lambda₀) ψ‖ :=
        proj_norm_diff_mono E (Set.Iic lambda₀) (Set.Iic lambda) (B N)
          isClosed_Iic.measurableSet isClosed_Iic.measurableSet isClosed_Iic.measurableSet
          (Set.Iic_subset_Iic.mpr hge)
          (Set.Iic_subset_Iic.mpr (le_of_lt hlt))
          ψ
    _ < ε := by have := hN N le_rfl; rwa [dist_eq_norm] at this



/-- The resolution of the identity converges to 0 as `lambda → -∞`. -/
lemma ProjectionValuedMeasure.cdf_tendsto_bot
    (E : ProjectionValuedMeasure H ℝ) (ψ : H) :
    Tendsto (fun lambda => E.cdf lambda ψ) atBot (𝓝 0) := by
  simp only [cdf]
  set B : ℕ → Set ℝ := fun n => Set.Iic (-(↑n : ℝ))
  have hB_meas : ∀ k, MeasurableSet (B k) := fun _ => isClosed_Iic.measurableSet
  have hB_anti : Antitone B := by
    intro m n hmn
    exact Set.Iic_subset_Iic.mpr (neg_le_neg (Nat.cast_le.mpr hmn))
  have hB_inter : ⋂ n, B n = ∅ := by
    ext x; simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    push Not
    obtain ⟨n, hn⟩ := exists_nat_gt (-x)
    exact ⟨n, by grind only [= Set.mem_Iic]⟩
  -- Sequential convergence: E(Bₙ)ψ → E(∅)ψ = 0
  have htend_seq := E.proj_tendsto_of_antitone B hB_meas hB_anti ψ
  rw [hB_inter, E.proj_empty, ContinuousLinearMap.zero_apply] at htend_seq
  rw [Metric.tendsto_atTop] at htend_seq
  -- Lift to filter convergence along atBot
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := htend_seq ε hε
  apply eventually_atBot.mpr
  refine ⟨-(↑N : ℝ), fun lambda hle => ?_⟩
  rw [dist_eq_norm, sub_zero]
  have h_sub : Set.Iic lambda ⊆ B N := Set.Iic_subset_Iic.mpr hle
  calc ‖E.proj (Set.Iic lambda) ψ‖
      = ‖E.proj (Set.Iic lambda) ψ - E.proj ∅ ψ‖ := by
        rw [E.proj_empty, ContinuousLinearMap.zero_apply, sub_zero]
    _ ≤ ‖E.proj (B N) ψ - E.proj ∅ ψ‖ :=
        proj_norm_diff_mono E ∅ (Set.Iic lambda) (B N)
          MeasurableSet.empty isClosed_Iic.measurableSet isClosed_Iic.measurableSet
          (Set.empty_subset _) h_sub ψ
    _ = ‖E.proj (B N) ψ‖ := by
        rw [E.proj_empty, ContinuousLinearMap.zero_apply, sub_zero]
    _ < ε := by
        have := hN N le_rfl; rwa [dist_eq_norm, sub_zero] at this

/-- The resolution of the identity converges to `ψ` as `lambda → +∞`. -/
lemma ProjectionValuedMeasure.cdf_tendsto_top
    (E : ProjectionValuedMeasure H ℝ) (ψ : H) :
    Tendsto (fun lambda => E.cdf lambda ψ) atTop (𝓝 ψ) := by
  simp only [cdf]
  -- Strategy: E(Iic λ)ψ = ψ - E((Iic λ)ᶜ)ψ, show the complement part → 0
  -- Antitone complements: Dₙ = (Iic n)ᶜ
  set D : ℕ → Set ℝ := fun n => (Set.Iic (↑n : ℝ))ᶜ
  have hD_meas : ∀ k, MeasurableSet (D k) := fun _ => isClosed_Iic.measurableSet.compl
  have hD_anti : Antitone D := by
    intro m n hmn
    exact Set.compl_subset_compl.mpr (Set.Iic_subset_Iic.mpr (Nat.cast_le.mpr hmn))
  have hD_inter : ⋂ n, D n = ∅ := by
    ext x; constructor
    · intro hx
      have : ∀ n : ℕ, (↑n : ℝ) < x := by
        intro n
        have := Set.mem_iInter.mp hx n
        exact not_le.mp this
      obtain ⟨n, hn⟩ := exists_nat_gt x
      linarith [this n]
    · simp only [Set.mem_empty_iff_false, Set.mem_iInter, IsEmpty.forall_iff]
  -- E(Dₙ)ψ → 0
  have htend_D := E.proj_tendsto_of_antitone D hD_meas hD_anti ψ
  rw [hD_inter, E.proj_empty, ContinuousLinearMap.zero_apply] at htend_D
  rw [Metric.tendsto_atTop] at htend_D
  -- Complement formula: E(Iic λ)ψ = ψ - E((Iic λ)ᶜ)ψ
  have h_compl : ∀ lambda : ℝ,
      E.proj (Set.Iic lambda) ψ = ψ - E.proj (Set.Iic lambda)ᶜ ψ := by
    intro lambda
    have h := congrFun (congrArg DFunLike.coe
      (E.proj_compl (Set.Iic lambda) isClosed_Iic.measurableSet)) ψ
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at h
    -- h : E⦃(Iic λ)ᶜ⦄ ψ = ψ - E⦃Iic λ⦄ ψ
    rw [h, sub_sub_cancel]
  -- ε-δ argument
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := htend_D ε hε
  apply eventually_atTop.mpr
  refine ⟨(↑N : ℝ), fun lambda hle => ?_⟩
  rw [dist_eq_norm]
  -- Rewrite: E(Iic λ)ψ - ψ = -E((Iic λ)ᶜ)ψ
  have h_neg : E.proj (Set.Iic lambda) ψ - ψ = -(E.proj (Set.Iic lambda)ᶜ ψ) := by
    rw [h_compl lambda]; abel
  rw [h_neg, norm_neg]
  -- Squeeze: (Iic λ)ᶜ ⊆ (Iic N)ᶜ = D N when λ ≥ N
  have h_sub : (Set.Iic lambda)ᶜ ⊆ D N :=
    Set.compl_subset_compl.mpr (Set.Iic_subset_Iic.mpr hle)
  calc ‖E.proj (Set.Iic lambda)ᶜ ψ‖
      = ‖E.proj (Set.Iic lambda)ᶜ ψ - E.proj ∅ ψ‖ := by
        rw [E.proj_empty, ContinuousLinearMap.zero_apply, sub_zero]
    _ ≤ ‖E.proj (D N) ψ - E.proj ∅ ψ‖ :=
        proj_norm_diff_mono E ∅ ((Set.Iic lambda)ᶜ) (D N)
          MeasurableSet.empty isClosed_Iic.measurableSet.compl
          isClosed_Iic.measurableSet.compl
          (Set.empty_subset _) h_sub ψ
    _ = ‖E.proj (D N) ψ‖ := by
        rw [E.proj_empty, ContinuousLinearMap.zero_apply, sub_zero]
    _ < ε := by
        have := hN N le_rfl; rwa [dist_eq_norm, sub_zero] at this

end RealPVM

end QuantumMechanics.SpectralTheory

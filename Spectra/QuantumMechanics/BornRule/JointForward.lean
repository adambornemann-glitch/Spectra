/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.Joint
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Algebra.Star.StarProjection
/-!
# Joint spectral measures — the forward construction (the multivariate spectral theorem)

This file builds the forward direction of the relational Born-rule layer, the genuine new content
that `BornRule.Joint` (sorry-free, easy/backward half) leaves open.  All `sorry`-free and axiom-clean.

* `stronglyCommute_iff_jointPVM` — the corrected equivalence.  Its **backward** half is the proved
  `stronglyCommute_of_jointPVM` (in `BornRule.Joint`); the **forward** half — the genuine new
  construction (Goal 2) — produces a joint projective PVM on `ℝ²` from commuting PVMs by Carathéodory
  extension of the bimeasure content `μ_ξ(S×T) = ⟪ξ, E_A(S)E_B(T)ξ⟫` (`jointScalarMeasure`), with the
  operator field recovered by polarization (`jointEffect`).  ∅-continuity of the content is the
  multivariate spectral theorem's core (`jointContentRing_tendsto_empty`, Route T / tightness).
* `jointBornMeasure_correlation` — the correlation identity `∫ xy dμ_ξ = ⟪ξ, A(Bξ)⟫.re` (Goal 3),
  the 2-D analogue of `weak_first_moment`: truncate `xy` to `[-N,N]²`, identify the truncated integral
  with the operator product `Φ_A(x·1_N)Φ_B(y·1_N)` (Step A, `joint_product_form`), collapse it to
  `E_A([-N,N])E_B([-N,N])(A(Bξ))` (Step C, `joint_truncated_vector`), and pass to the limit.  The bridge
  to Bell/CHSH.
-/

open MeasureTheory Complex Spectra Filter Topology
open scoped InnerProductSpace
open Spectra.QuantumMechanics.Observable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Reusable PVM σ-additivity infrastructure (general, candidate for `ProjValMeasure.Basic`)

These are generic facts about any `ProjValMeasure`, used below to assemble the joint content's
countable additivity (and reusable elsewhere): the projection of a set difference, finite
additivity over a `Finset`, strong (norm) convergence of partial unions via measure
continuity-from-above, and the finite Pythagoras for a pairwise-orthogonal family. -/

namespace Spectra.ProjValMeasure

/-- Projection of a set difference, `E(A \ B) = E(A) − E(B)` for `B ⊆ A`. -/
lemma proj_diff (P : ProjValMeasure H) {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBA : B ⊆ A) :
    P.proj (A \ B) (hA.diff hB) = P.proj A hA - P.proj B hB := by
  have key : P.proj B hB + P.proj (A \ B) (hA.diff hB) = P.proj A hA := by
    rw [← P.proj_union hB (hA.diff hB) disjoint_sdiff_self_right,
      P.proj_congr (Set.union_diff_cancel hBA) (hB.union (hA.diff hB)) hA]
  linear_combination (norm := module) key

/-- Finite additivity of the projections over a `Finset` of pairwise-disjoint measurable sets. -/
lemma proj_biUnion (P : ProjValMeasure H) {ι : Type*} {T : ι → Set ℝ}
    (hT : ∀ i, MeasurableSet (T i)) :
    ∀ (s : Finset ι), (↑s : Set ι).PairwiseDisjoint T →
      ∀ (hU : MeasurableSet (⋃ i ∈ s, T i)),
      P.proj (⋃ i ∈ s, T i) hU = ∑ i ∈ s, P.proj (T i) (hT i) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
    intro _ hU
    rw [Finset.sum_empty]
    calc P.proj (⋃ i ∈ (∅ : Finset ι), T i) hU
        = P.proj ∅ MeasurableSet.empty := P.proj_congr (by simp) hU MeasurableSet.empty
      _ = 0 := P.proj_empty
  | @insert a s ha ih =>
    intro hd hU
    have hsU : MeasurableSet (⋃ i ∈ s, T i) := Finset.measurableSet_biUnion s fun i _ => hT i
    have hdisj : Disjoint (T a) (⋃ i ∈ s, T i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      refine hd ?_ ?_ (fun h => ha (h ▸ hi)) <;> simp [hi]
    have hsub : (↑s : Set ι).PairwiseDisjoint T :=
      hd.subset (Finset.coe_subset.mpr (Finset.subset_insert a s))
    calc P.proj (⋃ i ∈ insert a s, T i) hU
        = P.proj (T a ∪ ⋃ i ∈ s, T i) ((hT a).union hsU) :=
          P.proj_congr (Finset.set_biUnion_insert a s T) hU ((hT a).union hsU)
      _ = P.proj (T a) (hT a) + P.proj (⋃ i ∈ s, T i) hsU := P.proj_union (hT a) hsU hdisj
      _ = P.proj (T a) (hT a) + ∑ i ∈ s, P.proj (T i) (hT i) := by rw [ih hsub hsU]
      _ = ∑ i ∈ insert a s, P.proj (T i) (hT i) := by rw [Finset.sum_insert ha]

/-- The increasing partial unions `⋃_{i<N} Tᵢ` exhaust `⋃ₙ Tₙ`. -/
lemma iUnion_range_biUnion (T : ℕ → Set ℝ) :
    ⋃ N, ⋃ i ∈ Finset.range N, T i = ⋃ n, T n := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun N => Set.iUnion₂_subset fun i _ => Set.subset_iUnion T i
  · refine Set.iUnion_subset fun n => ?_
    exact Set.subset_iUnion_of_subset (n + 1)
      (Set.subset_iUnion₂_of_subset n (Finset.self_mem_range_succ n) (le_refl _))

/-- Strong (norm) convergence: `E(⋃_{i<N} Tᵢ) ξ → E(⋃ₙ Tₙ) ξ`, from measure continuity-from-above
of the diagonal measure on the antitone tails. -/
lemma tendsto_proj_biUnion (P : ProjValMeasure H) {T : ℕ → Set ℝ} (hT : ∀ n, MeasurableSet (T n))
    (ξ : H) :
    Tendsto (fun N => P.proj (⋃ i ∈ Finset.range N, T i)
        (Finset.measurableSet_biUnion _ fun i _ => hT i) ξ) atTop
      (𝓝 (P.proj (⋃ n, T n) (MeasurableSet.iUnion hT) ξ)) := by
  haveI := P.diag_finite ξ
  set U := ⋃ n, T n with hU
  have hUm : MeasurableSet U := MeasurableSet.iUnion hT
  set RN : ℕ → Set ℝ := fun N => ⋃ i ∈ Finset.range N, T i with hRN
  have hRNm : ∀ N, MeasurableSet (RN N) := fun N => Finset.measurableSet_biUnion _ fun i _ => hT i
  have hsub : ∀ N, RN N ⊆ U := fun N => Set.iUnion₂_subset fun i _ => Set.subset_iUnion T i
  set D : ℕ → Set ℝ := fun N => U \ RN N with hD
  have hDm : ∀ N, MeasurableSet (D N) := fun N => hUm.diff (hRNm N)
  have hRNmono : ∀ {N M : ℕ}, N ≤ M → RN N ⊆ RN M := by
    intro N M hNM x hx
    simp only [hRN, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hNM), hxi⟩
  have hanti : Antitone D := fun N M hNM => Set.diff_subset_diff_right (hRNmono hNM)
  have hint : ⋂ N, D N = ∅ := by
    rw [hD, ← Set.diff_iUnion, iUnion_range_biUnion T, ← hU, Set.diff_self]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ N, ‖P.proj (RN N) (hRNm N) ξ - P.proj U hUm ξ‖
      = Real.sqrt (((P.diag ξ) (D N)).toReal) := by
    intro N
    have hpd : P.proj (D N) (hDm N) = P.proj U hUm - P.proj (RN N) (hRNm N) :=
      P.proj_diff hUm (hRNm N) (hsub N)
    have hneg : P.proj (RN N) (hRNm N) ξ - P.proj U hUm ξ = -(P.proj (D N) (hDm N) ξ) := by
      rw [hpd, ContinuousLinearMap.sub_apply]; abel
    rw [hneg, norm_neg, ← Real.sqrt_sq (norm_nonneg (P.proj (D N) (hDm N) ξ)),
      P.norm_sq_proj_apply]
  have hmeas : Tendsto (fun N => ((P.diag ξ) (D N)).toReal) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P.diag ξ)
      (fun N => (hDm N).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hint, measure_empty] at h
    have h2 := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp h
    exact h2
  have hsqrt : Tendsto (fun N => Real.sqrt (((P.diag ξ) (D N)).toReal)) atTop (𝓝 0) := by
    have := hmeas.sqrt; rwa [Real.sqrt_zero] at this
  exact hsqrt.congr fun N => (hnorm N).symm

omit [CompleteSpace H] in
/-- Finite Pythagoras for a pairwise-orthogonal `Finset` family. -/
lemma norm_sum_sq_orthogonal {ι : Type*} (s : Finset ι) (v : ι → H)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hperp : ⟪v a, ∑ i ∈ s, v i⟫_ℂ = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun i hi => ho a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
    have hrestrict : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℂ = 0 :=
      fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    rw [Finset.sum_insert ha, Finset.sum_insert ha, norm_add_sq (𝕜 := ℂ), hperp]
    simp only [map_zero, mul_zero, add_zero]
    rw [ih hrestrict]

/-- For a star projection (a self-adjoint idempotent — an orthogonal projection) `P`, the squared
norm of `P ξ` is the real part of the diagonal `⟪ξ, P ξ⟫`.  A general Hilbert-space fact (the
`IsStarProjection` analogue of `ProjValMeasure.norm_sq_proj_apply`); used below to bridge the norm²
form of the σ-additivity crux to the bimeasure value. -/
lemma norm_sq_apply_of_isStarProjection {P : H →L[ℂ] H} (hP : IsStarProjection P) (ξ : H) :
    ‖P ξ‖ ^ 2 = (⟪ξ, P ξ⟫_ℂ).re := by
  have h1 : ⟪P ξ, P ξ⟫_ℂ = ⟪ξ, P ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hP.isSelfAdjoint.adjoint_eq,
      ← ContinuousLinearMap.mul_apply, hP.isIdempotentElem.eq]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), h1, RCLike.re_eq_complex_re]

end Spectra.ProjValMeasure

/-! ## Axis grids — the Boolean sign-atoms of a finite family of measurable sets

A reusable refinement primitive for the joint-measure grid additivity.  The **sign atom** of a finite
indexed family `S : ι → Set ℝ` for a sign vector `c : ι → Bool` is the cell
`⋂ i, (S i  or  (S i)ᶜ)` lying in `S i` exactly where `c i = true`.  The sign atoms are pairwise
disjoint and measurable, and each `S j` is the disjoint union of the atoms with `c j = true` — so a
spectral projection of `S j` is a finite sum of projections of atoms (`proj_eq_sum_signAtom`).  This
turns a product `E_A(S)·E_B(T)` into a double sum over a common axis grid. -/

namespace Spectra.AxisGrid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sign atom of `S : ι → Set ℝ` for the sign vector `c`: the points in `S i` exactly where
`c i = true`. -/
def signAtom (S : ι → Set ℝ) (c : ι → Bool) : Set ℝ :=
  ⋂ i, if c i = true then S i else (S i)ᶜ

omit [Fintype ι] [DecidableEq ι] in
lemma mem_signAtom {S : ι → Set ℝ} (x : ℝ) (c : ι → Bool) :
    x ∈ signAtom S c ↔ ∀ i, (c i = true ↔ x ∈ S i) := by
  simp only [signAtom, Set.mem_iInter]
  refine forall_congr' fun i => ?_
  by_cases hc : c i = true <;> simp [hc, Set.mem_compl_iff]

omit [DecidableEq ι] in
lemma signAtom_measurableSet {S : ι → Set ℝ} (hS : ∀ i, MeasurableSet (S i)) (c : ι → Bool) :
    MeasurableSet (signAtom S c) := by
  refine MeasurableSet.iInter fun i => ?_
  by_cases hc : c i = true
  · simpa [hc] using hS i
  · simpa [hc] using (hS i).compl

omit [Fintype ι] [DecidableEq ι] in
lemma signAtom_pairwiseDisjoint (S : ι → Set ℝ) :
    Pairwise (Function.onFun Disjoint (signAtom S)) := by
  intro c c' hcc'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hcc'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  rw [mem_signAtom] at hx hx'
  exact hi (Bool.eq_iff_iff.mpr ((hx i).trans (hx' i).symm))

/-- Each `S j` is the (disjoint) union of the sign atoms whose `j`-coordinate is positive. -/
lemma signAtom_biUnion_eq {S : ι → Set ℝ} (j : ι) :
    ⋃ c ∈ Finset.univ.filter (fun c : ι → Bool => c j = true), signAtom S c = S j := by
  classical
  ext x
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, mem_signAtom]
  constructor
  · rintro ⟨c, hcj, hc⟩
    exact (hc j).mp hcj
  · intro hx
    refine ⟨fun i => decide (x ∈ S i), by simpa using hx, fun i => ?_⟩
    simp [decide_eq_true_eq]

/-- **The projection refinement.**  A spectral projection of `S j` is the finite sum of the
projections of the sign atoms with positive `j`-coordinate (`proj_biUnion` over the disjoint atoms). -/
lemma proj_eq_sum_signAtom (P : Spectra.ProjValMeasure H) {S : ι → Set ℝ}
    (hS : ∀ i, MeasurableSet (S i)) (j : ι) (hSj : MeasurableSet (S j)) :
    P.proj (S j) hSj = ∑ c ∈ Finset.univ.filter (fun c : ι → Bool => c j = true),
      P.proj (signAtom S c) (signAtom_measurableSet hS c) := by
  classical
  have hU : MeasurableSet (⋃ c ∈ Finset.univ.filter (fun c : ι → Bool => c j = true), signAtom S c) :=
    Finset.measurableSet_biUnion _ fun c _ => signAtom_measurableSet hS c
  rw [← P.proj_congr (signAtom_biUnion_eq j) hU hSj,
    P.proj_biUnion (fun c => signAtom_measurableSet hS c) _
      (fun c _ c' _ hcc' => signAtom_pairwiseDisjoint S hcc') hU]

open Classical in
/-- **A point lies in exactly one set of a disjoint cover.**  For a `Fintype`-indexed family `R` of
pairwise-disjoint sets and a point `p`, the number of indices `k` with `p ∈ R k` is `1` if `p` is in
the union and `0` otherwise. -/
lemma card_filter_mem_eq_ite {κ X : Type*} [Fintype κ] (R : κ → Set X)
    (hR : Pairwise (Function.onFun Disjoint R)) (p : X) :
    (Finset.univ.filter (fun k => p ∈ R k)).card = if p ∈ ⋃ k, R k then 1 else 0 := by
  by_cases hp : p ∈ ⋃ k, R k
  · rw [if_pos hp, Finset.card_eq_one]
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    refine ⟨k, ?_⟩
    ext k'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun hk' => ?_, fun h => h ▸ hk⟩
    by_contra hne
    exact absurd hk (Set.disjoint_left.mp (hR hne) hk')
  · rw [if_neg hp, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun k _ hpk => hp (Set.mem_iUnion.mpr ⟨k, hpk⟩)

end Spectra.AxisGrid

/-! ## The measurable-rectangle semiring of `ℝ × ℝ`

The target measure `μ_ξ` is built from its rectangle values via Carathéodory
(`MeasureTheory.AddContent.measure`).  Step one is the semiring of measurable rectangles. -/

/-- The measurable rectangles of `ℝ × ℝ`. -/
def jointRectangles : Set (Set (ℝ × ℝ)) :=
  {R | ∃ S T : Set ℝ, MeasurableSet S ∧ MeasurableSet T ∧ R = S ×ˢ T}

/-- The measurable rectangles form a set semiring: closed under intersection, and a rectangle minus
a rectangle is the disjoint union of two rectangles (`(S₁\S₂)×T₁ ⊔ (S₁∩S₂)×(T₁\T₂)`). -/
lemma isSetSemiring_jointRectangles : MeasureTheory.IsSetSemiring jointRectangles where
  empty_mem := ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, by simp⟩
  inter_mem := by
    rintro _ ⟨S₁, T₁, hS₁, hT₁, rfl⟩ _ ⟨S₂, T₂, hS₂, hT₂, rfl⟩
    exact ⟨S₁ ∩ S₂, T₁ ∩ T₂, hS₁.inter hS₂, hT₁.inter hT₂, Set.prod_inter_prod⟩
  diff_eq_sUnion' := by
    classical
    rintro _ ⟨S₁, T₁, hS₁, hT₁, rfl⟩ _ ⟨S₂, T₂, hS₂, hT₂, rfl⟩
    refine ⟨{(S₁ \ S₂) ×ˢ T₁, (S₁ ∩ S₂) ×ˢ (T₁ \ T₂)}, ?_, ?_, ?_⟩
    · intro R hR
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hR
      rcases hR with rfl | rfl
      · exact ⟨S₁ \ S₂, T₁, hS₁.diff hS₂, hT₁, rfl⟩
      · exact ⟨S₁ ∩ S₂, T₁ \ T₂, hS₁.inter hS₂, hT₁.diff hT₂, rfl⟩
    · simp only [Finset.coe_insert, Finset.coe_singleton]
      rw [Set.pairwiseDisjoint_insert]
      refine ⟨Set.pairwiseDisjoint_singleton _ _, ?_⟩
      intro c hc _
      simp only [Set.mem_singleton_iff] at hc; subst hc
      simp only [id_eq]
      rw [Set.disjoint_left]
      rintro ⟨x, y⟩ ⟨hx, _⟩ ⟨hx', _⟩
      exact hx.2 hx'.2
    · rw [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton]
      ext ⟨x, y⟩
      simp only [Set.mem_diff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff]
      tauto

namespace Spectra.QuantumMechanics.BornRule

open PVM Spectra.ProjValMeasure Spectra.AxisGrid

/-! ## Foundation for the forward (Goal 2) construction — Route B

The forward direction builds, for each `ξ`, the joint scalar measure `μ_ξ` on `ℝ²` with the
rectangle values `μ_ξ(S ×ˢ T) = ⟪ξ, E_A(S)·E_B(T) ξ⟫.re` (the genuine bimeasure — **not** the
product of marginals, which `exists_coupling_always` shows is vacuous), extends it via
`MeasureTheory.AddContent.measure`, and recovers the operator field by polarization.

The load-bearing reduction below makes the bimeasure's countable additivity free: for a *fixed*
`T`, the rectangle value `S ↦ ⟪ξ, E_A(S)·E_B(T) ξ⟫` is *literally* the already-constructed 1-D
spectral measure of `A` at the vector `E_B(T) ξ`.  (And symmetrically in `S`.)  These are
`sorry`-free; only the joint Carathéodory extension and the operator-field polarization remain. -/

/-- **The rectangle value is a 1-D spectral measure (A-slot).**  For strongly-commuting `A, B`,
`⟪ξ, E_A(S)·E_B(T) ξ⟫ = μ^A_{E_B(T)ξ}(S)`, where `μ^A_v = A.spectralPVM.diag v` is the existing
Born/spectral measure.  Hence, for fixed `T`, the bimeasure is countably additive in `S` for free.
Proof: `E_A(S)·E_B(T) = E_B(T)·E_A(S)·E_B(T)` (commute + `E_B(T)` idempotent), then move a
self-adjoint `E_B(T)` across the inner product and read off `inner_proj`. -/
theorem jointRect_inner_eq_diag_left (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (ξ : H) :
    ⟪ξ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ
      = (((A.spectralPVM.diag (B.spectralPVM.proj T hT ξ)) S).toReal : ℂ) := by
  set EA := A.spectralPVM.proj S hS
  set EB := B.spectralPVM.proj T hT
  have hcomm : EA * EB = EB * EA := (hSC S T hS hT).eq
  have hidem : EB * EB = EB := B.spectralPVM.proj_idem T hT
  have hadj : ContinuousLinearMap.adjoint EB = EB := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact B.spectralPVM.isSelfAdjoint_proj T hT
  calc ⟪ξ, (EA * EB) ξ⟫_ℂ
      = ⟪ξ, (EB * EA * EB) ξ⟫_ℂ := by conv_lhs => rw [← hidem, ← mul_assoc, hcomm]
    _ = ⟪ξ, EB ((EA * EB) ξ)⟫_ℂ := by rw [mul_assoc, ContinuousLinearMap.mul_apply]
    _ = ⟪EB ξ, (EA * EB) ξ⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_left EB ((EA * EB) ξ) ξ, hadj]
    _ = (((A.spectralPVM.diag (EB ξ)) S).toReal : ℂ) := by
        rw [ContinuousLinearMap.mul_apply]; exact A.spectralPVM.inner_proj S hS (EB ξ)

/-- **The rectangle value is nonnegative real.**  `⟪ξ, E_A(S)·E_B(T) ξ⟫` is a nonnegative real
(it equals `μ^A_{E_B(T)ξ}(S).toReal`), so the content `ENNReal.ofReal` of its real part is honest.
Needed for the `AddContent` positivity. -/
theorem jointRect_re_nonneg (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (ξ : H) :
    0 ≤ (⟪ξ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ).re := by
  rw [jointRect_inner_eq_diag_left A B hSC hS hT ξ, Complex.ofReal_re]
  exact ENNReal.toReal_nonneg

/-- **Orthogonality — the heart of the bimeasure's countable additivity.**  For disjoint `T₁, T₂`,
the vectors `E_A(S)·E_B(T₁)ξ` and `E_A(S)·E_B(T₂)ξ` are orthogonal.  (Cross terms vanish:
`E_B(T₁)·E_B(T₂) = E_B(T₁ ∩ T₂) = E_B(∅) = 0`, using commutation + idempotence + self-adjointness.)
Pythagoras then turns this into σ-additivity of the rectangle content in the `T`-slot:
`‖E_A(S)·E_B(⋃ Tₙ)ξ‖² = ∑ₙ ‖E_A(S)·E_B(Tₙ)ξ‖²`. -/
theorem jointRect_orthogonal (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S T₁ T₂ : Set ℝ} (hS : MeasurableSet S) (hT₁ : MeasurableSet T₁)
    (hT₂ : MeasurableSet T₂) (hd : Disjoint T₁ T₂) (ξ : H) :
    ⟪(A.spectralPVM.proj S hS * B.spectralPVM.proj T₁ hT₁) ξ,
      (A.spectralPVM.proj S hS * B.spectralPVM.proj T₂ hT₂) ξ⟫_ℂ = 0 := by
  set EA := A.spectralPVM.proj S hS
  set EB1 := B.spectralPVM.proj T₁ hT₁
  set EB2 := B.spectralPVM.proj T₂ hT₂
  have hsaA : ∀ u w : H, ⟪EA u, w⟫_ℂ = ⟪u, EA w⟫_ℂ := fun u w => by
    rw [← ContinuousLinearMap.adjoint_inner_right,
      (A.spectralPVM.isSelfAdjoint_proj S hS).adjoint_eq]
  have hsaB1 : ∀ u w : H, ⟪EB1 u, w⟫_ℂ = ⟪u, EB1 w⟫_ℂ := fun u w => by
    rw [← ContinuousLinearMap.adjoint_inner_right,
      (B.spectralPVM.isSelfAdjoint_proj T₁ hT₁).adjoint_eq]
  have hEAidem : ∀ z : H, EA (EA z) = EA z := fun z => by
    rw [← ContinuousLinearMap.mul_apply, A.spectralPVM.proj_idem S hS]
  have hcomm : ∀ y : H, EB1 (EA y) = EA (EB1 y) := fun y => by
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, (hSC S T₁ hS hT₁).eq.symm]
  have hzero : EB1 (EB2 ξ) = 0 := by
    rw [← ContinuousLinearMap.mul_apply, B.spectralPVM.proj_inter T₁ T₂ hT₁ hT₂,
      B.spectralPVM.proj_congr (Set.disjoint_iff_inter_eq_empty.mp hd) (hT₁.inter hT₂)
        MeasurableSet.empty, B.spectralPVM.proj_empty, ContinuousLinearMap.zero_apply]
  calc ⟪(EA * EB1) ξ, (EA * EB2) ξ⟫_ℂ
      = ⟪EB1 ξ, EA (EA (EB2 ξ))⟫_ℂ := by
        rw [ContinuousLinearMap.mul_apply EA EB1, ContinuousLinearMap.mul_apply EA EB2, hsaA]
    _ = ⟪EB1 ξ, EA (EB2 ξ)⟫_ℂ := by rw [hEAidem]
    _ = ⟪ξ, EB1 (EA (EB2 ξ))⟫_ℂ := hsaB1 _ _
    _ = ⟪ξ, EA (EB1 (EB2 ξ))⟫_ℂ := by rw [hcomm]
    _ = 0 := by rw [hzero, map_zero, inner_zero_right]

/-- **σ-additivity of the joint rectangle content** (in the `T`-slot) — the crux of G2.2, fully
assembled.  For pairwise-disjoint measurable `Tₙ`,
`‖E_A(S)·E_B(⋃ₙ Tₙ)ξ‖² = ∑ₙ ‖E_A(S)·E_B(Tₙ)ξ‖²`, i.e. the bimeasure `S × · ↦ ⟪ξ,E_A(S)E_B(·)ξ⟫` is
countably additive.  Proof: finite Pythagoras (`norm_sum_sq_orthogonal` via `jointRect_orthogonal`)
+ finite additivity (`proj_biUnion`) collapse the partial sums to `E_A(S)·E_B(⋃_{i<N} Tᵢ)ξ`, which
converge (`tendsto_proj_biUnion`, measure continuity-from-above); `hasSum_iff_tendsto_nat_of_nonneg`
closes it.  This is the measure-theoretic heart that feeds the `AddContent` extension. -/
theorem jointContent_hasSum (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {S : Set ℝ} (hS : MeasurableSet S) {T : ℕ → Set ℝ} (hT : ∀ n, MeasurableSet (T n))
    (hd : Pairwise (fun i j => Disjoint (T i) (T j))) (ξ : H) :
    HasSum (fun n => ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj (T n) (hT n)) ξ‖ ^ 2)
      (‖(A.spectralPVM.proj S hS
          * B.spectralPVM.proj (⋃ n, T n) (MeasurableSet.iUnion hT)) ξ‖ ^ 2) := by
  set EA := A.spectralPVM.proj S hS with hEA
  have hUN : ∀ N, MeasurableSet (⋃ i ∈ Finset.range N, T i) :=
    fun N => Finset.measurableSet_biUnion _ fun i _ => hT i
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => sq_nonneg _)]
  have hpd : ∀ N, ∑ i ∈ Finset.range N, (EA * B.spectralPVM.proj (T i) (hT i)) ξ
      = (EA * B.spectralPVM.proj (⋃ i ∈ Finset.range N, T i) (hUN N)) ξ := by
    intro N
    have hbi := B.spectralPVM.proj_biUnion hT (Finset.range N)
      (fun i _ j _ hij => hd hij) (hUN N)
    rw [← ContinuousLinearMap.sum_apply, ← Finset.mul_sum, ← hbi]
  have hpyth : ∀ N, ‖(EA * B.spectralPVM.proj (⋃ i ∈ Finset.range N, T i) (hUN N)) ξ‖ ^ 2
      = ∑ i ∈ Finset.range N, ‖(EA * B.spectralPVM.proj (T i) (hT i)) ξ‖ ^ 2 := by
    intro N
    rw [← hpd]
    exact norm_sum_sq_orthogonal (Finset.range N)
      (fun i => (EA * B.spectralPVM.proj (T i) (hT i)) ξ)
      (fun i _ j _ hij => jointRect_orthogonal A B hSC hS (hT i) (hT j) (hd hij) ξ)
  simp only [← hpyth]
  have hconv : Tendsto (fun N => (EA * B.spectralPVM.proj (⋃ i ∈ Finset.range N, T i) (hUN N)) ξ)
      atTop (𝓝 ((EA * B.spectralPVM.proj (⋃ n, T n) (MeasurableSet.iUnion hT)) ξ)) := by
    simp only [ContinuousLinearMap.mul_apply]
    exact (EA.continuous.tendsto _).comp (B.spectralPVM.tendsto_proj_biUnion hT ξ)
  exact hconv.norm.pow 2

/-! ## G2.1 — the rectangle effect is an orthogonal projection

The operator the joint PVM will assign to the rectangle `S × T` is `E_A(S)·E_B(T)`.  Strong
commutativity makes this product of two commuting projections itself a projection (self-adjoint and
idempotent), and the two rectangle effects compose like the spectral projections (`jointRect_mul`,
the rectangle case of `IsProjective`).  The payoff is the **content bridge**
`jointRect_norm_sq_eq_diag`: because the effect is a projection, the norm² content summed by
`jointContent_hasSum` *is* the bimeasure value `⟪ξ, E_A(S)E_B(T)ξ⟫`, so the σ-additivity crux reads
off directly as σ-additivity of the bimeasure (`jointContent_hasSum_diag`) — the form the
`AddContent` extension (G2.2) consumes.

Scope: the σ-additivity delivered here is *one-variable* (the `T`-slot, for a fixed `S`, in `.toReal`
form).  The `ℝ≥0∞` lift and the finite additivity over *arbitrary* disjoint rectangle partitions
(the `AddContent.sUnion'` obligation, via grid/atom refinement) are the remaining G2.2 nut. -/

/-- **G2.1 — the rectangle effect is an orthogonal projection.**  For strongly-commuting `A, B`, the
operator `E_A(S)·E_B(T)` is self-adjoint and idempotent (`IsStarProjection`): the product of the two
*commuting* projections is again a projection.  This is the effect the joint PVM assigns to the
rectangle `S × T`. -/
theorem jointRect_isStarProjection (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    IsStarProjection (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) :=
  IsStarProjection.mul
    ⟨A.spectralPVM.proj_idem S hS, A.spectralPVM.isSelfAdjoint_proj S hS⟩
    ⟨B.spectralPVM.proj_idem T hT, B.spectralPVM.isSelfAdjoint_proj T hT⟩
    (hSC S T hS hT)

/-- **G2.1 — rectangle multiplicativity.**  The rectangle effects compose like the spectral
projections: `(E_A(S₁)E_B(T₁))·(E_A(S₂)E_B(T₂)) = E_A(S₁∩S₂)·E_B(T₁∩T₂)`.  Strong commutativity is
exactly what lets the inner `E_B(T₁)` and `E_A(S₂)` swap; `proj_inter` closes each slot.  This is the
`proj_inter` of the joint PVM on rectangles — the rectangle case of `IsProjective` (G2.4). -/
theorem jointRect_mul (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {S₁ S₂ T₁ T₂ : Set ℝ} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂) :
    (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁)
        * (A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂)
      = A.spectralPVM.proj (S₁ ∩ S₂) (hS₁.inter hS₂)
        * B.spectralPVM.proj (T₁ ∩ T₂) (hT₁.inter hT₂) := by
  have hcomm : B.spectralPVM.proj T₁ hT₁ * A.spectralPVM.proj S₂ hS₂
      = A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₁ hT₁ := (hSC S₂ T₁ hS₂ hT₁).eq.symm
  calc (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁)
          * (A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂)
      = A.spectralPVM.proj S₁ hS₁ * (B.spectralPVM.proj T₁ hT₁ * A.spectralPVM.proj S₂ hS₂)
          * B.spectralPVM.proj T₂ hT₂ := by simp only [mul_assoc]
    _ = A.spectralPVM.proj S₁ hS₁ * (A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₁ hT₁)
          * B.spectralPVM.proj T₂ hT₂ := by rw [hcomm]
    _ = (A.spectralPVM.proj S₁ hS₁ * A.spectralPVM.proj S₂ hS₂)
          * (B.spectralPVM.proj T₁ hT₁ * B.spectralPVM.proj T₂ hT₂) := by simp only [mul_assoc]
    _ = A.spectralPVM.proj (S₁ ∩ S₂) (hS₁.inter hS₂)
          * B.spectralPVM.proj (T₁ ∩ T₂) (hT₁.inter hT₂) := by
        rw [A.spectralPVM.proj_inter, B.spectralPVM.proj_inter]

/-- **G2.1 — the content bridge.**  Because the rectangle effect `E_A(S)·E_B(T)` is an orthogonal
projection (`jointRect_isStarProjection`), its squared norm equals its diagonal:
`‖E_A(S)E_B(T)ξ‖² = ⟪ξ, E_A(S)E_B(T)ξ⟫.re = μ^A_{E_B(T)ξ}(S)`.  This reconciles the norm² form of the
σ-additivity crux (`jointContent_hasSum`) with the bimeasure (`jointRect_inner_eq_diag_left`) — the
nonnegative content the `AddContent` extension (G2.2) actually sums. -/
theorem jointRect_norm_sq_eq_diag (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (ξ : H) :
    ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2
      = ((A.spectralPVM.diag (B.spectralPVM.proj T hT ξ)) S).toReal := by
  rw [norm_sq_apply_of_isStarProjection (jointRect_isStarProjection A B hSC hS hT) ξ,
    jointRect_inner_eq_diag_left A B hSC hS hT ξ, Complex.ofReal_re]

/-! ### Marginal defect estimates (the tightness route to ∅-continuity)

The rectangle content `‖E_A(S)E_B(T)ξ‖²` is **dominated by each marginal separately**: by `μ^A_ξ(S)`
(commute the factors, then `E_B(T)` is a contraction) and by `μ^B_ξ(T)` (`E_A(S)` is a contraction,
no commutation needed).  Marginal *domination of the total mass* is too weak to force ∅-continuity
(mass can sit on a joint atom while both marginals stay large), but the *approximation defect*
`mR((S×T) ∖ (S'×T'))` **is** marginal-controlled (`jointRect_diff_defect_le`) — the key estimate
behind the compact-inner-regularity (Alexandrov) discharge of `jointContentRing_tendsto_empty`. -/

/-- **A-marginal domination of the rectangle content.**  `‖E_A(S)E_B(T)ξ‖² ≤ μ^A_ξ(S)`.  Commute the
factors so `E_A(S)E_B(T)ξ = E_B(T)(E_A(S)ξ)`, then `E_B(T)` is a contraction (`norm_proj_apply_le`)
and `‖E_A(S)ξ‖² = μ^A_ξ(S)` (`norm_sq_proj_apply`).  Uses `StronglyCommute`. -/
theorem jointRect_norm_sq_le_diag_left (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (ξ : H) :
    ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2
      ≤ ((A.spectralPVM.diag ξ) S).toReal := by
  have hcomm : A.spectralPVM.proj S hS * B.spectralPVM.proj T hT
      = B.spectralPVM.proj T hT * A.spectralPVM.proj S hS := (hSC S T hS hT).eq
  rw [hcomm, ContinuousLinearMap.mul_apply, ← A.spectralPVM.norm_sq_proj_apply S hS ξ]
  gcongr
  exact B.spectralPVM.norm_proj_apply_le T hT _

/-- **B-marginal domination of the rectangle content.**  `‖E_A(S)E_B(T)ξ‖² ≤ μ^B_ξ(T)`.  `E_A(S)` is a
contraction (`norm_proj_apply_le`) and `‖E_B(T)ξ‖² = μ^B_ξ(T)` (`norm_sq_proj_apply`).  No commutation
needed. -/
theorem jointRect_norm_sq_le_diag_right (A B : Observable.UnboundedObservable H)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (ξ : H) :
    ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2
      ≤ ((B.spectralPVM.diag ξ) T).toReal := by
  rw [ContinuousLinearMap.mul_apply, ← B.spectralPVM.norm_sq_proj_apply T hT ξ]
  gcongr
  exact A.spectralPVM.norm_proj_apply_le S hS _

/-- **The marginal-defect estimate — the key tightness input.**  The two rectangle pieces of the
semiring difference `(S×T) ∖ (S'×T') = (S∖S')×T ⊔ (S∩S')×(T∖T')` have total content bounded by the two
marginal defects:
`‖E_A(S∖S')E_B(T)ξ‖² + ‖E_A(S∩S')E_B(T∖T')ξ‖² ≤ μ^A_ξ(S∖S') + μ^B_ξ(T∖T')`.
First piece bounded via `jointRect_norm_sq_le_diag_left` (A-marginal), second via
`jointRect_norm_sq_le_diag_right` (B-marginal).  When `S'⊆S, T'⊆T` the LHS is exactly
`mR((S×T) ∖ (S'×T'))` (finite additivity over the two disjoint pieces), so a compact inner
approximation `S'×T' ⊆ S×T` with both marginal defects small makes the joint content defect small —
the regularity that drives the Alexandrov discharge of `jointContentRing_tendsto_empty`. -/
theorem jointRect_diff_defect_le (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S S' T T' : Set ℝ}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hT : MeasurableSet T) (hT' : MeasurableSet T')
    (ξ : H) :
    ‖(A.spectralPVM.proj (S \ S') (hS.diff hS') * B.spectralPVM.proj T hT) ξ‖ ^ 2
        + ‖(A.spectralPVM.proj (S ∩ S') (hS.inter hS')
            * B.spectralPVM.proj (T \ T') (hT.diff hT')) ξ‖ ^ 2
      ≤ ((A.spectralPVM.diag ξ) (S \ S')).toReal + ((B.spectralPVM.diag ξ) (T \ T')).toReal :=
  add_le_add
    (jointRect_norm_sq_le_diag_left A B hSC (hS.diff hS') hT ξ)
    (jointRect_norm_sq_le_diag_right A B (hS.inter hS') (hT.diff hT') ξ)

/-- **G2.1 capstone — σ-additivity in bimeasure form.**  Feeding the content bridge
`jointRect_norm_sq_eq_diag` into the crux `jointContent_hasSum`: for pairwise-disjoint measurable
`Tₙ`, the nonnegative rectangle values `μ^A_{E_B(Tₙ)ξ}(S)` sum to `μ^A_{E_B(⋃ₙ Tₙ)ξ}(S)`.  This is
countable additivity of the bimeasure `S × · ↦ ⟪ξ, E_A(S)E_B(·)ξ⟫` in the `T`-slot, exactly the form
the `AddContent` extension (G2.2) consumes. -/
theorem jointContent_hasSum_diag (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S : Set ℝ} (hS : MeasurableSet S) {T : ℕ → Set ℝ}
    (hT : ∀ n, MeasurableSet (T n)) (hd : Pairwise (fun i j => Disjoint (T i) (T j))) (ξ : H) :
    HasSum (fun n => ((A.spectralPVM.diag (B.spectralPVM.proj (T n) (hT n) ξ)) S).toReal)
      (((A.spectralPVM.diag
          (B.spectralPVM.proj (⋃ n, T n) (MeasurableSet.iUnion hT) ξ)) S).toReal) := by
  have key : ∀ (U : Set ℝ) (hU : MeasurableSet U),
      ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj U hU) ξ‖ ^ 2
        = ((A.spectralPVM.diag (B.spectralPVM.proj U hU ξ)) S).toReal :=
    fun U hU => jointRect_norm_sq_eq_diag A B hSC hS hU ξ
  simpa only [key] using jointContent_hasSum A B hSC hS hT hd ξ

/-! ## G2.2 — the per-state joint measure `μ_ξ` (the bimeasure → measure extension)

The rectangle content `m(S × T) = ‖E_A(S)E_B(T)ξ‖²` is extended to a genuine finite measure on the
Borel sets of `ℝ²` by Carathéodory on the rectangle semiring (`isSetSemiring_jointRectangles`).  The
crux is finite additivity of the content over an *arbitrary* disjoint rectangle partition of a
rectangle (`AddContent.sUnion'`), which by Pythagoras reduces to the **vector completeness**
`∑ₖ E_A(Sₖ)E_B(Tₖ)ξ = E_A(S)E_B(T)ξ` (a grid/atom refinement). -/

/-- **Generalized orthogonality.**  For two *disjoint rectangles* `S₁×T₁` and `S₂×T₂`, the vectors
`E_A(S₁)E_B(T₁)ξ` and `E_A(S₂)E_B(T₂)ξ` are orthogonal.  Disjointness of the rectangles means
`(S₁∩S₂)×(T₁∩T₂) = ∅`, i.e. `S₁∩S₂ = ∅` or `T₁∩T₂ = ∅`; either way the product effect
`E_A(S₁∩S₂)E_B(T₁∩T₂)` (= `(E_A(S₁)E_B(T₁))·(E_A(S₂)E_B(T₂))` by `jointRect_mul`) vanishes, and a
self-adjoint move (`jointRect_isStarProjection`) reads off the inner product.  This generalizes
`jointRect_orthogonal` (the same-`S` case) and is the Pythagoras input for the grid additivity. -/
theorem jointRect_orthogonal_general (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S₁ S₂ T₁ T₂ : Set ℝ}
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂)
    (hd : Disjoint (S₁ ×ˢ T₁) (S₂ ×ˢ T₂)) (ξ : H) :
    ⟪(A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁) ξ,
      (A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂) ξ⟫_ℂ = 0 := by
  have hsa : IsSelfAdjoint (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁) :=
    (jointRect_isStarProjection A B hSC hS₁ hT₁).isSelfAdjoint
  -- the product effect of two disjoint rectangles annihilates every vector
  have hzero : (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁)
      ((A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂) ξ) = 0 := by
    rw [← ContinuousLinearMap.mul_apply, jointRect_mul A B hSC hS₁ hS₂ hT₁ hT₂]
    have hcap : (S₁ ∩ S₂) ×ˢ (T₁ ∩ T₂) = (∅ : Set (ℝ × ℝ)) := by
      rw [← Set.prod_inter_prod]; exact Set.disjoint_iff_inter_eq_empty.mp hd
    rcases Set.prod_eq_empty_iff.mp hcap with hSe | hTe
    · rw [A.spectralPVM.proj_congr hSe (hS₁.inter hS₂) MeasurableSet.empty,
        A.spectralPVM.proj_empty]; simp
    · rw [B.spectralPVM.proj_congr hTe (hT₁.inter hT₂) MeasurableSet.empty,
        B.spectralPVM.proj_empty]; simp
  -- move the self-adjoint left factor across the inner product and read off the annihilation
  rw [← hsa.adjoint_eq, ContinuousLinearMap.adjoint_inner_left, hzero, inner_zero_right]

/-- **The grid collapse (vector completeness).**  If a `Fintype`-indexed family `σ` of pairwise
disjoint measurable sets exhausts `S₀`, and likewise `τ` exhausts `T₀`, then the rectangle-effect
vectors over the product grid sum to the whole-rectangle effect:
`∑_{(a,b)} E_A(σ a)E_B(τ b)ξ = E_A(S₀)E_B(T₀)ξ`.  Pure finite additivity of each PVM
(`proj_biUnion`) plus bilinearity of the operator product — no orthogonality, no induction. -/
theorem jointVector_grid_collapse (A B : Observable.UnboundedObservable H)
    {α β : Type*} [Fintype α] [Fintype β] (σ : α → Set ℝ) (τ : β → Set ℝ)
    (hσ : ∀ a, MeasurableSet (σ a)) (hτ : ∀ b, MeasurableSet (τ b))
    {S₀ T₀ : Set ℝ} (hS₀ : MeasurableSet S₀) (hT₀ : MeasurableSet T₀)
    (hσd : Pairwise (Function.onFun Disjoint σ)) (hτd : Pairwise (Function.onFun Disjoint τ))
    (hσsup : ⋃ a, σ a = S₀) (hτsup : ⋃ b, τ b = T₀) (ξ : H) :
    ∑ p : α × β,
        (A.spectralPVM.proj (σ p.1) (hσ p.1) * B.spectralPVM.proj (τ p.2) (hτ p.2)) ξ
      = (A.spectralPVM.proj S₀ hS₀ * B.spectralPVM.proj T₀ hT₀) ξ := by
  classical
  have hSproj : A.spectralPVM.proj S₀ hS₀ = ∑ a, A.spectralPVM.proj (σ a) (hσ a) := by
    have hbu : (⋃ a ∈ (Finset.univ : Finset α), σ a) = S₀ := by simpa using hσsup
    have hU : MeasurableSet (⋃ a ∈ (Finset.univ : Finset α), σ a) :=
      Finset.measurableSet_biUnion _ fun a _ => hσ a
    rw [← A.spectralPVM.proj_congr hbu hU hS₀,
      A.spectralPVM.proj_biUnion hσ Finset.univ (fun a _ b _ hab => hσd hab) hU]
  have hTproj : B.spectralPVM.proj T₀ hT₀ = ∑ b, B.spectralPVM.proj (τ b) (hτ b) := by
    have hbu : (⋃ b ∈ (Finset.univ : Finset β), τ b) = T₀ := by simpa using hτsup
    have hU : MeasurableSet (⋃ b ∈ (Finset.univ : Finset β), τ b) :=
      Finset.measurableSet_biUnion _ fun b _ => hτ b
    rw [← B.spectralPVM.proj_congr hbu hU hT₀,
      B.spectralPVM.proj_biUnion hτ Finset.univ (fun b _ c _ hbc => hτd hbc) hU]
  rw [hSproj, hTproj, Finset.sum_mul_sum, Fintype.sum_prod_type]
  simp only [ContinuousLinearMap.sum_apply]

/-- **Grid-cell orthogonality.**  Distinct cells of the product grid give orthogonal effect vectors
— immediate from `jointRect_orthogonal_general`, since distinct cells differ in some axis atom, and
distinct atoms are disjoint, so the rectangles are disjoint. -/
theorem jointGridCell_orthogonal (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {α β : Type*} [Fintype α] [Fintype β]
    (σ : α → Set ℝ) (τ : β → Set ℝ)
    (hσ : ∀ a, MeasurableSet (σ a)) (hτ : ∀ b, MeasurableSet (τ b))
    (hσd : Pairwise (Function.onFun Disjoint σ)) (hτd : Pairwise (Function.onFun Disjoint τ))
    (ξ : H) (p q : α × β) (hpq : p ≠ q) :
    ⟪(A.spectralPVM.proj (σ p.1) (hσ p.1) * B.spectralPVM.proj (τ p.2) (hτ p.2)) ξ,
      (A.spectralPVM.proj (σ q.1) (hσ q.1) * B.spectralPVM.proj (τ q.2) (hτ q.2)) ξ⟫_ℂ = 0 := by
  have hd : Disjoint (σ p.1 ×ˢ τ p.2) (σ q.1 ×ˢ τ q.2) := by
    rw [Set.disjoint_prod]
    rcases not_and_or.mp (fun h => hpq (Prod.ext_iff.mpr h)) with h1 | h2
    · exact Or.inl (hσd h1)
    · exact Or.inr (hτd h2)
  exact jointRect_orthogonal_general A B hSC (hσ p.1) (hσ q.1) (hτ p.2) (hτ q.2) hd ξ

/-- **Vector completeness via multiplicity counting.**  If a `Fintype`-indexed family of measurable
rectangles `Sp k ×ˢ Tp k` is pairwise disjoint and covers `S₀ ×ˢ T₀`, then the rectangle-effect
vectors sum to the whole-rectangle effect: `∑ₖ E_A(Sp k)E_B(Tp k)ξ = E_A(S₀)E_B(T₀)ξ`.  Proof:
refine both axes over the *common* sign-atom grid of the augmented family `Sfam, Tfam` indexed by
`Option κ` (the extra index `none` carries `S₀, T₀`).  Each side becomes a double sum over sign
vectors with a `ℕ`-multiplicity coefficient; pointwise, a nonzero atom cell witnesses a point lying
in exactly one cover rectangle (`card_filter_mem_eq_ite` + `hcover`), matching the multiplicity `1`
the whole rectangle assigns.  This is the grid/atom refinement feeding the `AddContent.sUnion'`
finite additivity (G2.2). -/
theorem jointVector_sUnion (A B : Observable.UnboundedObservable H)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (Sp Tp : κ → Set ℝ)
    (hSp : ∀ k, MeasurableSet (Sp k)) (hTp : ∀ k, MeasurableSet (Tp k))
    {S₀ T₀ : Set ℝ} (hS₀ : MeasurableSet S₀) (hT₀ : MeasurableSet T₀)
    (hdisj : Pairwise (Function.onFun Disjoint (fun k => Sp k ×ˢ Tp k)))
    (hcover : ⋃ k, Sp k ×ˢ Tp k = S₀ ×ˢ T₀) (ξ : H) :
    ∑ k, (A.spectralPVM.proj (Sp k) (hSp k) * B.spectralPVM.proj (Tp k) (hTp k)) ξ
      = (A.spectralPVM.proj S₀ hS₀ * B.spectralPVM.proj T₀ hT₀) ξ := by
  classical
  -- Augmented axis families over `Option κ`: index `none` carries `S₀, T₀`.
  set Sfam : Option κ → Set ℝ := fun o => o.elim S₀ Sp with hSfam_def
  set Tfam : Option κ → Set ℝ := fun o => o.elim T₀ Tp with hTfam_def
  have hSfam : ∀ o, MeasurableSet (Sfam o) := by
    rintro (_ | k)
    · exact hS₀
    · exact hSp k
  have hTfam : ∀ o, MeasurableSet (Tfam o) := by
    rintro (_ | k)
    · exact hT₀
    · exact hTp k
  -- the building block: an atom-pair effect vector
  set g : (Option κ → Bool) → (Option κ → Bool) → H :=
    fun u v => (A.spectralPVM.proj (signAtom Sfam u) (signAtom_measurableSet hSfam u)
      * B.spectralPVM.proj (signAtom Tfam v) (signAtom_measurableSet hTfam v)) ξ with hg_def
  -- expand a rectangle effect `(E_A(Sfam i) * E_B(Tfam i)) ξ` over the common grid
  have hcell : ∀ i : Option κ,
      (A.spectralPVM.proj (Sfam i) (hSfam i) * B.spectralPVM.proj (Tfam i) (hTfam i)) ξ
        = ∑ u ∈ Finset.univ.filter (fun u : Option κ → Bool => u i = true),
            ∑ v ∈ Finset.univ.filter (fun v : Option κ → Bool => v i = true), g u v := by
    intro i
    rw [proj_eq_sum_signAtom A.spectralPVM hSfam i (hSfam i),
      proj_eq_sum_signAtom B.spectralPVM hTfam i (hTfam i), Finset.sum_mul_sum]
    simp only [ContinuousLinearMap.sum_apply, hg_def]
  -- RHS: `(E_A(S₀) * E_B(T₀)) ξ = (E_A(Sfam none) * E_B(Tfam none)) ξ`
  have hRHS : (A.spectralPVM.proj S₀ hS₀ * B.spectralPVM.proj T₀ hT₀) ξ
      = ∑ u ∈ Finset.univ.filter (fun u : Option κ → Bool => u none = true),
          ∑ v ∈ Finset.univ.filter (fun v : Option κ → Bool => v none = true), g u v := by
    rw [A.spectralPVM.proj_congr (rfl : S₀ = Sfam none) hS₀ (hSfam none),
      B.spectralPVM.proj_congr (rfl : T₀ = Tfam none) hT₀ (hTfam none)]
    exact hcell none
  -- LHS: `∑ k, (E_A(Sp k) * E_B(Tp k)) ξ = ∑ k, (E_A(Sfam (some k)) * E_B(Tfam (some k))) ξ`
  have hLHS : ∑ k, (A.spectralPVM.proj (Sp k) (hSp k) * B.spectralPVM.proj (Tp k) (hTp k)) ξ
      = ∑ k, ∑ u ∈ Finset.univ.filter (fun u : Option κ → Bool => u (some k) = true),
          ∑ v ∈ Finset.univ.filter (fun v : Option κ → Bool => v (some k) = true), g u v := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [A.spectralPVM.proj_congr (rfl : Sp k = Sfam (some k)) (hSp k) (hSfam (some k)),
      B.spectralPVM.proj_congr (rfl : Tp k = Tfam (some k)) (hTp k) (hTfam (some k))]
    exact hcell (some k)
  rw [hLHS, hRHS]
  -- Convert filtered sums to full `univ` sums with `if`-coefficients, and collapse the nested
  -- `if`s into a single conjunction-condition (so everything is `∑ ... if P then g u v else 0`).
  have hcollapse : ∀ i : Option κ,
      (∑ u ∈ Finset.univ.filter (fun u : Option κ → Bool => u i = true),
        ∑ v ∈ Finset.univ.filter (fun v : Option κ → Bool => v i = true), g u v)
      = ∑ u, ∑ v, if (u i = true ∧ v i = true) then g u v else 0 := by
    intro i
    simp only [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h1 : u i = true
    · rw [if_pos h1]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h2 : v i = true <;> simp [h1, h2]
    · rw [if_neg h1]
      symm
      refine (Finset.sum_congr rfl fun v _ => ?_).trans Finset.sum_const_zero
      rw [if_neg (fun h => h1 h.1)]
  rw [hcollapse none]
  simp only [hcollapse (some _)]
  -- reorder `∑ k` innermost: `∑ k, ∑ u, ∑ v, F` → `∑ u, ∑ v, ∑ k, F`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  -- Goal: ∑ k, (if (u (some k) ∧ v (some k)) then g u v else 0)
  --        = if (u none ∧ v none) then g u v else 0
  -- ∑ k, (if P k then c else 0) = (filter P univ).card • c, with `c = g u v` constant in k.
  rw [← Finset.sum_filter, Finset.sum_const]
  -- Pointwise scalar equality suffices, then dispatch the two `if`s.
  by_cases hg0 : g u v = 0
  · rw [hg0, smul_zero]; simp
  · -- `g u v ≠ 0` forces both atom cells to be nonempty.
    have hSne : (signAtom Sfam u).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; intro he
      apply hg0
      simp only [hg_def]
      rw [A.spectralPVM.proj_congr he (signAtom_measurableSet hSfam u) MeasurableSet.empty,
        A.spectralPVM.proj_empty]
      simp
    have hTne : (signAtom Tfam v).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]; intro he
      apply hg0
      simp only [hg_def]
      rw [B.spectralPVM.proj_congr he (signAtom_measurableSet hTfam v) MeasurableSet.empty,
        B.spectralPVM.proj_empty]
      simp
    obtain ⟨a, ha⟩ := hSne
    obtain ⟨b, hb⟩ := hTne
    rw [mem_signAtom] at ha hb
    -- the per-k predicate equals membership of `(a,b)` in the `k`-th rectangle
    have hfilt : (Finset.univ.filter
          (fun k => u (some k) = true ∧ v (some k) = true))
        = (Finset.univ.filter (fun k => (a, b) ∈ Sp k ×ˢ Tp k)) := by
      refine Finset.filter_congr fun k _ => ?_
      have h1 : u (some k) = true ↔ a ∈ Sp k := ha (some k)
      have h2 : v (some k) = true ↔ b ∈ Tp k := hb (some k)
      rw [Set.mem_prod]
      exact ⟨fun ⟨p, q⟩ => ⟨h1.mp p, h2.mp q⟩, fun ⟨p, q⟩ => ⟨h1.mpr p, h2.mpr q⟩⟩
    have hcard : (Finset.univ.filter (fun k => (a, b) ∈ Sp k ×ˢ Tp k)).card
        = if (a, b) ∈ S₀ ×ˢ T₀ then 1 else 0 := by
      have := card_filter_mem_eq_ite (fun k => Sp k ×ˢ Tp k) hdisj (a, b)
      rw [hcover] at this
      convert this using 3
    rw [hfilt, hcard]
    -- now match the `if (a,b) ∈ S₀ ×ˢ T₀` count against `if (u none ∧ v none)`
    have hcond : ((a, b) ∈ S₀ ×ˢ T₀) ↔ (u none = true ∧ v none = true) := by
      have h1 : u none = true ↔ a ∈ S₀ := ha none
      have h2 : v none = true ↔ b ∈ T₀ := hb none
      rw [Set.mem_prod]
      exact ⟨fun ⟨p, q⟩ => ⟨h1.mpr p, h2.mpr q⟩, fun ⟨p, q⟩ => ⟨h1.mp p, h2.mp q⟩⟩
    by_cases hc : (a, b) ∈ S₀ ×ˢ T₀
    · rw [if_pos hc, if_pos (hcond.mp hc), one_smul]
    · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h)), zero_smul]

/-- **The norm-squared payload.**  Pairing vector completeness (`jointVector_sUnion`) with grid
orthogonality: over a disjoint rectangle cover of `S₀ ×ˢ T₀`, the whole-rectangle effect's squared
norm splits as the sum of the cell effects' squared norms.  This is the Pythagoras identity the
`AddContent.sUnion'` finite-additivity obligation (G2.2) consumes. -/
theorem jointRect_sUnion_norm_sq (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {κ : Type*} [Fintype κ] [DecidableEq κ] (Sp Tp : κ → Set ℝ)
    (hSp : ∀ k, MeasurableSet (Sp k)) (hTp : ∀ k, MeasurableSet (Tp k))
    {S₀ T₀ : Set ℝ} (hS₀ : MeasurableSet S₀) (hT₀ : MeasurableSet T₀)
    (hdisj : Pairwise (Function.onFun Disjoint (fun k => Sp k ×ˢ Tp k)))
    (hcover : ⋃ k, Sp k ×ˢ Tp k = S₀ ×ˢ T₀) (ξ : H) :
    ‖(A.spectralPVM.proj S₀ hS₀ * B.spectralPVM.proj T₀ hT₀) ξ‖ ^ 2
      = ∑ k, ‖(A.spectralPVM.proj (Sp k) (hSp k) * B.spectralPVM.proj (Tp k) (hTp k)) ξ‖ ^ 2 := by
  rw [← jointVector_sUnion A B Sp Tp hSp hTp hS₀ hT₀ hdisj hcover ξ]
  refine norm_sum_sq_orthogonal Finset.univ
    (fun k => (A.spectralPVM.proj (Sp k) (hSp k) * B.spectralPVM.proj (Tp k) (hTp k)) ξ)
    (fun i _ j _ hij => ?_)
  exact jointRect_orthogonal_general A B hSC (hSp i) (hSp j) (hTp i) (hTp j) (hdisj hij) ξ

/-! ## G2.2 — the joint rectangle content as a `MeasureTheory.AddContent`

The nonnegative rectangle content `m(S ×ˢ T) = ‖E_A(S)E_B(T)ξ‖²` (in `ℝ≥0∞`) is packaged as a
`MeasureTheory.AddContent` on the rectangle semiring `jointRectangles`.  Its `empty'` is immediate
(`E_A(∅) = 0`); its `sUnion'` finite-additivity obligation is discharged by the Pythagoras payload
`jointRect_sUnion_norm_sq` (vector completeness + grid orthogonality) lifted to `ℝ≥0∞`.  This is the
content the Carathéodory extension (`AddContent.measure`) consumes to build `μ_ξ`. -/

/-- **The `ℝ≥0∞`-valued rectangle content value.**  On a rectangle `R = S ×ˢ T` it is
`ENNReal.ofReal (‖E_A(S)E_B(T)ξ‖²)`; off the rectangle semiring it is `0`.  Defined as an `⨆` over
all rectangle representations of `R`; representation independence (proved in `jointRectVal_prod`)
makes the supremum collapse to the common value, and the empty index set gives `0` for
non-rectangles. -/
noncomputable def jointRectVal (A B : Observable.UnboundedObservable H) (ξ : H)
    (R : Set (ℝ × ℝ)) : ENNReal :=
  ⨆ (S : Set ℝ) (T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T) (_ : R = S ×ˢ T),
    ENNReal.ofReal (‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2)

/-- **Representation independence.**  Two presentations `S ×ˢ T = S' ×ˢ T'` of the same rectangle
give the same content value.  If the factors agree it is `proj_congr`; if some factor is empty then
both products carry an `E(∅) = 0` factor and both values are `ENNReal.ofReal 0 = 0`. -/
theorem jointRectVal_aux_indep (A B : Observable.UnboundedObservable H) (ξ : H)
    {S T S' T' : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS' : MeasurableSet S') (hT' : MeasurableSet T') (heq : S ×ˢ T = S' ×ˢ T') :
    ENNReal.ofReal (‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2)
      = ENNReal.ofReal (‖(A.spectralPVM.proj S' hS' * B.spectralPVM.proj T' hT') ξ‖ ^ 2) := by
  -- an empty factor makes the rectangle effect annihilate `ξ`, so the value is `0`
  have hzero : ∀ {U V : Set ℝ} (hU : MeasurableSet U) (hV : MeasurableSet V),
      U = ∅ ∨ V = ∅ →
      ENNReal.ofReal (‖(A.spectralPVM.proj U hU * B.spectralPVM.proj V hV) ξ‖ ^ 2) = 0 := by
    rintro U V hU hV (hUe | hVe)
    · rw [ContinuousLinearMap.mul_apply,
        A.spectralPVM.proj_congr hUe hU MeasurableSet.empty, A.spectralPVM.proj_empty]
      simp
    · rw [ContinuousLinearMap.mul_apply,
        B.spectralPVM.proj_congr hVe hV MeasurableSet.empty, B.spectralPVM.proj_empty,
        ContinuousLinearMap.zero_apply, map_zero]
      simp
  rcases Set.prod_eq_prod_iff.mp heq with ⟨rfl, rfl⟩ | ⟨he, he'⟩
  · rw [A.spectralPVM.proj_congr rfl hS hS', B.spectralPVM.proj_congr rfl hT hT']
  · rw [hzero hS hT he, hzero hS' hT' he']

/-- **The content value on a rectangle.**  `jointRectVal A B ξ (S ×ˢ T) = ENNReal.ofReal
(‖E_A(S)E_B(T)ξ‖²)`.  The defining `⨆` collapses to the single common value by representation
independence (`jointRectVal_aux_indep`). -/
theorem jointRectVal_prod (A B : Observable.UnboundedObservable H) (ξ : H)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    jointRectVal A B ξ (S ×ˢ T)
      = ENNReal.ofReal (‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2) := by
  apply le_antisymm
  · -- every term of the `⨆` equals the target value (representation independence)
    refine iSup_le fun S' => iSup_le fun T' => iSup_le fun hS' => iSup_le fun hT' =>
      iSup_le fun heq => ?_
    rw [jointRectVal_aux_indep A B ξ hS' hT' hS hT heq.symm]
  · -- the `(S, T)` representation is one of the terms
    refine le_iSup_of_le S (le_iSup_of_le T (le_iSup_of_le hS (le_iSup_of_le hT
      (le_iSup_of_le rfl ?_))))
    rw [A.spectralPVM.proj_congr rfl hS hS, B.spectralPVM.proj_congr rfl hT hT]

/-- **The diagonal-measure form of the content value.**  Restating `jointRectVal_prod` through the
content bridge `jointRect_norm_sq_eq_diag`: on a rectangle the content is `μ^A_{E_B(T)ξ}(S)`. -/
theorem jointRectVal_prod_diag (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    jointRectVal A B ξ (S ×ˢ T)
      = (A.spectralPVM.diag (B.spectralPVM.proj T hT ξ)) S := by
  rw [jointRectVal_prod A B ξ hS hT, jointRect_norm_sq_eq_diag A B hSC hS hT ξ,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **The joint rectangle content as a `MeasureTheory.AddContent`.**  `toFun = jointRectVal`;
`empty'` is `E_A(∅) = 0`; `sUnion'` is the Pythagoras payload `jointRect_sUnion_norm_sq` lifted to
`ℝ≥0∞` via `ENNReal.ofReal_sum_of_nonneg`.  This is the per-state content extended to `μ_ξ`. -/
noncomputable def jointContent (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) : MeasureTheory.AddContent ENNReal jointRectangles where
  toFun := jointRectVal A B ξ
  empty' := by
    have he : (∅ : Set (ℝ × ℝ)) = (∅ : Set ℝ) ×ˢ (∅ : Set ℝ) := by simp
    rw [he, jointRectVal_prod A B ξ MeasurableSet.empty MeasurableSet.empty,
      ContinuousLinearMap.mul_apply, A.spectralPVM.proj_empty]
    simp
  sUnion' := by
    classical
    intro I h_ss h_dis h_mem
    -- the union is a rectangle `S₀ ×ˢ T₀`
    obtain ⟨S₀, T₀, hS₀, hT₀, hST₀⟩ := h_mem
    -- index `I` by its coercion fintype; each member is a rectangle `Sp R ×ˢ Tp R`
    set κ := {R : Set (ℝ × ℝ) // R ∈ I} with hκ
    have hmemR : ∀ R : κ, R.1 ∈ jointRectangles := fun R => h_ss R.2
    set Sp : κ → Set ℝ := fun R => (hmemR R).choose with hSp_def
    set Tp : κ → Set ℝ := fun R => (hmemR R).choose_spec.choose with hTp_def
    have hSp : ∀ R, MeasurableSet (Sp R) := fun R => (hmemR R).choose_spec.choose_spec.1
    have hTp : ∀ R, MeasurableSet (Tp R) := fun R => (hmemR R).choose_spec.choose_spec.2.1
    have hR : ∀ R : κ, R.1 = Sp R ×ˢ Tp R := fun R => (hmemR R).choose_spec.choose_spec.2.2
    -- pairwise disjointness of the rectangle cells, transported through `hR`
    have hdisj : Pairwise (Function.onFun Disjoint (fun R : κ => Sp R ×ˢ Tp R)) := by
      intro R R' hRR'
      have hne : R.1 ≠ R'.1 := fun h => hRR' (Subtype.ext h)
      have := h_dis R.2 R'.2 hne
      rw [Function.onFun, ← hR R, ← hR R']
      simpa [Function.onFun, id] using this
    -- the cells cover `S₀ ×ˢ T₀`
    have hcover : ⋃ R : κ, Sp R ×ˢ Tp R = S₀ ×ˢ T₀ := by
      rw [← hST₀, Set.sUnion_eq_iUnion]
      exact Set.iUnion_congr fun R => (hR R).symm
    -- the Pythagoras payload
    have hpyth := jointRect_sUnion_norm_sq A B hSC Sp Tp hSp hTp hS₀ hT₀ hdisj hcover ξ
    -- lift to `ℝ≥0∞`
    show jointRectVal A B ξ (⋃₀ ↑I) = ∑ u ∈ I, jointRectVal A B ξ u
    rw [hST₀, jointRectVal_prod A B ξ hS₀ hT₀, hpyth,
      ENNReal.ofReal_sum_of_nonneg (fun R _ => sq_nonneg _)]
    -- `∑ R : κ, ofReal ‖..‖² = ∑ R : κ, jointRectVal R.1 = ∑ u ∈ I, jointRectVal u`
    rw [← Finset.sum_coe_sort I (jointRectVal A B ξ)]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [(by rw [hR R] : jointRectVal A B ξ R.1 = jointRectVal A B ξ (Sp R ×ˢ Tp R)),
      jointRectVal_prod A B ξ (hSp R) (hTp R)]

/-- **The content never takes the value `∞`.**  On a rectangle the value is `ENNReal.ofReal _`,
which is finite.  (Feeds the local finiteness needed by the Carathéodory extension.) -/
theorem jointContent_ne_top (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {R : Set (ℝ × ℝ)} (hR : R ∈ jointRectangles) : jointContent A B hSC ξ R ≠ ⊤ := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hR
  show jointRectVal A B ξ (S ×ˢ T) ≠ ⊤
  rw [jointRectVal_prod A B ξ hS hT]
  exact ENNReal.ofReal_ne_top

/-- **Total mass.**  The content of the full plane `univ ×ˢ univ` is `‖ξ‖²`: both factor projections
are the identity (`proj_univ`), so the rectangle effect is the identity and `‖id ξ‖² = ‖ξ‖²`. -/
theorem jointContent_univ (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) : jointContent A B hSC ξ (Set.univ ×ˢ Set.univ) = ENNReal.ofReal (‖ξ‖ ^ 2) := by
  show jointRectVal A B ξ (Set.univ ×ˢ Set.univ) = ENNReal.ofReal (‖ξ‖ ^ 2)
  rw [jointRectVal_prod A B ξ MeasurableSet.univ MeasurableSet.univ,
    ContinuousLinearMap.mul_apply, A.spectralPVM.proj_univ, B.spectralPVM.proj_univ,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

/-! ## G2.2 — the per-state joint scalar measure `μ_ξ` (Carathéodory extension)

The `MeasureTheory.AddContent` `jointContent` (on the rectangle *semiring*) is extended to a genuine
finite Borel measure on `ℝ × ℝ` by Carathéodory (`AddContent.measure`).  This needs σ-subadditivity
of the content, which on a *semiring* follows from σ-additivity on the generated *ring* (the
sup-closure), which in turn (Mathlib's `addContent_iUnion_eq_sum_of_tendsto_zero`) reduces to
**continuity at `∅`** of the ring content.  That ∅-continuity is the one genuine open analytic nut of
G2.2 (`jointContentRing_tendsto_empty`, left as `sorry`); everything else here is `sorry`-free. -/

/-- **Finiteness on the sup-closure ring.**  The ring content (the sup-closure of `jointContent`)
never takes the value `⊤`: an element of the sup-closure is a finite disjoint union of rectangles
(`mem_supClosure_iff`), its content is the finite sum of the rectangle values
(`supClosure_apply_finpartition`), and each summand is finite (`jointContent_ne_top`). -/
theorem jointContentRing_ne_top (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {s : Set (ℝ × ℝ)} (hs : s ∈ supClosure jointRectangles) :
    (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles s ≠ ⊤ := by
  obtain ⟨P, hP⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs
  rw [(jointContent A B hSC ξ).supClosure_apply_finpartition isSetSemiring_jointRectangles hP]
  rw [ENNReal.sum_ne_top]
  exact fun p hp => jointContent_ne_top A B hSC ξ (hP hp)

/-! ## G2.2 — the partition-independent *vector* content (the ∅-continuity reduction)

The ring content `mR(s) = (jointContent.supClosure) s` is the squared norm of a **vector**
`jointVectorContent ξ s ∈ H`, defined on the elementary sets (finite disjoint unions of rectangles)
and *additive* there.  Concretely, for any disjoint rectangle partition `J` of `s`,
`jointVectorContent ξ s = ∑_{R ∈ J} E_A(S_R) E_B(T_R) ξ`, a value independent of the partition
(`jointVectorContent_eq`, via the common-refinement collapse `jointVector_sUnion`).  Its squared norm
is `mR(s).toReal` (`jointVectorContent_norm_sq`, finite Pythagoras over the disjoint cells) and it is
finitely additive on disjoint elementary sets (`jointVectorContent_add`).

This reduces ∅-continuity to a **single, sharp** statement: on an antitone `sₙ` with `⋂ₙ sₙ = ∅`, the
vectors `jointVectorContent ξ sₙ` form a Cauchy sequence (the squared increments telescope the
antitone real sequence `mR(sₙ).toReal`), hence converge to a limit `w`, and the open content is
exactly `w = 0` — the joint spectral measure of the commuting pair has no mass on `∅`. -/

open scoped Classical in
/-- The effect vector `E_A(S_R) E_B(T_R) ξ` attached to a rectangle `R = S_R ×ˢ T_R` (chosen
representatives; `0` off the rectangle semiring).  Representation-independent on rectangles
(`rectVec_prod`). -/
noncomputable def rectVec (A B : Observable.UnboundedObservable H) (ξ : H)
    (R : Set (ℝ × ℝ)) : H :=
  if h : R ∈ jointRectangles then
    (A.spectralPVM.proj h.choose h.choose_spec.choose_spec.1
      * B.spectralPVM.proj h.choose_spec.choose h.choose_spec.choose_spec.2.1) ξ
  else 0

/-- **Effect-vector representation independence.**  The vector form of `jointRectVal_aux_indep`: two
presentations of the same rectangle give the same effect vector (factor-agreement, or an empty factor
annihilates `ξ`). -/
theorem rectVec_aux_indep (A B : Observable.UnboundedObservable H) (ξ : H)
    {S T S' T' : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS' : MeasurableSet S') (hT' : MeasurableSet T') (heq : S ×ˢ T = S' ×ˢ T') :
    (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ
      = (A.spectralPVM.proj S' hS' * B.spectralPVM.proj T' hT') ξ := by
  have hzero : ∀ {U V : Set ℝ} (hU : MeasurableSet U) (hV : MeasurableSet V),
      U = ∅ ∨ V = ∅ → (A.spectralPVM.proj U hU * B.spectralPVM.proj V hV) ξ = 0 := by
    rintro U V hU hV (hUe | hVe)
    · rw [ContinuousLinearMap.mul_apply,
        A.spectralPVM.proj_congr hUe hU MeasurableSet.empty, A.spectralPVM.proj_empty]; simp
    · rw [ContinuousLinearMap.mul_apply,
        B.spectralPVM.proj_congr hVe hV MeasurableSet.empty, B.spectralPVM.proj_empty,
        ContinuousLinearMap.zero_apply, map_zero]
  rcases Set.prod_eq_prod_iff.mp heq with ⟨rfl, rfl⟩ | ⟨he, he'⟩
  · rw [A.spectralPVM.proj_congr rfl hS hS', B.spectralPVM.proj_congr rfl hT hT']
  · rw [hzero hS hT he, hzero hS' hT' he']

/-- **`rectVec` on a rectangle is the effect vector.**  `rectVec ξ (S ×ˢ T) = E_A(S) E_B(T) ξ`,
independent of the chosen presentation (`rectVec_aux_indep`). -/
theorem rectVec_prod (A B : Observable.UnboundedObservable H) (ξ : H)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    rectVec A B ξ (S ×ˢ T) = (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ := by
  classical
  have hmem : (S ×ˢ T) ∈ jointRectangles := ⟨S, T, hS, hT, rfl⟩
  rw [rectVec, dif_pos hmem]
  exact (rectVec_aux_indep A B ξ hmem.choose_spec.choose_spec.1
    hmem.choose_spec.choose_spec.2.1 hS hT hmem.choose_spec.choose_spec.2.2.symm)

open scoped Classical in
/-- The vector content of an elementary set `s`, as the sum of the rectangle effect vectors over a
chosen disjoint rectangle partition (`0` off the sup-closure).  Partition-independent
(`jointVectorContent_eq`). -/
noncomputable def jointVectorContent (A B : Observable.UnboundedObservable H) (ξ : H)
    (s : Set (ℝ × ℝ)) : H :=
  if h : s ∈ supClosure jointRectangles then
    ∑ R ∈ ((isSetSemiring_jointRectangles.mem_supClosure_iff).mp h).choose.parts,
      rectVec A B ξ R
  else 0

/-- **Partition independence (the crux).**  For *any* disjoint rectangle cover `J` of `s` (parts in
`jointRectangles`), the sum of the rectangle effect vectors equals `jointVectorContent ξ s`.  Proof:
the chosen partition `K` (from `mem_supClosure_iff`) and `J` have a common refinement
`{R ∩ R' : R ∈ J, R' ∈ K}`; for each fixed `R ∈ J`, `{R ∩ R' : R' ∈ K}` is a disjoint rectangle cover
of the rectangle `R` (since `R ⊆ s = ⋃ K`), so `jointVector_sUnion` collapses
`∑_{R'} E(R ∩ R') = E(R)`.  Summing over `J` and symmetrizing in `J, K` gives equality. -/
theorem jointVectorContent_eq (A B : Observable.UnboundedObservable H) (ξ : H)
    {s : Set (ℝ × ℝ)} (hs : s ∈ supClosure jointRectangles)
    {J : Finset (Set (ℝ × ℝ))} (hJC : ↑J ⊆ jointRectangles)
    (hJd : (J : Set (Set (ℝ × ℝ))).PairwiseDisjoint id) (hJs : s = ⋃₀ ↑J) :
    ∑ R ∈ J, rectVec A B ξ R = jointVectorContent A B ξ s := by
  classical
  -- expand the chosen-partition definition first, then name the chosen partition `K`
  rw [jointVectorContent, dif_pos hs]
  set K := ((isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs).choose with hKdef
  have hKC : ↑K.parts ⊆ jointRectangles :=
    ((isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs).choose_spec
  have hKd : (K.parts : Set (Set (ℝ × ℝ))).PairwiseDisjoint id := K.disjoint
  have hKs : s = ⋃₀ ↑K.parts := by
    have h := K.sup_parts
    rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]
    exact h.symm
  -- The general two-cover agreement
  have agree : ∀ (J₁ J₂ : Finset (Set (ℝ × ℝ))),
      (↑J₁ ⊆ jointRectangles) → (↑J₂ ⊆ jointRectangles) →
      (∀ a ∈ J₂, ∀ b ∈ J₂, a ≠ b → Disjoint a b) →
      (⋃ R ∈ J₁, R) = (⋃ R ∈ J₂, R) →
      ∑ R ∈ J₁, rectVec A B ξ R = ∑ R ∈ J₁, ∑ R' ∈ J₂, rectVec A B ξ (R ∩ R') := by
    intro J₁ J₂ hJ₁C hJ₂C hJ₂d hcov
    refine Finset.sum_congr rfl fun R hR => ?_
    -- `R = S_R ×ˢ T_R` is a rectangle
    obtain ⟨SR, TR, hSR, hTR, hReq⟩ := hJ₁C hR
    -- index the cover of `R` by `R' ∈ J₂` (subtype)
    rw [← Finset.sum_coe_sort J₂ (fun R' => rectVec A B ξ (R ∩ R'))]
    -- represent each `R ∩ R'` as a rectangle `(SR ∩ S') ×ˢ (TR ∩ T')`
    set Sp : {R' // R' ∈ J₂} → Set ℝ := fun R' => SR ∩ (hJ₂C R'.2).choose with hSpdef
    set Tp : {R' // R' ∈ J₂} → Set ℝ :=
      fun R' => TR ∩ (hJ₂C R'.2).choose_spec.choose with hTpdef
    have hS'm : ∀ R' : {R' // R' ∈ J₂}, MeasurableSet (hJ₂C R'.2).choose :=
      fun R' => (hJ₂C R'.2).choose_spec.choose_spec.1
    have hT'm : ∀ R' : {R' // R' ∈ J₂}, MeasurableSet (hJ₂C R'.2).choose_spec.choose :=
      fun R' => (hJ₂C R'.2).choose_spec.choose_spec.2.1
    have hR'eq : ∀ R' : {R' // R' ∈ J₂},
        R'.1 = (hJ₂C R'.2).choose ×ˢ (hJ₂C R'.2).choose_spec.choose :=
      fun R' => (hJ₂C R'.2).choose_spec.choose_spec.2.2
    have hSpm : ∀ R', MeasurableSet (Sp R') := fun R' => hSR.inter (hS'm R')
    have hTpm : ∀ R', MeasurableSet (Tp R') := fun R' => hTR.inter (hT'm R')
    have hcell : ∀ R' : {R' // R' ∈ J₂},
        rectVec A B ξ (R ∩ R'.1) = rectVec A B ξ (Sp R' ×ˢ Tp R') := by
      intro R'
      congr 1
      rw [hReq, hR'eq R', Set.prod_inter_prod]
    simp_rw [hcell]
    simp_rw [rectVec_prod A B ξ (hSpm _) (hTpm _)]
    -- rewrite the LHS `rectVec A B ξ R` to the whole-rectangle effect `E_A(SR)E_B(TR)ξ`
    have hLHSeq : rectVec A B ξ R = (A.spectralPVM.proj SR hSR * B.spectralPVM.proj TR hTR) ξ := by
      rw [hReq]; exact rectVec_prod A B ξ hSR hTR
    rw [hLHSeq]
    -- the cells `Sp R' ×ˢ Tp R'` are disjoint and cover `R = SR ×ˢ TR`
    refine (jointVector_sUnion A B Sp Tp hSpm hTpm hSR hTR ?_ ?_ ξ).symm
    · -- disjointness: descends from `J₂` disjointness (cells ⊆ distinct `R'`)
      intro R₁ R₂ hR₁₂
      have hne : R₁.1 ≠ R₂.1 := fun h => hR₁₂ (Subtype.ext h)
      have hd := hJ₂d R₁.1 R₁.2 R₂.1 R₂.2 hne
      rw [Function.onFun]
      rw [show Sp R₁ ×ˢ Tp R₁ = R ∩ R₁.1 by rw [hReq, hR'eq R₁, Set.prod_inter_prod],
        show Sp R₂ ×ˢ Tp R₂ = R ∩ R₂.1 by rw [hReq, hR'eq R₂, Set.prod_inter_prod]]
      exact (hd.mono inf_le_right inf_le_right)
    · -- cover: `⋃ R' (R ∩ R') = R ∩ (⋃ J₂) = R ∩ s = R`
      have hRsub : R ⊆ ⋃ R'' ∈ J₂, R'' := by
        rw [← hcov]; exact Set.subset_biUnion_of_mem (u := fun R => R) hR
      have : ⋃ R' : {R' // R' ∈ J₂}, Sp R' ×ˢ Tp R' = R := by
        have hcells : ∀ R' : {R' // R' ∈ J₂}, Sp R' ×ˢ Tp R' = R ∩ R'.1 := fun R' => by
          rw [hReq, hR'eq R', Set.prod_inter_prod]
        simp_rw [hcells]
        rw [← Set.inter_iUnion]
        rw [show (⋃ R' : {R' // R' ∈ J₂}, R'.1) = ⋃ R'' ∈ J₂, R'' by
          rw [Set.iUnion_subtype]]
        exact Set.inter_eq_left.mpr hRsub
      rw [this, hReq]
  -- apply agreement both ways and conclude
  have hKd' : ∀ a ∈ K.parts, ∀ b ∈ K.parts, a ≠ b → Disjoint a b :=
    fun a ha b hb hab => hKd ha hb hab
  have hJd' : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → Disjoint a b :=
    fun a ha b hb hab => hJd ha hb hab
  -- the covers, in `⋃ R ∈ _, R` form
  have hJbi : (⋃ R ∈ J, R) = s := by rw [hJs]; exact (Set.sUnion_eq_biUnion).symm
  have hKbi : (⋃ R ∈ K.parts, R) = s := by
    conv_rhs => rw [hKs]
    exact (Set.sUnion_eq_biUnion).symm
  have hcovJK : (⋃ R ∈ J, R) = ⋃ R ∈ K.parts, R := by rw [hJbi, hKbi]
  have h1 := agree J K.parts hJC hKC hKd' hcovJK
  have h2 := agree K.parts J hKC hJC hJd' hcovJK.symm
  rw [h1, h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun R' _ => Finset.sum_congr rfl fun R _ => ?_
  rw [Set.inter_comm]

/-- **The content of a rectangle is `‖rectVec‖²`.**  For `R ∈ jointRectangles`,
`jointContent ξ R = ENNReal.ofReal (‖rectVec ξ R‖²)`.  Restates `jointRectVal_prod` through `rectVec`
(`rectVec_prod`). -/
theorem jointContent_rectVec (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {R : Set (ℝ × ℝ)} (hR : R ∈ jointRectangles) :
    jointContent A B hSC ξ R = ENNReal.ofReal (‖rectVec A B ξ R‖ ^ 2) := by
  obtain ⟨S, T, hS, hT, rfl⟩ := hR
  show jointRectVal A B ξ (S ×ˢ T) = _
  rw [jointRectVal_prod A B ξ hS hT, rectVec_prod A B ξ hS hT]

/-- **The squared norm of the vector content is the ring content.**
`‖jointVectorContent ξ s‖² = mR(s).toReal`.  Over the chosen rectangle partition `K` of `s`,
`mR(s) = ∑_{R ∈ K} ofReal ‖rectVec R‖²` (`supClosure_apply_finpartition` + `jointContent_rectVec`),
whose `.toReal` is `∑ ‖rectVec R‖²` (`toReal_sum`), which is `‖∑ rectVec R‖²` (finite Pythagoras over
the pairwise-orthogonal disjoint cells, `jointRect_orthogonal_general`), i.e. `‖jointVectorContent‖²`
(`jointVectorContent_eq`). -/
theorem jointVectorContent_norm_sq (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (ξ : H) {s : Set (ℝ × ℝ)} (hs : s ∈ supClosure jointRectangles) :
    ‖jointVectorContent A B ξ s‖ ^ 2
      = ((jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles s).toReal := by
  classical
  -- the chosen rectangle partition `K`
  obtain ⟨K, hKC⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs
  -- ring content over `K`
  rw [(jointContent A B hSC ξ).supClosure_apply_finpartition isSetSemiring_jointRectangles hKC]
  -- each summand is `ofReal ‖rectVec‖²`
  have hsummand : ∀ R ∈ K.parts, jointContent A B hSC ξ R = ENNReal.ofReal (‖rectVec A B ξ R‖ ^ 2) :=
    fun R hR => jointContent_rectVec A B hSC ξ (hKC hR)
  rw [Finset.sum_congr rfl hsummand,
    ← ENNReal.ofReal_sum_of_nonneg (fun R _ => sq_nonneg _), ENNReal.toReal_ofReal
      (Finset.sum_nonneg fun R _ => sq_nonneg _)]
  -- Pythagoras: the cells are pairwise orthogonal
  have hortho : ∀ R₁ ∈ K.parts, ∀ R₂ ∈ K.parts, R₁ ≠ R₂ →
      ⟪rectVec A B ξ R₁, rectVec A B ξ R₂⟫_ℂ = 0 := by
    intro R₁ hR₁ R₂ hR₂ hne
    obtain ⟨S₁, T₁, hS₁, hT₁, hR₁eq⟩ := hKC hR₁
    obtain ⟨S₂, T₂, hS₂, hT₂, hR₂eq⟩ := hKC hR₂
    have hd : Disjoint (S₁ ×ˢ T₁) (S₂ ×ˢ T₂) := by
      rw [← hR₁eq, ← hR₂eq]; exact K.disjoint hR₁ hR₂ hne
    rw [show rectVec A B ξ R₁ = (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁) ξ by
        rw [hR₁eq]; exact rectVec_prod A B ξ hS₁ hT₁,
      show rectVec A B ξ R₂ = (A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂) ξ by
        rw [hR₂eq]; exact rectVec_prod A B ξ hS₂ hT₂]
    exact jointRect_orthogonal_general A B hSC hS₁ hS₂ hT₁ hT₂ hd ξ
  rw [← norm_sum_sq_orthogonal K.parts (rectVec A B ξ) hortho]
  -- identify `∑ rectVec = jointVectorContent`
  have hKd : (K.parts : Set (Set (ℝ × ℝ))).PairwiseDisjoint id := K.disjoint
  have hKs : s = ⋃₀ ↑K.parts := by
    have h := K.sup_parts
    rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]; exact h.symm
  rw [jointVectorContent_eq A B ξ hs hKC hKd hKs]

/-- **Finite additivity of the vector content** on disjoint elementary sets.
`jointVectorContent ξ (a ∪ b) = jointVectorContent ξ a + jointVectorContent ξ b` for disjoint
`a, b ∈ supClosure jointRectangles`.  Proof: chosen partitions `Ja, Jb` of `a, b` combine to a
disjoint rectangle partition `Ja ∪ Jb` of `a ∪ b`; `jointVectorContent_eq` evaluates all three sides
and `Finset.sum_union` (disjoint part-sets, since `a, b` disjoint) splits the sum. -/
theorem jointVectorContent_add (A B : Observable.UnboundedObservable H) (ξ : H)
    {a b : Set (ℝ × ℝ)} (ha : a ∈ supClosure jointRectangles) (hb : b ∈ supClosure jointRectangles)
    (hab : Disjoint a b) :
    jointVectorContent A B ξ (a ∪ b)
      = jointVectorContent A B ξ a + jointVectorContent A B ξ b := by
  classical
  obtain ⟨Ja, hJaC⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp ha
  obtain ⟨Jb, hJbC⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp hb
  have hJad : (Ja.parts : Set (Set (ℝ × ℝ))).PairwiseDisjoint id := Ja.disjoint
  have hJbd : (Jb.parts : Set (Set (ℝ × ℝ))).PairwiseDisjoint id := Jb.disjoint
  have hJas : a = ⋃₀ ↑Ja.parts := by
    have h := Ja.sup_parts; rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]; exact h.symm
  have hJbs : b = ⋃₀ ↑Jb.parts := by
    have h := Jb.sup_parts; rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]; exact h.symm
  -- the part-sets are disjoint as Finsets (members of `Ja` ⊆ `a`, of `Jb` ⊆ `b`, and `a, b` disjoint)
  have hpartDisjoint : Disjoint Ja.parts Jb.parts := by
    rw [Finset.disjoint_left]
    intro R hRa hRb
    -- `R ⊆ a` and `R ⊆ b`, but each `R` is nonempty in a Finpartition (⊥ ∉ parts)... handle empty too
    have hRsuba : R ⊆ a := by rw [hJas]; exact Set.subset_sUnion_of_mem hRa
    have hRsubb : R ⊆ b := by rw [hJbs]; exact Set.subset_sUnion_of_mem hRb
    have hRempty : R = ⊥ := by
      rw [Set.bot_eq_empty, ← Set.subset_empty_iff,
        ← Set.disjoint_iff_inter_eq_empty.mp hab]
      exact Set.subset_inter hRsuba hRsubb
    exact Ja.bot_notMem (hRempty ▸ hRa)
  -- `Ja.parts ∪ Jb.parts` is a disjoint rectangle partition of `a ∪ b`
  have hUC : ↑(Ja.parts ∪ Jb.parts) ⊆ jointRectangles := by
    rw [Finset.coe_union]; exact Set.union_subset hJaC hJbC
  have hUd : ((Ja.parts ∪ Jb.parts : Finset (Set (ℝ × ℝ))) :
      Set (Set (ℝ × ℝ))).PairwiseDisjoint id := by
    rw [Finset.coe_union]
    apply Set.PairwiseDisjoint.union hJad hJbd
    intro R₁ hR₁ R₂ hR₂ _
    have hR₁suba : R₁ ⊆ a := by rw [hJas]; exact Set.subset_sUnion_of_mem hR₁
    have hR₂subb : R₂ ⊆ b := by rw [hJbs]; exact Set.subset_sUnion_of_mem hR₂
    exact (hab.mono hR₁suba hR₂subb)
  have hUs : a ∪ b = ⋃₀ ↑(Ja.parts ∪ Jb.parts) := by
    rw [Finset.coe_union, Set.sUnion_union, ← hJas, ← hJbs]
  have hUmem : a ∪ b ∈ supClosure jointRectangles :=
    (isSetSemiring_jointRectangles.isSetRing_supClosure).union_mem ha hb
  -- evaluate all three contents over their partitions and split the sum
  rw [← jointVectorContent_eq A B ξ hUmem hUC hUd hUs,
    ← jointVectorContent_eq A B ξ ha hJaC hJad hJas,
    ← jointVectorContent_eq A B ξ hb hJbC hJbd hJbs,
    Finset.sum_union hpartDisjoint]

/-! ## G2.2 — compact inner regularity of the ring content (the tightness ∅-continuity)

The ring content `mR` is **inner regular by compact rectangles**: any elementary set is approximated
from inside by a compact elementary set up to arbitrarily small content.  Per rectangle this is the
marginal-defect bound `jointContentRing_diff_le` (the ℝ≥0∞ lift of `jointRect_diff_defect_le`) fed by
the inner regularity of the genuine marginals `μ^A_ξ, μ^B_ξ` on `ℝ`.  This is the compactness input
that discharges `jointContentRing_tendsto_empty` by the classical Alexandrov argument (a finitely
additive, compact-inner-regular content is σ-additive): a decreasing elementary sequence with empty
intersection cannot keep positive content, else the inner compact approximants would have the finite
intersection property and meet. -/

/-- The ring content of a single rectangle is `ofReal ‖E_A(S)E_B(T)ξ‖²` (`supClosure_apply_of_mem` +
`jointContent_rectVec` + `rectVec_prod`). -/
theorem jointContentRing_prod (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles (S ×ˢ T)
      = ENNReal.ofReal (‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2) := by
  rw [(jointContent A B hSC ξ).supClosure_apply_of_mem isSetSemiring_jointRectangles
        ⟨S, T, hS, hT, rfl⟩,
    jointContent_rectVec A B hSC ξ ⟨S, T, hS, hT, rfl⟩, rectVec_prod A B ξ hS hT]

/-- **The marginal-defect bound on the ring content.**  The content of the difference
`(S×T) ∖ (S'×T')` is bounded by the two marginal defects `μ^A_ξ(S∖S') + μ^B_ξ(T∖T')`.  Lifts
`jointRect_diff_defect_le` from the norm² pieces to the ℝ≥0∞ ring content, via the semiring
difference decomposition `(S×T)∖(S'×T') = (S∖S')×T ⊔ (S∩S')×(T∖T')` + finite additivity
(`addContent_union`).  Together with inner regularity of `μ^A_ξ, μ^B_ξ`, this is the compact
inner-regularity input to the Alexandrov ∅-continuity argument. -/
theorem jointContentRing_diff_le (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {S S' T T' : Set ℝ} (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (hT : MeasurableSet T) (hT' : MeasurableSet T') :
    (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((S ×ˢ T) \ (S' ×ˢ T'))
      ≤ A.spectralPVM.diag ξ (S \ S') + B.spectralPVM.diag ξ (T \ T') := by
  have hRing : MeasureTheory.IsSetRing (supClosure jointRectangles) :=
    isSetSemiring_jointRectangles.isSetRing_supClosure
  have hset : (S ×ˢ T) \ (S' ×ˢ T')
      = ((S \ S') ×ˢ T) ∪ ((S ∩ S') ×ˢ (T \ T')) := by
    ext ⟨x, y⟩
    simp only [Set.mem_diff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff]
    tauto
  have hP₁ : ((S \ S') ×ˢ T) ∈ supClosure jointRectangles :=
    subset_supClosure ⟨S \ S', T, hS.diff hS', hT, rfl⟩
  have hP₂ : ((S ∩ S') ×ˢ (T \ T')) ∈ supClosure jointRectangles :=
    subset_supClosure ⟨S ∩ S', T \ T', hS.inter hS', hT.diff hT', rfl⟩
  have hdisj : Disjoint ((S \ S') ×ˢ T) ((S ∩ S') ×ˢ (T \ T')) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, _⟩ ⟨hx', _⟩
    exact hx.2 hx'.2
  rw [hset, addContent_union hRing hP₁ hP₂ hdisj,
    jointContentRing_prod A B hSC ξ (hS.diff hS') hT,
    jointContentRing_prod A B hSC ξ (hS.inter hS') (hT.diff hT'),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  refine le_trans (ENNReal.ofReal_le_ofReal
    (jointRect_diff_defect_le A B hSC hS hS' hT hT' ξ)) ?_
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Per-rectangle compact inner approximation.**  A measurable rectangle `S ×ˢ T` is approximated
from inside by a compact rectangle `K = S' ×ˢ T'` whose content defect is `< ε`: pick compact
`S' ⊆ S`, `T' ⊆ T` by inner regularity of the marginals `μ^A_ξ, μ^B_ξ` (each defect `< ε/2`), then
`jointContentRing_diff_le` bounds the joint defect by `μ^A_ξ(S∖S') + μ^B_ξ(T∖T') < ε`. -/
theorem jointRect_inner_compact (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ K : Set (ℝ × ℝ), K ∈ jointRectangles ∧ K ⊆ S ×ˢ T ∧ IsCompact K ∧
      (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((S ×ˢ T) \ K) < ε := by
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨S', hS'sub, hS'cp, hS'lt⟩ :=
    hS.exists_isCompact_diff_lt (measure_ne_top (A.spectralPVM.diag ξ) S) hε2
  obtain ⟨T', hT'sub, hT'cp, hT'lt⟩ :=
    hT.exists_isCompact_diff_lt (measure_ne_top (B.spectralPVM.diag ξ) T) hε2
  refine ⟨S' ×ˢ T',
    ⟨S', T', hS'cp.isClosed.measurableSet, hT'cp.isClosed.measurableSet, rfl⟩,
    Set.prod_mono hS'sub hT'sub, hS'cp.prod hT'cp, ?_⟩
  calc (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((S ×ˢ T) \ (S' ×ˢ T'))
      ≤ A.spectralPVM.diag ξ (S \ S') + B.spectralPVM.diag ξ (T \ T') :=
        jointContentRing_diff_le A B hSC ξ hS hS'cp.isClosed.measurableSet hT
          hT'cp.isClosed.measurableSet
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hS'lt hT'lt
    _ = ε := ENNReal.add_halves ε

/-- **Compact inner regularity of the ring content.**  Every elementary set `s` (a finite union of
measurable rectangles) is approximated from inside by a compact elementary set `K ⊆ s` with content
defect `mR(s ∖ K) ≤ ε`.  Induction over a rectangle cover of `s`: approximate each rectangle part by
a compact sub-rectangle (`jointRect_inner_compact`) at budget `ε/2ⁿ`, union them, and bound the total
defect by finite subadditivity (`addContent_union_le`).  This is the tightness hypothesis the
Alexandrov ∅-continuity argument feeds on. -/
theorem jointElem_inner_compact (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {s : Set (ℝ × ℝ)} (hs : s ∈ supClosure jointRectangles) {ε : ENNReal} (hε : ε ≠ 0) :
    ∃ K : Set (ℝ × ℝ), K ∈ supClosure jointRectangles ∧ K ⊆ s ∧ IsCompact K ∧
      (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles (s \ K) ≤ ε := by
  classical
  have hRing : MeasureTheory.IsSetRing (supClosure jointRectangles) :=
    isSetSemiring_jointRectangles.isSetRing_supClosure
  -- inner-approximate an arbitrary finite union of rectangles (no disjointness needed)
  have aux : ∀ (J : Finset (Set (ℝ × ℝ))), ↑J ⊆ jointRectangles → ∀ {δ : ENNReal}, δ ≠ 0 →
      ∃ K, K ∈ supClosure jointRectangles ∧ K ⊆ ⋃₀ ↑J ∧ IsCompact K ∧
        (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((⋃₀ ↑J) \ K) ≤ δ := by
    intro J
    induction J using Finset.induction with
    | empty =>
        intro _ δ _
        refine ⟨∅, hRing.empty_mem, by simp, isCompact_empty, ?_⟩
        simp only [Finset.coe_empty, Set.sUnion_empty, Set.diff_empty, addContent_empty]
        exact zero_le
    | @insert R J hRnotin ih =>
        intro hJC δ hδ
        obtain ⟨S, T, hS, hT, rfl⟩ : R ∈ jointRectangles := hJC (Finset.mem_insert_self R J)
        have hJC' : ↑J ⊆ jointRectangles := fun x hx => hJC (Finset.mem_insert_of_mem hx)
        have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ).ne'
        obtain ⟨KJ, hKJmem, hKJsub, hKJcp, hKJle⟩ := ih hJC' hδ2
        obtain ⟨KR, hKRmem, hKRsub, hKRcp, hKRlt⟩ :=
          jointRect_inner_compact A B hSC ξ hS hT hδ2
        have hB'mem : ⋃₀ (↑J : Set (Set (ℝ × ℝ))) ∈ supClosure jointRectangles := by
          rw [Set.sUnion_eq_biUnion, Finset.set_biUnion_coe]
          exact hRing.biUnion_mem J fun x hx => subset_supClosure (hJC' (Finset.mem_coe.mpr hx))
        have hSTmem : (S ×ˢ T) ∈ supClosure jointRectangles := subset_supClosure ⟨S, T, hS, hT, rfl⟩
        have hKRring : KR ∈ supClosure jointRectangles := subset_supClosure hKRmem
        refine ⟨KR ∪ KJ, hRing.union_mem hKRring hKJmem, ?_, hKRcp.union hKJcp, ?_⟩
        · rw [Finset.coe_insert, Set.sUnion_insert]
          exact Set.union_subset_union hKRsub hKJsub
        · rw [Finset.coe_insert, Set.sUnion_insert]
          have hsub : ((S ×ˢ T) ∪ ⋃₀ (↑J : Set (Set (ℝ × ℝ)))) \ (KR ∪ KJ)
              ⊆ ((S ×ˢ T) \ KR) ∪ (⋃₀ (↑J : Set (Set (ℝ × ℝ))) \ KJ) := by
            rw [Set.union_diff_distrib]
            exact Set.union_subset_union
              (Set.diff_subset_diff_right Set.subset_union_left)
              (Set.diff_subset_diff_right Set.subset_union_right)
          calc (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles
                  (((S ×ˢ T) ∪ ⋃₀ ↑J) \ (KR ∪ KJ))
              ≤ (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles
                  (((S ×ˢ T) \ KR) ∪ (⋃₀ ↑J \ KJ)) :=
                addContent_mono hRing.isSetSemiring
                  (hRing.diff_mem (hRing.union_mem hSTmem hB'mem) (hRing.union_mem hKRring hKJmem))
                  (hRing.union_mem (hRing.diff_mem hSTmem hKRring) (hRing.diff_mem hB'mem hKJmem))
                  hsub
            _ ≤ (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles ((S ×ˢ T) \ KR)
                  + (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles (⋃₀ ↑J \ KJ) :=
                addContent_union_le hRing (hRing.diff_mem hSTmem hKRring)
                  (hRing.diff_mem hB'mem hKJmem)
            _ ≤ δ / 2 + δ / 2 := add_le_add hKRlt.le hKJle
            _ = δ := ENNReal.add_halves δ
  -- apply `aux` to a chosen rectangle partition of `s`
  obtain ⟨P, hPC⟩ := (isSetSemiring_jointRectangles.mem_supClosure_iff).mp hs
  have hPs : s = ⋃₀ ↑P.parts := by
    have h := P.sup_parts
    rw [Finset.sup_set_eq_biUnion] at h
    rw [Set.sUnion_eq_biUnion]; exact h.symm
  rw [hPs]
  exact aux P.parts hPC hε

/-- **Continuity at `∅` of the ring content.**  For an antitone sequence `sₙ` of elementary sets
(finite disjoint unions of rectangles) with `⋂ₙ sₙ = ∅`, the content `mR(sₙ) = ‖jointVectorContent ξ sₙ‖²`
tends to `0` — the σ-additivity input (`AddContent.measure`) for the joint scalar measure.

The reduction `mR(sₙ) → ‖w‖²` for the in-`H` limit `w` of the Cauchy sequence of vector contents
`jointVectorContent ξ sₙ` is elementary (`jointVectorContent_norm_sq`, `_add`, ring additivity); the
sharp content is `w = 0`, the **multivariate spectral theorem's** core (the joint spectral measure of
the commuting pair assigns no mass to `∅`; *not* recoverable from the marginal data alone, cf.
`exists_coupling_always`).  It is discharged here by **Route T (tightness / Alexandrov)**: the
joint content's compact inner regularity comes from the genuine marginals via commutation + contraction
(the approximation *defect* `mR((S×T)∖(S'×T')) ≤ μ^A_ξ(S∖S') + μ^B_ξ(T∖T')` is marginal-controlled even
though the *mass* is not), and a finite-intersection-property argument on decreasing compacts forces
`w = 0`.  `sorry`-free and axiom-clean. -/
theorem jointContentRing_tendsto_empty (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (ξ : H) ⦃s : ℕ → Set (ℝ × ℝ)⦄
    (hs : ∀ n, s n ∈ supClosure jointRectangles) (hanti : Antitone s) (hempty : (⋂ n, s n) = ∅) :
    Filter.Tendsto (fun n => (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles (s n))
      Filter.atTop (nhds 0) := by
  classical
  set mR := (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles with hmRdef
  have hRing : MeasureTheory.IsSetRing (supClosure jointRectangles) :=
    isSetSemiring_jointRectangles.isSetRing_supClosure
  have hmR_ne_top : ∀ n, mR (s n) ≠ ⊤ := fun n => jointContentRing_ne_top A B hSC ξ (hs n)
  -- the vector content and the real content sequence
  set v : ℕ → H := fun n => jointVectorContent A B ξ (s n) with hvdef
  set a : ℕ → ℝ := fun n => (mR (s n)).toReal with hadef
  have hav : ∀ n, a n = ‖v n‖ ^ 2 := fun n =>
    (jointVectorContent_norm_sq A B hSC ξ (hs n)).symm
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n => ENNReal.toReal_nonneg
  -- `mR` is monotone on the ring and `s` is antitone, so `a` is antitone
  have ha_anti : Antitone a := by
    intro n m hnm
    refine ENNReal.toReal_mono (hmR_ne_top n) ?_
    exact addContent_mono hRing.isSetSemiring (hs m) (hs n) (hanti hnm)
  -- the telescoping increment: for `n ≤ m`, `v n − v m = jointVectorContent ξ (s n \ s m)`
  have hdiff : ∀ n m, n ≤ m →
      v n - v m = jointVectorContent A B ξ (s n \ s m) ∧
      a n - a m = ‖jointVectorContent A B ξ (s n \ s m)‖ ^ 2 := by
    intro n m hnm
    have hsm_sub : s m ⊆ s n := hanti hnm
    have hdmem : (s n \ s m) ∈ supClosure jointRectangles := hRing.diff_mem (hs n) (hs m)
    -- decompose `s n = s m ∪ (s n \ s m)` (disjoint)
    have hunion : s n = s m ∪ (s n \ s m) := (Set.union_diff_cancel hsm_sub).symm
    have hdisj : Disjoint (s m) (s n \ s m) := disjoint_sdiff_self_right
    have hvadd : v n = v m + jointVectorContent A B ξ (s n \ s m) := by
      rw [hvdef]; dsimp only
      conv_lhs => rw [hunion]
      exact jointVectorContent_add A B ξ (hs m) hdmem hdisj
    refine ⟨by rw [hvadd]; abel, ?_⟩
    -- the real content telescopes: `a n = a m + ‖...‖²`
    have haadd : a n = a m + ‖jointVectorContent A B ξ (s n \ s m)‖ ^ 2 := by
      rw [hadef]; dsimp only
      have hcont : mR (s n) = mR (s m) + mR (s n \ s m) := by
        conv_lhs => rw [hunion]
        exact addContent_union hRing (hs m) hdmem hdisj
      rw [hcont, ENNReal.toReal_add (hmR_ne_top m)
          (jointContentRing_ne_top A B hSC ξ hdmem),
        jointVectorContent_norm_sq A B hSC ξ hdmem]
    rw [haadd]; ring
  -- symmetric norm identity: `‖v n − v m‖² = |a n − a m|`
  have hsym : ∀ n m, ‖v n - v m‖ ^ 2 = |a n - a m| := by
    intro n m
    rcases le_total n m with h | h
    · obtain ⟨hd, ha⟩ := hdiff n m h
      rw [hd, ← ha, abs_of_nonneg]
      exact sub_nonneg.mpr (ha_anti h)
    · obtain ⟨hd, ha⟩ := hdiff m n h
      have : ‖v n - v m‖ ^ 2 = ‖v m - v n‖ ^ 2 := by rw [← norm_neg, neg_sub]
      rw [this, hd, ← ha, abs_of_nonpos (by linarith [ha_anti h])]
      ring
  -- `a` converges (antitone, bounded below by 0) to its infimum `L`
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; exact ha_nonneg n⟩
  set L : ℝ := ⨅ n, a n with hLdef
  have ha_tendsto : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf ha_anti hbdd
  have hL_le : ∀ n, L ≤ a n := fun n => ciInf_le hbdd n
  -- the Cauchy modulus `b N = √(a N − L) → 0`, dominating `dist (v n) (v m)` for `N ≤ n, m`
  set b : ℕ → ℝ := fun N => Real.sqrt (a N - L) with hbdef
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    have : Tendsto (fun N => a N - L) atTop (𝓝 (L - L)) := ha_tendsto.sub_const L
    rw [sub_self] at this
    have := this.sqrt
    rwa [Real.sqrt_zero] at this
  have hvCauchy : CauchySeq v := by
    refine cauchySeq_of_le_tendsto_0 b (fun n m N hNn hNm => ?_) hb_tendsto
    -- `dist (v n) (v m) = ‖v n − v m‖ = √|a n − a m| ≤ √(a N − L) = b N`
    rw [dist_eq_norm]
    have hnorm : ‖v n - v m‖ = Real.sqrt |a n - a m| := by
      rw [← hsym n m, Real.sqrt_sq (norm_nonneg _)]
    rw [hnorm, hbdef]
    refine Real.sqrt_le_sqrt ?_
    -- both `a n, a m ∈ [L, a N]`, so `|a n − a m| ≤ a N − L`
    have hn := ha_anti hNn
    have hm := ha_anti hNm
    rw [abs_le]
    exact ⟨by linarith [hL_le n], by linarith [hL_le m]⟩
  -- the limit vector `w`
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hvCauchy
  -- `a n = ‖v n‖² → ‖w‖²`
  have ha_to_w : Tendsto a atTop (𝓝 (‖w‖ ^ 2)) := by
    refine (hw.norm.pow 2).congr fun n => ?_
    exact (hav n).symm
  /- The limit `w = 0` by the **tightness (Alexandrov) argument**: it suffices that `L = ⨅ₙ aₙ = 0`.
     If `L > 0`, inner-approximate each `sₙ` by a compact elementary `Cₙ ⊆ sₙ` (`jointElem_inner_compact`)
     with content defect `≤ L/4·2⁻ⁿ`; the decreasing compacts `Kₙ = ⋂_{j≤n} Cⱼ` then keep content
     `≥ L/2 > 0`, so each is nonempty, and by the finite intersection property `⋂ₙ Kₙ ≠ ∅` — but
     `Kₙ ⊆ sₙ`, contradicting `⋂ₙ sₙ = ∅`.  The defect is marginal-controlled (`jointRect_diff_defect_le`),
     the one place the genuine commuting-projection structure enters. -/
  have hw0 : w = 0 := by
    have hwsq : ‖w‖ ^ 2 = L := tendsto_nhds_unique ha_to_w ha_tendsto
    have hL_nonneg : 0 ≤ L := ge_of_tendsto' ha_tendsto ha_nonneg
    suffices hL0 : L = 0 by
      have hnw : ‖w‖ = 0 := by
        have h0 : ‖w‖ ^ 2 = 0 := hwsq.trans hL0
        exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h0
      exact norm_eq_zero.mp hnw
    by_contra hLne
    have hLpos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hLne)
    -- per-step compact inner approximations `Cⱼ ⊆ sⱼ` with content defect `≤ ofReal (L/4·(1/2)ʲ)`
    have hbudget : ∀ j, ∃ C, C ∈ supClosure jointRectangles ∧ C ⊆ s j ∧ IsCompact C ∧
        mR (s j \ C) ≤ ENNReal.ofReal (L / 4 * (1 / 2) ^ j) := by
      intro j
      apply jointElem_inner_compact A B hSC ξ (hs j)
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos (by linarith) (by positivity)
    choose C hCmem hCsub hCcp hCle using hbudget
    have hCclosed : ∀ j, IsClosed (C j) := fun j => (hCcp j).isClosed
    -- the decreasing compact family `Kₙ = ⋂_{j ∈ range (n+1)} Cⱼ`
    set K : ℕ → Set (ℝ × ℝ) := fun n => ⋂ j ∈ Finset.range (n + 1), C j with hKdef
    have hKsubC : ∀ n, K n ⊆ C n := fun n => by
      simp only [hKdef]; exact Set.biInter_subset_of_mem (Finset.self_mem_range_succ n)
    have hKsub0 : ∀ n, K n ⊆ C 0 := fun n => by
      simp only [hKdef]
      exact Set.biInter_subset_of_mem (Finset.mem_range.mpr (Nat.succ_pos n))
    have hKsubs : ∀ n, K n ⊆ s n := fun n => (hKsubC n).trans (hCsub n)
    have hKclosed : ∀ n, IsClosed (K n) := fun n => by
      simp only [hKdef]; exact isClosed_iInter fun j => isClosed_iInter fun _ => hCclosed j
    have hKcompact : ∀ n, IsCompact (K n) := fun n =>
      (hCcp 0).of_isClosed_subset (hKclosed n) (hKsub0 n)
    have hKmem : ∀ n, K n ∈ supClosure jointRectangles := fun n => by
      simp only [hKdef]
      exact hRing.biInter_mem (Finset.range (n + 1))
        (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)) fun j _ => hCmem j
    have hKdec : ∀ n, K (n + 1) ⊆ K n := by
      intro n x hx
      simp only [hKdef, Set.mem_iInter, Finset.mem_range] at hx ⊢
      exact fun j hj => hx j (by omega)
    -- the cumulative defect stays `≤ ofReal (L/2)`
    have hdefect : ∀ n, mR (s n \ K n) ≤ ENNReal.ofReal (L / 2) := by
      intro n
      have hsub : s n \ K n ⊆ ⋃ j ∈ Finset.range (n + 1), (s j \ C j) := by
        intro x hx
        obtain ⟨hxsn, hxnK⟩ := hx
        simp only [hKdef, Set.mem_iInter, Finset.mem_range, not_forall, exists_prop] at hxnK
        obtain ⟨j, hj, hxCj⟩ := hxnK
        exact Set.mem_biUnion (Finset.mem_range.mpr hj) ⟨hanti (Nat.lt_succ_iff.mp hj) hxsn, hxCj⟩
      calc mR (s n \ K n)
          ≤ mR (⋃ j ∈ Finset.range (n + 1), (s j \ C j)) :=
            addContent_mono hRing.isSetSemiring (hRing.diff_mem (hs n) (hKmem n))
              (hRing.biUnion_mem _ fun j _ => hRing.diff_mem (hs j) (hCmem j)) hsub
        _ ≤ ∑ j ∈ Finset.range (n + 1), mR (s j \ C j) :=
            addContent_biUnion_le hRing fun j _ => hRing.diff_mem (hs j) (hCmem j)
        _ ≤ ∑ j ∈ Finset.range (n + 1), ENNReal.ofReal (L / 4 * (1 / 2) ^ j) :=
            Finset.sum_le_sum fun j _ => hCle j
        _ = ENNReal.ofReal (∑ j ∈ Finset.range (n + 1), L / 4 * (1 / 2) ^ j) :=
            (ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity).symm
        _ ≤ ENNReal.ofReal (L / 2) := by
            apply ENNReal.ofReal_le_ofReal
            rw [← Finset.mul_sum]
            have hgeo : ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j ≤ 2 :=
              (summable_geometric_two.sum_le_tsum _ fun i _ => by positivity).trans_eq
                tsum_geometric_two
            calc L / 4 * ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j
                ≤ L / 4 * 2 := by apply mul_le_mul_of_nonneg_left hgeo (by linarith)
              _ = L / 2 := by ring
    -- each `Kₙ` is nonempty: its content is `≥ L/2 > 0`
    have hKne : ∀ n, (K n).Nonempty := by
      intro n
      rw [Set.nonempty_iff_ne_empty]
      intro hKempty
      have hdnetop : mR (s n \ K n) ≠ ⊤ :=
        jointContentRing_ne_top A B hSC ξ (hRing.diff_mem (hs n) (hKmem n))
      have hKnetop : mR (K n) ≠ ⊤ :=
        ne_top_of_le_ne_top (hmR_ne_top n)
          (addContent_mono hRing.isSetSemiring (hKmem n) (hs n) (hKsubs n))
      have hadd : mR (s n) = mR (K n) + mR (s n \ K n) := by
        conv_lhs => rw [(Set.union_diff_cancel (hKsubs n)).symm]
        exact addContent_union hRing (hKmem n) (hRing.diff_mem (hs n) (hKmem n))
          disjoint_sdiff_self_right
      have hareal : a n = (mR (K n)).toReal + (mR (s n \ K n)).toReal := by
        rw [hadef]; dsimp only; rw [hadd, ENNReal.toReal_add hKnetop hdnetop]
      have hdtoReal : (mR (s n \ K n)).toReal ≤ L / 2 := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdefect n)
        rwa [ENNReal.toReal_ofReal (by positivity)] at h
      have hKzero : (mR (K n)).toReal = 0 := by
        rw [hKempty, addContent_empty, ENNReal.toReal_zero]
      linarith [hL_le n, hareal, hdtoReal, hKzero, hLpos]
    -- finite intersection property: `⋂ₙ Kₙ ≠ ∅`, but `Kₙ ⊆ sₙ` and `⋂ₙ sₙ = ∅`
    have hmeet : (⋂ n, K n).Nonempty :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKdec hKne
        (hKcompact 0) hKclosed
    have hKsub_inter : (⋂ n, K n) ⊆ (⋂ n, s n) := Set.iInter_mono hKsubs
    rw [hempty] at hKsub_inter
    exact absurd (hmeet.mono hKsub_inter) (Set.not_nonempty_empty)
  -- conclude: `mR (s n) = ofReal (a n) → ofReal ‖w‖² = ofReal 0 = 0`
  have hmR_eq : ∀ n, mR (s n) = ENNReal.ofReal (a n) := fun n =>
    (ENNReal.ofReal_toReal (hmR_ne_top n)).symm
  have hgoal : Tendsto (fun n => mR (s n)) atTop (𝓝 (ENNReal.ofReal (‖w‖ ^ 2))) := by
    simp only [hmR_eq]
    exact (ENNReal.continuous_ofReal.tendsto _).comp ha_to_w
  rw [hw0, norm_zero] at hgoal
  simpa using hgoal

/-- **σ-subadditivity of the rectangle content.**  The semiring content `jointContent` is
σ-subadditive.  Proof: build the σ-additive ring content `mR` on the sup-closure ring via
`addContent_iUnion_eq_sum_of_tendsto_zero` (finiteness `jointContentRing_ne_top` + ∅-continuity
`jointContentRing_tendsto_empty`), get `mR.IsSigmaSubadditive`
(`isSigmaSubadditive_of_addContent_iUnion_eq_tsum`), then transfer down to the rectangles via
`supClosure_apply_of_mem` (a rectangle is its own one-element sup-closure value).  Rests on the open
∅-continuity, hence transitively `sorry`-dependent. -/
theorem jointContent_isSigmaSubadditive (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (ξ : H) : (jointContent A B hSC ξ).IsSigmaSubadditive := by
  have hRing : MeasureTheory.IsSetRing (supClosure jointRectangles) :=
    isSetSemiring_jointRectangles.isSetRing_supClosure
  set mR := (jointContent A B hSC ξ).supClosure isSetSemiring_jointRectangles with hmR
  have m_iUnion : ∀ (f : ℕ → Set (ℝ × ℝ)) (_ : ∀ i, f i ∈ supClosure jointRectangles)
      (_ : (⋃ i, f i) ∈ supClosure jointRectangles)
      (_ : Pairwise (Function.onFun Disjoint f)),
      mR (⋃ i, f i) = ∑' i, mR (f i) :=
    fun f hf hUf hdisj =>
      MeasureTheory.addContent_iUnion_eq_sum_of_tendsto_zero hRing mR
        (fun s hs => jointContentRing_ne_top A B hSC ξ hs)
        (fun s hs hanti hempty => jointContentRing_tendsto_empty A B hSC ξ hs hanti hempty)
        hf hUf hdisj
  have hRsub : mR.IsSigmaSubadditive :=
    MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum hRing m_iUnion
  intro f hf hUf
  have hfR : ∀ i, f i ∈ supClosure jointRectangles := fun i => subset_supClosure (hf i)
  have hUfR : (⋃ i, f i) ∈ supClosure jointRectangles := subset_supClosure hUf
  have key := hRsub hfR hUfR
  rwa [(jointContent A B hSC ξ).supClosure_apply_of_mem isSetSemiring_jointRectangles hUf,
    show (fun i => mR (f i)) = (fun i => jointContent A B hSC ξ (f i)) from
      funext fun i => (jointContent A B hSC ξ).supClosure_apply_of_mem
        isSetSemiring_jointRectangles (hf i)] at key

/-- **The rectangle semiring generates the Borel σ-algebra of `ℝ × ℝ`.**  `jointRectangles`
(`= image2 (· ×ˢ ·) {MeasurableSet} {MeasurableSet}` after reordering existentials) generates the
product measurable space `Prod.instMeasurableSpace`, which is the ambient instance
(`generateFrom_prod`).  Supplies the `hC_gen` equality for the Carathéodory extension. -/
theorem generateFrom_jointRectangles :
    (inferInstance : MeasurableSpace (ℝ × ℝ))
      = MeasurableSpace.generateFrom jointRectangles := by
  have hset : jointRectangles
      = Set.image2 (· ×ˢ ·) {s : Set ℝ | MeasurableSet s} {t : Set ℝ | MeasurableSet t} := by
    ext R
    simp only [jointRectangles, Set.mem_setOf_eq, Set.mem_image2]
    constructor
    · rintro ⟨S, T, hS, hT, rfl⟩; exact ⟨S, hS, T, hT, rfl⟩
    · rintro ⟨S, hS, T, hT, rfl⟩; exact ⟨S, T, hS, hT, rfl⟩
  rw [hset, generateFrom_prod]

/-- **The per-state joint scalar measure `μ_ξ`.**  The Carathéodory extension of the rectangle
content `jointContent` to a (finite, see below) Borel measure on `ℝ × ℝ`. -/
noncomputable def jointScalarMeasure (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (ξ : H) : MeasureTheory.Measure (ℝ × ℝ) :=
  (jointContent A B hSC ξ).measure isSetSemiring_jointRectangles
    generateFrom_jointRectangles.le (jointContent_isSigmaSubadditive A B hSC ξ)

/-- **`μ_ξ` on a rectangle is the bimeasure value.**  `μ_ξ(S ×ˢ T) = μ^A_{E_B(T)ξ}(S)` — the
Carathéodory measure agrees with the content on the semiring (`AddContent.measure_eq`), and the
content on a rectangle is the diagonal form (`jointRectVal_prod_diag`). -/
theorem jointScalarMeasure_prod (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    jointScalarMeasure A B hSC ξ (S ×ˢ T)
      = (A.spectralPVM.diag (B.spectralPVM.proj T hT ξ)) S := by
  have hmem : (S ×ˢ T) ∈ jointRectangles := ⟨S, T, hS, hT, rfl⟩
  rw [jointScalarMeasure, (jointContent A B hSC ξ).measure_eq isSetSemiring_jointRectangles
    generateFrom_jointRectangles (jointContent_isSigmaSubadditive A B hSC ξ) hmem]
  show jointRectVal A B ξ (S ×ˢ T) = _
  rw [jointRectVal_prod_diag A B hSC ξ hS hT]

/-- **`μ_ξ` on a rectangle, in norm² form.**  `μ_ξ(S ×ˢ T).toReal = ‖E_A(S)E_B(T)ξ‖²`. -/
theorem jointScalarMeasure_prod_norm_sq (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (ξ : H) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (jointScalarMeasure A B hSC ξ (S ×ˢ T)).toReal
      = ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2 := by
  rw [jointScalarMeasure_prod A B hSC ξ hS hT, ← jointRect_norm_sq_eq_diag A B hSC hS hT ξ]

/-- **`μ_ξ` is finite**, with total mass `‖ξ‖²`: `μ_ξ(univ) = μ_ξ(univ ×ˢ univ) = ‖ξ‖² < ∞`. -/
instance jointScalarMeasure_isFiniteMeasure (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (ξ : H) :
    MeasureTheory.IsFiniteMeasure (jointScalarMeasure A B hSC ξ) := by
  constructor
  have hmem : (Set.univ ×ˢ Set.univ : Set (ℝ × ℝ)) ∈ jointRectangles :=
    ⟨Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ, rfl⟩
  rw [← Set.univ_prod_univ, jointScalarMeasure,
    (jointContent A B hSC ξ).measure_eq isSetSemiring_jointRectangles
      generateFrom_jointRectangles (jointContent_isSigmaSubadditive A B hSC ξ) hmem,
    jointContent_univ A B hSC ξ]
  exact ENNReal.ofReal_lt_top

/-! ## G2.3 — `μ_ξ(E)` is a quadratic form in `ξ` (the operator-field foundation)

For the operator field `effect E` (built by polarizing `ξ ↦ μ_ξ(E)`) to exist, the real quadratic
form `q_E(ξ) = μ_ξ(E)` must satisfy the parallelogram law.  This holds for **every** measurable
`E ⊆ ℝ²` by a Dynkin (π–λ) induction over the rectangle π-system: on rectangles it is the diagonal
parallelogram of the projection `E_A(S)E_B(T)`; it passes to complements (`μ_ξ(Eᶜ) = ‖ξ‖² − μ_ξ(E)`,
with the norm's own parallelogram law) and to countable disjoint unions (σ-additivity of the genuine
measure `μ_ξ`). -/

/-- **`μ_ξ(E)` satisfies the parallelogram law in `ξ`, for every measurable `E`.**  Hence
`ξ ↦ μ_ξ(E)` is a bounded (`≤ ‖ξ‖²`) quadratic form, and polarizes to the sesquilinear form of the
operator `effect E` (G2.3).  Proved by Dynkin induction on the rectangle π-system. -/
theorem jointScalarMeasure_parallelogram (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ : H) :
    (jointScalarMeasure A B hSC (ψ + φ) E).toReal
        + (jointScalarMeasure A B hSC (ψ - φ) E).toReal
      = 2 * (jointScalarMeasure A B hSC ψ E).toReal
        + 2 * (jointScalarMeasure A B hSC φ E).toReal := by
  classical
  set q : Set (ℝ × ℝ) → H → ℝ := fun E ξ => (jointScalarMeasure A B hSC ξ E).toReal with hq
  have hqE : ∀ (E : Set (ℝ × ℝ)) (ξ : H),
      q E ξ = (jointScalarMeasure A B hSC ξ E).toReal := fun _ _ => rfl
  -- the diagonal of an operator obeys the real parallelogram law (inlined `diag_parallelogram`)
  have hrepar : ∀ (P : H →L[ℂ] H) (ψ φ : H),
      (⟪ψ + φ, P (ψ + φ)⟫_ℂ).re + (⟪ψ - φ, P (ψ - φ)⟫_ℂ).re
        = 2 * (⟪ψ, P ψ⟫_ℂ).re + 2 * (⟪φ, P φ⟫_ℂ).re := by
    intro P ψ φ
    have h : ⟪ψ + φ, P (ψ + φ)⟫_ℂ + ⟪ψ - φ, P (ψ - φ)⟫_ℂ
        = 2 * ⟪ψ, P ψ⟫_ℂ + 2 * ⟪φ, P φ⟫_ℂ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]; ring
    have h2 := congrArg Complex.re h
    simpa using h2
  -- total mass `q univ ξ = ‖ξ‖²`
  have hmass : ∀ ξ : H, q Set.univ ξ = ‖ξ‖ ^ 2 := by
    intro ξ
    have hu : jointScalarMeasure A B hSC ξ Set.univ = A.spectralPVM.diag ξ Set.univ := by
      rw [← Set.univ_prod_univ,
        jointScalarMeasure_prod A B hSC ξ MeasurableSet.univ MeasurableSet.univ,
        B.spectralPVM.proj_univ, ContinuousLinearMap.id_apply]
    rw [hqE, hu, A.spectralPVM.diag_univ_toReal]
  -- the property is closed under the Dynkin operations on the rectangle π-system
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ φ : H, q E (ψ + φ) + q E (ψ - φ) = 2 * q E ψ + 2 * q E φ)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ φ
  · -- empty
    intro ψ φ; simp only [hqE, measure_empty, ENNReal.toReal_zero, mul_zero, add_zero]
  · -- basic: rectangles, via the projection's diagonal parallelogram
    rintro _ ⟨S, T, hS, hT, rfl⟩ ψ φ
    have hbasic : ∀ ξ : H, q (S ×ˢ T) ξ
        = (⟪ξ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ).re := by
      intro ξ
      rw [hqE, jointScalarMeasure_prod_norm_sq A B hSC ξ hS hT,
        norm_sq_apply_of_isStarProjection (jointRect_isStarProjection A B hSC hS hT) ξ]
    rw [hbasic, hbasic, hbasic, hbasic]
    exact hrepar _ ψ φ
  · -- complement: `q Eᶜ ξ = ‖ξ‖² − q E ξ`
    intro t htm ih ψ φ
    have hcompl : ∀ ξ : H, q tᶜ ξ = ‖ξ‖ ^ 2 - q t ξ := by
      intro ξ
      have hle : jointScalarMeasure A B hSC ξ t ≤ jointScalarMeasure A B hSC ξ Set.univ :=
        measure_mono (Set.subset_univ t)
      rw [hqE tᶜ ξ, measure_compl htm (measure_ne_top _ _),
        ENNReal.toReal_sub_of_le hle (measure_ne_top _ _), ← hqE t ξ, ← hqE Set.univ ξ, hmass]
    rw [hcompl, hcompl, hcompl, hcompl]
    have hpar := parallelogram_law_with_norm ℂ ψ φ
    have hih := ih ψ φ
    nlinarith [hpar, hih]
  · -- countable disjoint union: σ-additivity of `μ_ξ`
    intro f hfd hfm ih ψ φ
    have hsum : ∀ ξ : H, q (⋃ i, f i) ξ = ∑' i, q (f i) ξ := by
      intro ξ
      rw [hqE, measure_iUnion hfd hfm, ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _)]
    have hsummable : ∀ ξ : H, Summable (fun i => q (f i) ξ) := by
      intro ξ
      apply ENNReal.summable_toReal
      rw [← measure_iUnion hfd hfm]
      exact measure_ne_top _ _
    rw [hsum, hsum, hsum, hsum,
      ← (hsummable (ψ + φ)).tsum_add (hsummable (ψ - φ)),
      ← tsum_mul_left, ← tsum_mul_left,
      ← ((hsummable ψ).mul_left 2).tsum_add ((hsummable φ).mul_left 2)]
    exact tsum_congr fun i => ih i ψ φ

/-! ## G2.3 — the operator field `jointEffect E` (polarizing the quadratic form `μ_ξ(E)`)

The quadratic form `q_E(ξ) = μ_ξ(E)` polarizes to `crossMeasureForm E ψ φ =
¼(q_E(ψ+φ) − q_E(ψ−φ) − i·q_E(ψ+iφ) + i·q_E(ψ−iφ))`, a bounded sesquilinear form in `(ψ, φ)`.  Each
sesquilinear identity is proved by Dynkin induction over the rectangle π-system, reducing to the
rectangle case `crossMeasureForm (S ×ˢ T) ψ φ = ⟪ψ, E_A(S)E_B(T) φ⟫` where it is the (honest,
ℂ-linear) projection effect.  Riesz packaging (`continuousLinearMapOfBilin`, then adjoint) turns the
form into the operator `jointEffect E`, with `⟪ξ, jointEffect E ξ⟫ = μ_ξ(E)` (the diagonal collapse
`crossMeasureForm_diag`) and `jointEffect (S ×ˢ T) = E_A(S)E_B(T)`. -/

omit [CompleteSpace H] in
/-- **Polarization, right slot.**  The off-diagonal `⟪ψ, T φ⟫` is the fixed `ℂ`-combination of the
diagonal `z ↦ ⟪z, T z⟫` — the mirror of `inner_op_eq_polarization` (which polarizes `⟪T ψ, φ⟫`).
Holds for *any* `T` (no self-adjointness). -/
theorem inner_polarization_right (T : H →L[ℂ] H) (ψ φ : H) :
    ⟪ψ, T φ⟫_ℂ = (1 / 4 : ℂ) *
      ( ⟪ψ + φ, T (ψ + φ)⟫_ℂ - ⟪ψ - φ, T (ψ - φ)⟫_ℂ
        - I * ⟪ψ + I • φ, T (ψ + I • φ)⟫_ℂ + I * ⟪ψ - I • φ, T (ψ - I • φ)⟫_ℂ ) := by
  have hI : (starRingEnd ℂ) I = -I := by change star I = -I; simp [Complex.conj_I]
  simp only [map_add, map_sub, map_smul,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, hI]
  ring_nf; simp only [Complex.I_sq]; ring

/-- The **complex polarized form** of the joint scalar measure: `crossMeasureForm E ψ φ` is the
`ℂ`-combination of the four real masses `μ_{ψ±φ}(E)`, `μ_{ψ±iφ}(E)` whose diagonal is `μ_ξ(E)` and
whose rectangle value is `⟪ψ, E_A(S)E_B(T) φ⟫`.  It is the sesquilinear form of `jointEffect E`. -/
noncomputable def crossMeasureForm (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (E : Set (ℝ × ℝ)) (ψ φ : H) : ℂ :=
  (1 / 4 : ℂ) *
    ( ((jointScalarMeasure A B hSC (ψ + φ) E).toReal : ℂ)
      - ((jointScalarMeasure A B hSC (ψ - φ) E).toReal : ℂ)
      - I * ((jointScalarMeasure A B hSC (ψ + I • φ) E).toReal : ℂ)
      + I * ((jointScalarMeasure A B hSC (ψ - I • φ) E).toReal : ℂ) )

omit [CompleteSpace H] in
/-- The diagonal `⟪ξ, ξ⟫` as a complex coercion of `‖ξ‖²` (a `Complex.ofReal`-headed restatement of
`inner_self_eq_norm_sq_to_K`, robust under the `RCLike`/`Complex` coercion split). -/
theorem inner_self_complex (ξ : H) : ⟪ξ, ξ⟫_ℂ = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- **Complement mass.**  `μ_ξ(Eᶜ) = ‖ξ‖² − μ_ξ(E)`, since the total mass is `‖ξ‖²`. -/
theorem jointScalarMeasure_compl_toReal (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (ξ : H) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    (jointScalarMeasure A B hSC ξ Eᶜ).toReal
      = ‖ξ‖ ^ 2 - (jointScalarMeasure A B hSC ξ E).toReal := by
  have hle : jointScalarMeasure A B hSC ξ E ≤ jointScalarMeasure A B hSC ξ Set.univ :=
    measure_mono (Set.subset_univ E)
  have hmass : (jointScalarMeasure A B hSC ξ Set.univ).toReal = ‖ξ‖ ^ 2 := by
    have hu : jointScalarMeasure A B hSC ξ Set.univ = A.spectralPVM.diag ξ Set.univ := by
      rw [← Set.univ_prod_univ,
        jointScalarMeasure_prod A B hSC ξ MeasurableSet.univ MeasurableSet.univ,
        B.spectralPVM.proj_univ, ContinuousLinearMap.id_apply]
    rw [hu, A.spectralPVM.diag_univ_toReal]
  rw [measure_compl hE (measure_ne_top _ _),
    ENNReal.toReal_sub_of_le hle (measure_ne_top _ _), hmass]

/-- **Diagonal of the rectangle effect.**  `μ_ξ(S ×ˢ T) = ⟪ξ, E_A(S)E_B(T) ξ⟫`: the diagonal mass is
the diagonal of the (self-adjoint, idempotent) rectangle projection (`norm_sq_apply_of_isStarProjection`
for the real part; idempotence + self-adjointness for vanishing imaginary part). -/
theorem jointRect_diag_complex (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (ξ : H) :
    ((jointScalarMeasure A B hSC ξ (S ×ˢ T)).toReal : ℂ)
      = ⟪ξ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ := by
  have hsp := jointRect_isStarProjection A B hSC hS hT
  have h1 : ⟪(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ,
      (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ
      = ⟪ξ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsp.isSelfAdjoint.adjoint_eq,
      ← ContinuousLinearMap.mul_apply, hsp.isIdempotentElem.eq]
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re, jointScalarMeasure_prod_norm_sq A B hSC ξ hS hT,
      norm_sq_apply_of_isStarProjection hsp ξ]
  · rw [Complex.ofReal_im, ← h1]
    exact (inner_self_im (𝕜 := ℂ) _).symm

/-- **Base case.**  On a rectangle the form is the honest projection effect:
`crossMeasureForm (S ×ˢ T) ψ φ = ⟪ψ, E_A(S)E_B(T) φ⟫` — each diagonal mass is the star-projection
diagonal (`jointRect_diag_complex`) and polarization (`inner_polarization_right`) reassembles it. -/
theorem crossMeasureForm_rect (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (ψ φ : H) :
    crossMeasureForm A B hSC (S ×ˢ T) ψ φ
      = ⟪ψ, (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) φ⟫_ℂ := by
  rw [crossMeasureForm, jointRect_diag_complex A B hSC hS hT (ψ + φ),
    jointRect_diag_complex A B hSC hS hT (ψ - φ), jointRect_diag_complex A B hSC hS hT (ψ + I • φ),
    jointRect_diag_complex A B hSC hS hT (ψ - I • φ),
    inner_polarization_right (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ψ φ]

/-- **Complement closure.**  `crossMeasureForm Eᶜ ψ φ = ⟪ψ, φ⟫ − crossMeasureForm E ψ φ`: the four
masses split as `μ_z(Eᶜ) = ‖z‖² − μ_z(E)`, the `‖·‖²` part polarizes to the inner product `⟪ψ, φ⟫`
(`inner_polarization_right` at `id`), and the rest is `−crossMeasureForm E`. -/
theorem crossMeasureForm_compl (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ : H) :
    crossMeasureForm A B hSC Eᶜ ψ φ = ⟪ψ, φ⟫_ℂ - crossMeasureForm A B hSC E ψ φ := by
  have hc : ∀ z : H, ((jointScalarMeasure A B hSC z Eᶜ).toReal : ℂ)
      = ((‖z‖ ^ 2 : ℝ) : ℂ) - ((jointScalarMeasure A B hSC z E).toReal : ℂ) := by
    intro z; rw [jointScalarMeasure_compl_toReal A B hSC z hE]; push_cast; ring
  have hnorm : ⟪ψ, φ⟫_ℂ = (1 / 4 : ℂ) *
      ( ((‖ψ + φ‖ ^ 2 : ℝ) : ℂ) - ((‖ψ - φ‖ ^ 2 : ℝ) : ℂ)
        - I * ((‖ψ + I • φ‖ ^ 2 : ℝ) : ℂ) + I * ((‖ψ - I • φ‖ ^ 2 : ℝ) : ℂ) ) := by
    have h := inner_polarization_right (ContinuousLinearMap.id ℂ H) ψ φ
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h]; simp only [inner_self_complex]
  rw [crossMeasureForm, crossMeasureForm, hc (ψ + φ), hc (ψ - φ), hc (ψ + I • φ), hc (ψ - I • φ),
    hnorm]
  ring

/-- **Countable disjoint-union closure.**  `crossMeasureForm (⋃ i, f i) ψ φ = ∑' i, crossMeasureForm
(f i) ψ φ`: each mass is σ-additive (`measure_iUnion`), `Complex.ofReal_tsum` moves the coercion
through, and `tsum` linearity reassembles the four series into one. -/
theorem crossMeasureForm_iUnion (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {f : ℕ → Set (ℝ × ℝ)} (hd : Pairwise (Function.onFun Disjoint f))
    (hm : ∀ i, MeasurableSet (f i)) (ψ φ : H) :
    crossMeasureForm A B hSC (⋃ i, f i) ψ φ = ∑' i, crossMeasureForm A B hSC (f i) ψ φ := by
  have hsumm : ∀ z : H, Summable (fun i => (jointScalarMeasure A B hSC z (f i)).toReal) := by
    intro z; apply ENNReal.summable_toReal; rw [← measure_iUnion hd hm]; exact measure_ne_top _ _
  have hsummC : ∀ z : H, Summable (fun i => ((jointScalarMeasure A B hSC z (f i)).toReal : ℂ)) :=
    fun z => (Complex.summable_ofReal).mpr (hsumm z)
  have hz : ∀ z : H, ((jointScalarMeasure A B hSC z (⋃ i, f i)).toReal : ℂ)
      = ∑' i, ((jointScalarMeasure A B hSC z (f i)).toReal : ℂ) := by
    intro z
    rw [measure_iUnion hd hm, ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _),
      Complex.ofReal_tsum]
  have s1 := hsummC (ψ + φ); have s2 := hsummC (ψ - φ)
  have s3 := hsummC (ψ + I • φ); have s4 := hsummC (ψ - I • φ)
  symm
  calc ∑' i, crossMeasureForm A B hSC (f i) ψ φ
      = (1 / 4 : ℂ) * ∑' i,
          ( ((jointScalarMeasure A B hSC (ψ + φ) (f i)).toReal : ℂ)
            - ((jointScalarMeasure A B hSC (ψ - φ) (f i)).toReal : ℂ)
            - I * ((jointScalarMeasure A B hSC (ψ + I • φ) (f i)).toReal : ℂ)
            + I * ((jointScalarMeasure A B hSC (ψ - I • φ) (f i)).toReal : ℂ) ) := by
        rw [← tsum_mul_left]; exact tsum_congr fun i => by rw [crossMeasureForm]
    _ = (1 / 4 : ℂ) *
          ( (∑' i, ((jointScalarMeasure A B hSC (ψ + φ) (f i)).toReal : ℂ))
            - (∑' i, ((jointScalarMeasure A B hSC (ψ - φ) (f i)).toReal : ℂ))
            - I * (∑' i, ((jointScalarMeasure A B hSC (ψ + I • φ) (f i)).toReal : ℂ))
            + I * (∑' i, ((jointScalarMeasure A B hSC (ψ - I • φ) (f i)).toReal : ℂ)) ) := by
        congr 1
        rw [Summable.tsum_add ((s1.sub s2).sub (s3.mul_left I)) (s4.mul_left I),
          Summable.tsum_sub (s1.sub s2) (s3.mul_left I), Summable.tsum_sub s1 s2,
          tsum_mul_left, tsum_mul_left]
    _ = crossMeasureForm A B hSC (⋃ i, f i) ψ φ := by
        rw [crossMeasureForm, hz (ψ + φ), hz (ψ - φ), hz (ψ + I • φ), hz (ψ - I • φ)]

/-- **Summability** of the per-cell forms (each of the four masses is summable; the `ℂ`-combination
inherits it). -/
theorem crossMeasureForm_summable (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {f : ℕ → Set (ℝ × ℝ)}
    (hd : Pairwise (Function.onFun Disjoint f)) (hm : ∀ i, MeasurableSet (f i)) (ψ φ : H) :
    Summable (fun i => crossMeasureForm A B hSC (f i) ψ φ) := by
  have hsumm : ∀ z : H, Summable (fun i => ((jointScalarMeasure A B hSC z (f i)).toReal : ℂ)) := by
    intro z
    refine (Complex.summable_ofReal).mpr (ENNReal.summable_toReal ?_)
    rw [← measure_iUnion hd hm]; exact measure_ne_top _ _
  simp only [crossMeasureForm]
  exact Summable.mul_left _
    ((((hsumm _).sub (hsumm _)).sub ((hsumm _).mul_left I)).add ((hsumm _).mul_left I))

/-! ### Sesquilinearity of `crossMeasureForm` (by Dynkin induction over the rectangle π-system)

Each identity reduces — on rectangles — to (conjugate-)linearity of the honest projection effect
`⟪ψ, E_A(S)E_B(T) φ⟫`, and passes to complements (via `crossMeasureForm_compl` + the matching inner
identity) and to countable disjoint unions (via `crossMeasureForm_iUnion` + `tsum` linearity). -/

/-- Additive in the (conjugate-linear) left slot. -/
theorem crossMeasureForm_add_left (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ₁ ψ₂ φ : H) :
    crossMeasureForm A B hSC E (ψ₁ + ψ₂) φ
      = crossMeasureForm A B hSC E ψ₁ φ + crossMeasureForm A B hSC E ψ₂ φ := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ₁ ψ₂ φ : H, crossMeasureForm A B hSC E (ψ₁ + ψ₂) φ
      = crossMeasureForm A B hSC E ψ₁ φ + crossMeasureForm A B hSC E ψ₂ φ)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ₁ ψ₂ φ
  · intro ψ₁ ψ₂ φ; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ψ₁ ψ₂ φ
    rw [crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT, inner_add_left]
  · intro t htm ih ψ₁ ψ₂ φ
    rw [crossMeasureForm_compl A B hSC htm, crossMeasureForm_compl A B hSC htm,
      crossMeasureForm_compl A B hSC htm, inner_add_left, ih ψ₁ ψ₂ φ]
    ring
  · intro g hgd hgm ih ψ₁ ψ₂ φ
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, crossMeasureForm_iUnion A B hSC hgd hgm,
      crossMeasureForm_iUnion A B hSC hgd hgm, ← (crossMeasureForm_summable A B hSC hgd hgm ψ₁ φ).tsum_add
        (crossMeasureForm_summable A B hSC hgd hgm ψ₂ φ)]
    exact tsum_congr fun i => ih i ψ₁ ψ₂ φ

/-- Conjugate-homogeneous in the left slot. -/
theorem crossMeasureForm_smul_left (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (c : ℂ) (ψ φ : H) :
    crossMeasureForm A B hSC E (c • ψ) φ
      = (starRingEnd ℂ) c * crossMeasureForm A B hSC E ψ φ := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ φ : H, crossMeasureForm A B hSC E (c • ψ) φ
      = (starRingEnd ℂ) c * crossMeasureForm A B hSC E ψ φ)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ φ
  · intro ψ φ; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ψ φ
    rw [crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT, inner_smul_left]
  · intro t htm ih ψ φ
    rw [crossMeasureForm_compl A B hSC htm, crossMeasureForm_compl A B hSC htm,
      inner_smul_left, ih ψ φ]
    ring
  · intro g hgd hgm ih ψ φ
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, crossMeasureForm_iUnion A B hSC hgd hgm,
      ← tsum_mul_left]
    exact tsum_congr fun i => ih i ψ φ

/-- Additive in the (linear) right slot. -/
theorem crossMeasureForm_add_right (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ₁ φ₂ : H) :
    crossMeasureForm A B hSC E ψ (φ₁ + φ₂)
      = crossMeasureForm A B hSC E ψ φ₁ + crossMeasureForm A B hSC E ψ φ₂ := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ φ₁ φ₂ : H, crossMeasureForm A B hSC E ψ (φ₁ + φ₂)
      = crossMeasureForm A B hSC E ψ φ₁ + crossMeasureForm A B hSC E ψ φ₂)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ φ₁ φ₂
  · intro ψ φ₁ φ₂; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ψ φ₁ φ₂
    rw [crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT, map_add,
      inner_add_right]
  · intro t htm ih ψ φ₁ φ₂
    rw [crossMeasureForm_compl A B hSC htm, crossMeasureForm_compl A B hSC htm,
      crossMeasureForm_compl A B hSC htm, inner_add_right, ih ψ φ₁ φ₂]
    ring
  · intro g hgd hgm ih ψ φ₁ φ₂
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, crossMeasureForm_iUnion A B hSC hgd hgm,
      crossMeasureForm_iUnion A B hSC hgd hgm, ← (crossMeasureForm_summable A B hSC hgd hgm ψ φ₁).tsum_add
        (crossMeasureForm_summable A B hSC hgd hgm ψ φ₂)]
    exact tsum_congr fun i => ih i ψ φ₁ φ₂

/-- Homogeneous in the (linear) right slot. -/
theorem crossMeasureForm_smul_right (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (c : ℂ) (ψ φ : H) :
    crossMeasureForm A B hSC E ψ (c • φ) = c * crossMeasureForm A B hSC E ψ φ := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ψ φ : H, crossMeasureForm A B hSC E ψ (c • φ)
      = c * crossMeasureForm A B hSC E ψ φ)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ψ φ
  · intro ψ φ; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ψ φ
    rw [crossMeasureForm_rect A B hSC hS hT, crossMeasureForm_rect A B hSC hS hT, map_smul, inner_smul_right]
  · intro t htm ih ψ φ
    rw [crossMeasureForm_compl A B hSC htm, crossMeasureForm_compl A B hSC htm,
      inner_smul_right, ih ψ φ]
    ring
  · intro g hgd hgm ih ψ φ
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, crossMeasureForm_iUnion A B hSC hgd hgm,
      ← tsum_mul_left]
    exact tsum_congr fun i => ih i ψ φ

/-- **Diagonal collapse.**  `crossMeasureForm E ξ ξ = μ_ξ(E)` for every measurable `E` — the
polarized form recovers the original quadratic form on the diagonal.  Dynkin induction: rectangles
(`jointRect_diag_complex`), complements (`jointScalarMeasure_compl_toReal` + `inner_self_complex`),
countable unions (σ-additivity). -/
theorem crossMeasureForm_diag (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ξ : H) :
    crossMeasureForm A B hSC E ξ ξ = ((jointScalarMeasure A B hSC ξ E).toReal : ℂ) := by
  refine MeasurableSpace.induction_on_inter
    (C := fun E _ => ∀ ξ : H,
      crossMeasureForm A B hSC E ξ ξ = ((jointScalarMeasure A B hSC ξ E).toReal : ℂ))
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ E hE ξ
  · intro ξ; simp [crossMeasureForm]
  · rintro _ ⟨S, T, hS, hT, rfl⟩ ξ
    rw [crossMeasureForm_rect A B hSC hS hT, ← jointRect_diag_complex A B hSC hS hT ξ]
  · intro t htm ih ξ
    rw [crossMeasureForm_compl A B hSC htm, ih ξ, inner_self_complex,
      jointScalarMeasure_compl_toReal A B hSC ξ htm]
    push_cast; ring
  · intro g hgd hgm ih ξ
    rw [crossMeasureForm_iUnion A B hSC hgd hgm, measure_iUnion hgd hgm,
      ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _), Complex.ofReal_tsum]
    exact tsum_congr fun i => ih i ξ

/-! ### Riesz packaging: the operator field `jointEffect E`

The bounded sesquilinear `crossMeasureForm E` is represented (`continuousLinearMapOfBilin`, adjoint)
by the operator `jointEffect E`, with `⟪ξ, jointEffect E ξ⟫ = μ_ξ(E)` (the POVM weld) and
`jointEffect (S ×ˢ T) = E_A(S)E_B(T)` (rectangle agreement). -/

/-- **Operator-norm bound** for the form, `‖crossMeasureForm E ψ φ‖ ≤ 2‖ψ‖‖φ‖`: a crude
`‖ψ‖²+‖φ‖²` bound (mass bound + the two parallelogram laws), homogenized by rescaling `φ ↦ t•φ`. -/
theorem crossMeasureForm_norm_le (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ : H) :
    ‖crossMeasureForm A B hSC E ψ φ‖ ≤ 2 * ‖ψ‖ * ‖φ‖ := by
  -- each mass `μ_z(E) ≤ μ_z(univ) = ‖z‖²`
  have hm_le : ∀ z : H, ‖((jointScalarMeasure A B hSC z E).toReal : ℂ)‖ ≤ ‖z‖ ^ 2 := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hu : jointScalarMeasure A B hSC z Set.univ = A.spectralPVM.diag z Set.univ := by
      rw [← Set.univ_prod_univ,
        jointScalarMeasure_prod A B hSC z MeasurableSet.univ MeasurableSet.univ,
        B.spectralPVM.proj_univ, ContinuousLinearMap.id_apply]
    calc (jointScalarMeasure A B hSC z E).toReal
        ≤ (jointScalarMeasure A B hSC z Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ E))
      _ = (A.spectralPVM.diag z Set.univ).toReal := by rw [hu]
      _ = ‖z‖ ^ 2 := A.spectralPVM.diag_univ_toReal z
  -- crude bound `‖crossMeasureForm E x y‖ ≤ ‖x‖² + ‖y‖²`
  have hmain : ∀ x y : H, ‖crossMeasureForm A B hSC E x y‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    have htri : ‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)
          - ((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)
          - I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)
          + I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖
        ≤ ‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)‖
          + ‖((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)‖
          + ‖((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖
          + ‖((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := by
      have eI3 : ‖I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖
          = ‖((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      have eI4 : ‖I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖
          = ‖((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      calc ‖_ - _ - I * _ + I * _‖
          ≤ ‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)
              - ((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)
              - I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖
            + ‖I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)
              - ((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)‖
            + ‖I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖)
            + ‖I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := by
              gcongr; exact norm_sub_le _ _
        _ ≤ ((‖((jointScalarMeasure A B hSC (x + y) E).toReal : ℂ)‖
              + ‖((jointScalarMeasure A B hSC (x - y) E).toReal : ℂ)‖)
            + ‖I * ((jointScalarMeasure A B hSC (x + I • y) E).toReal : ℂ)‖)
            + ‖I * ((jointScalarMeasure A B hSC (x - I • y) E).toReal : ℂ)‖ := by
              gcongr; exact norm_sub_le _ _
        _ = _ := by rw [eI3, eI4]
    have hpar1 : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
      parallelogram_law_with_norm ℂ x y
    have hpar2 : ‖x + I • y‖ ^ 2 + ‖x - I • y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      have h := parallelogram_law_with_norm ℂ x (I • y)
      rwa [norm_smul, Complex.norm_I, one_mul] at h
    rw [crossMeasureForm, norm_mul,
      show ‖(1 / 4 : ℂ)‖ = 1 / 4 by rw [norm_div, norm_one, Complex.norm_ofNat]]
    have hb := htri.trans (by
      gcongr <;> exact hm_le _ :
      _ ≤ ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 + ‖x + I • y‖ ^ 2 + ‖x - I • y‖ ^ 2)
    nlinarith [hb, hpar1, hpar2, norm_nonneg (crossMeasureForm A B hSC E x y)]
  -- homogenize: handle the zero slots, then rescale `φ ↦ (‖ψ‖/‖φ‖)•φ`
  rcases eq_or_ne φ 0 with rfl | hφ
  · have h0 : crossMeasureForm A B hSC E ψ 0 = 0 := by
      have := crossMeasureForm_smul_right A B hSC hE (0 : ℂ) ψ 0; simpa using this
    simp [h0]
  rcases eq_or_ne ψ 0 with rfl | hψ
  · have h0 : crossMeasureForm A B hSC E 0 φ = 0 := by
      have := crossMeasureForm_smul_left A B hSC hE (0 : ℂ) 0 φ; simpa using this
    simp [h0]
  have hψ0 : (0 : ℝ) < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hφ0 : (0 : ℝ) < ‖φ‖ := norm_pos_iff.mpr hφ
  set t : ℝ := ‖ψ‖ / ‖φ‖ with ht_def
  have ht : 0 < t := div_pos hψ0 hφ0
  have hb := hmain ψ ((t : ℂ) • φ)
  rw [crossMeasureForm_smul_right A B hSC hE (t : ℂ) ψ φ, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.le, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht.le] at hb
  have htφ : t * ‖φ‖ = ‖ψ‖ := by rw [ht_def]; field_simp
  have key : t * ‖crossMeasureForm A B hSC E ψ φ‖ ≤ ‖ψ‖ ^ 2 + (t * ‖φ‖) ^ 2 := hb
  rw [htφ] at key
  have hfinal : ‖crossMeasureForm A B hSC E ψ φ‖ ≤ (‖ψ‖ ^ 2 + ‖ψ‖ ^ 2) / t :=
    (le_div_iff₀' ht).mpr (by linarith [key])
  refine hfinal.trans (le_of_eq ?_)
  rw [ht_def, div_div_eq_mul_div, div_eq_iff hψ0.ne']
  ring

/-- The polarized pairing `(ψ, φ) ↦ crossMeasureForm E ψ φ`, bundled as a continuous sesquilinear
map (`mk₂'ₛₗ` with conjugation on the left slot; the bound is `crossMeasureForm_norm_le`). -/
noncomputable def crossMeasureFormBilin (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
      (fun ψ φ => crossMeasureForm A B hSC E ψ φ)
      (fun ψ₁ ψ₂ φ => crossMeasureForm_add_left A B hSC hE ψ₁ ψ₂ φ)
      (fun c ψ φ => by rw [crossMeasureForm_smul_left A B hSC hE c ψ φ, smul_eq_mul])
      (fun ψ φ₁ φ₂ => crossMeasureForm_add_right A B hSC hE ψ φ₁ φ₂)
      (fun c ψ φ => by
        rw [crossMeasureForm_smul_right A B hSC hE c ψ φ, RingHom.id_apply, smul_eq_mul]))
    2
    (fun ψ φ => crossMeasureForm_norm_le A B hSC hE ψ φ)

@[simp] theorem crossMeasureFormBilin_apply (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ψ φ : H) :
    crossMeasureFormBilin A B hSC hE ψ φ = crossMeasureForm A B hSC E ψ φ := rfl

/-- **The joint effect** `jointEffect E`: the operator whose sesquilinear form is `crossMeasureForm E`
(`continuousLinearMapOfBilin`, adjointed to put the operator in the second inner-product slot, as in
`spectralCalculus`). -/
noncomputable def jointEffect (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint
    (InnerProductSpace.continuousLinearMapOfBilin (crossMeasureFormBilin A B hSC hE))

/-- The defining identity: `⟪ξ, jointEffect E η⟫ = crossMeasureForm E ξ η`. -/
theorem jointEffect_inner (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ξ η : H) :
    ⟪ξ, jointEffect A B hSC hE η⟫_ℂ = crossMeasureForm A B hSC E ξ η := by
  simp only [jointEffect]
  rw [ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply, crossMeasureFormBilin_apply]

/-- **The POVM weld.**  `⟪ξ, jointEffect E ξ⟫ = μ_ξ(E)` — the diagonal of the joint effect is the
joint scalar measure. -/
theorem jointEffect_diag (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ξ : H) :
    ⟪ξ, jointEffect A B hSC hE ξ⟫_ℂ = ((jointScalarMeasure A B hSC ξ E).toReal : ℂ) := by
  rw [jointEffect_inner, crossMeasureForm_diag A B hSC hE ξ]

/-- **Rectangle agreement.**  `jointEffect (S ×ˢ T) = E_A(S)·E_B(T)` — the joint effect on a
rectangle is the product of the spectral projections (determined by the diagonal,
`op_ext_of_inner_self`). -/
theorem jointEffect_rect (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    jointEffect A B hSC (hS.prod hT) = A.spectralPVM.proj S hS * B.spectralPVM.proj T hT := by
  refine op_ext_of_inner_self fun ξ => ?_
  rw [jointEffect_inner, crossMeasureForm_rect A B hSC hS hT]

/-- **Normalization.**  `jointEffect univ = 1`. -/
theorem jointEffect_univ (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B) :
    jointEffect A B hSC (MeasurableSet.univ : MeasurableSet (Set.univ : Set (ℝ × ℝ)))
      = ContinuousLinearMap.id ℂ H := by
  refine op_ext_of_inner_self fun ξ => ?_
  rw [jointEffect_diag, ContinuousLinearMap.id_apply, inner_self_complex]
  congr 1
  rw [← Set.univ_prod_univ,
    jointScalarMeasure_prod A B hSC ξ MeasurableSet.univ MeasurableSet.univ,
    B.spectralPVM.proj_univ, ContinuousLinearMap.id_apply, A.spectralPVM.diag_univ_toReal]

/-! ### The joint POVM and its cylinder marginals (G2.5)

`jointEffect` assembles into a `POVM H (ℝ × ℝ)`: the weld `inner_effect` is `jointEffect_diag`, the
normalization is `jointEffect_univ`, and the diagonal data is the joint scalar measure `μ_ξ`.  Its
`IsJointOf A B` is then immediate from rectangle agreement (`jointEffect_rect`) — `M(S × ℝ) =
E_A(S)·E_B(ℝ) = E_A(S)·1 = E_A(S)`.  (`IsProjective` — operator multiplicativity on *all* sets, G2.4 —
remains; on rectangles it is `jointRect_mul`, but the extension to the full product σ-algebra needs
the operator-level σ-additivity of the multivariate spectral theorem.) -/

/-- **The joint POVM** of a strongly-commuting pair: the operator-valued measure on `ℝ²` whose
effects are `jointEffect` and whose diagonal data is the joint scalar measure `μ_ξ`. -/
noncomputable def jointPOVM (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B) :
    POVM H (ℝ × ℝ) where
  effect _ hE := jointEffect A B hSC hE
  diag ξ := jointScalarMeasure A B hSC ξ
  diag_finite ξ := jointScalarMeasure_isFiniteMeasure A B hSC ξ
  inner_effect _ hE ξ := jointEffect_diag A B hSC hE ξ
  effect_univ := jointEffect_univ A B hSC

/-- **G2.5 — the joint POVM has the right cylinder marginals.**  `M(S × ℝ) = E_A(S)` and
`M(ℝ × T) = E_B(T)`: immediate from `jointEffect_rect` and `proj_univ` (the other factor is the
identity).  This is the hypothesis that couples the joint PVM to `A` and `B` (`IsJointOf`). -/
theorem jointPOVM_isJointOf (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B) :
    (jointPOVM A B hSC).IsJointOf A B := by
  refine ⟨fun S hS => ?_, fun T hT => ?_⟩
  · show jointEffect A B hSC (hS.prod MeasurableSet.univ) = A.spectralPVM.proj S hS
    rw [jointEffect_rect A B hSC hS MeasurableSet.univ, B.spectralPVM.proj_univ]
    exact mul_one _
  · show jointEffect A B hSC (MeasurableSet.univ.prod hT) = B.spectralPVM.proj T hT
    rw [jointEffect_rect A B hSC MeasurableSet.univ hT, A.spectralPVM.proj_univ]
    exact one_mul _

/-! ### G2.4 — `IsProjective`: the joint effects are multiplicative

`jointEffect (B₁ ∩ B₂) = jointEffect B₁ · jointEffect B₂` for *all* measurable `B₁, B₂` — operator
multiplicativity, the field that upgrades the POVM to a genuine PVM.  Proof: two nested Dynkin
inductions (`induction_on_inter`) at the **sesquilinear-form** level, where σ-additivity is the clean
`crossMeasureForm_iUnion` and no operator-topology σ-additivity is ever needed.  The right factor is
reduced to a rectangle first (`crossMeasureForm_inter_rect`, induct over `B₁`), then the left factor
to an arbitrary set (`crossMeasureForm_inter`, induct over `B₂`), using self-adjointness of
`jointEffect B₁` to keep the inner-product vectors fixed across the second induction. -/

/-- **Finite additivity of `crossMeasureForm`** in its set argument: each diagonal mass
`μ_z(X ∪ Y) = μ_z(X) + μ_z(Y)` (`measure_union`), and the polarization is linear in the masses. -/
theorem crossMeasureForm_union2 (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {X Y : Set (ℝ × ℝ)} (_hX : MeasurableSet X) (hY : MeasurableSet Y) (hd : Disjoint X Y) (ψ φ : H) :
    crossMeasureForm A B hSC (X ∪ Y) ψ φ
      = crossMeasureForm A B hSC X ψ φ + crossMeasureForm A B hSC Y ψ φ := by
  have hm : ∀ z : H, ((jointScalarMeasure A B hSC z (X ∪ Y)).toReal : ℂ)
      = ((jointScalarMeasure A B hSC z X).toReal : ℂ) + ((jointScalarMeasure A B hSC z Y).toReal : ℂ) := by
    intro z
    rw [measure_union hd hY, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    push_cast; ring
  rw [crossMeasureForm, crossMeasureForm, crossMeasureForm,
    hm (ψ + φ), hm (ψ - φ), hm (ψ + I • φ), hm (ψ - I • φ)]
  ring

/-- **Each joint effect is self-adjoint.**  `⟪ξ, jointEffect E ξ⟫ = μ_ξ(E)` is real for every `ξ`
(`jointEffect_diag`), and a real diagonal characterizes self-adjointness. -/
theorem jointEffect_isSelfAdjoint (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) : IsSelfAdjoint (jointEffect A B hSC hE) :=
  (jointPOVM A B hSC).isSelfAdjoint_effect E hE

/-- The self-adjointness swap: `⟪jointEffect E ζ, ω⟫ = ⟪ζ, jointEffect E ω⟫`. -/
theorem jointEffect_swap (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (ζ ω : H) :
    ⟪(jointEffect A B hSC hE) ζ, ω⟫_ℂ = ⟪ζ, (jointEffect A B hSC hE) ω⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, (jointEffect_isSelfAdjoint A B hSC hE).adjoint_eq]

/-- **Step A — right factor a rectangle.**  `crossMeasureForm (B₁ ∩ (S₂×T₂)) ξ η =
crossMeasureForm B₁ ξ (jointEffect (S₂×T₂) η)` for all measurable `B₁`.  Dynkin induction over `B₁`
on the rectangle π-system: base = `jointRect_mul`, complement/⋃ = `crossMeasureForm_compl`/`_iUnion`
with the vectors `(ξ, jointEffect (S₂×T₂) η)` fixed. -/
theorem crossMeasureForm_inter_rect (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {S₂ T₂ : Set ℝ} (hS₂ : MeasurableSet S₂) (hT₂ : MeasurableSet T₂)
    {B₁ : Set (ℝ × ℝ)} (hB₁ : MeasurableSet B₁) :
    ∀ ξ η : H, crossMeasureForm A B hSC (B₁ ∩ (S₂ ×ˢ T₂)) ξ η
      = crossMeasureForm A B hSC B₁ ξ (jointEffect A B hSC (hS₂.prod hT₂) η) := by
  refine MeasurableSpace.induction_on_inter
    (C := fun B₁ _ => ∀ ξ η : H, crossMeasureForm A B hSC (B₁ ∩ (S₂ ×ˢ T₂)) ξ η
      = crossMeasureForm A B hSC B₁ ξ (jointEffect A B hSC (hS₂.prod hT₂) η))
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ B₁ hB₁
  · intro ξ η
    rw [Set.empty_inter]; simp [crossMeasureForm]
  · rintro _ ⟨S₁, T₁, hS₁, hT₁, rfl⟩ ξ η
    rw [Set.prod_inter_prod, crossMeasureForm_rect A B hSC (hS₁.inter hS₂) (hT₁.inter hT₂),
      crossMeasureForm_rect A B hSC hS₁ hT₁, jointEffect_rect A B hSC hS₂ hT₂,
      show (A.spectralPVM.proj S₁ hS₁ * B.spectralPVM.proj T₁ hT₁)
          ((A.spectralPVM.proj S₂ hS₂ * B.spectralPVM.proj T₂ hT₂) η)
        = (A.spectralPVM.proj (S₁ ∩ S₂) (hS₁.inter hS₂)
            * B.spectralPVM.proj (T₁ ∩ T₂) (hT₁.inter hT₂)) η from by
        rw [← ContinuousLinearMap.mul_apply, jointRect_mul A B hSC hS₁ hS₂ hT₁ hT₂]]
  · intro t htm ih ξ η
    have hd : Disjoint (t ∩ (S₂ ×ˢ T₂)) (tᶜ ∩ (S₂ ×ˢ T₂)) := by
      rw [Set.disjoint_left]; rintro x ⟨hxt, _⟩ ⟨hxtc, _⟩; exact hxtc hxt
    have hunion : (t ∩ (S₂ ×ˢ T₂)) ∪ (tᶜ ∩ (S₂ ×ˢ T₂)) = S₂ ×ˢ T₂ := by
      rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
    have hkey : crossMeasureForm A B hSC (S₂ ×ˢ T₂) ξ η
        = crossMeasureForm A B hSC (t ∩ (S₂ ×ˢ T₂)) ξ η
          + crossMeasureForm A B hSC (tᶜ ∩ (S₂ ×ˢ T₂)) ξ η := by
      conv_lhs => rw [← hunion]
      exact crossMeasureForm_union2 A B hSC (htm.inter (hS₂.prod hT₂))
        (htm.compl.inter (hS₂.prod hT₂)) hd ξ η
    rw [crossMeasureForm_compl A B hSC htm, ← ih ξ η,
      jointEffect_inner A B hSC (hS₂.prod hT₂) ξ η, hkey]
    ring
  · intro g hgd hgm ih ξ η
    rw [Set.iUnion_inter,
      crossMeasureForm_iUnion A B hSC
        (fun i j hij => (hgd hij).mono Set.inter_subset_left Set.inter_subset_left)
        (fun i => (hgm i).inter (hS₂.prod hT₂)),
      crossMeasureForm_iUnion A B hSC hgd hgm]
    exact tsum_congr fun i => ih i ξ η

/-- **Step B — both factors arbitrary.**  `crossMeasureForm (B₁ ∩ B₂) ξ η =
crossMeasureForm B₂ (jointEffect B₁ ξ) η`.  Dynkin induction over `B₂`: base = Step A + the
self-adjointness swap of `jointEffect B₁`, complement/⋃ with the vectors `(jointEffect B₁ ξ, η)`
fixed. -/
theorem crossMeasureForm_inter (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {B₁ : Set (ℝ × ℝ)} (hB₁ : MeasurableSet B₁) {B₂ : Set (ℝ × ℝ)} (hB₂ : MeasurableSet B₂) :
    ∀ ξ η : H, crossMeasureForm A B hSC (B₁ ∩ B₂) ξ η
      = crossMeasureForm A B hSC B₂ (jointEffect A B hSC hB₁ ξ) η := by
  refine MeasurableSpace.induction_on_inter
    (C := fun B₂ _ => ∀ ξ η : H, crossMeasureForm A B hSC (B₁ ∩ B₂) ξ η
      = crossMeasureForm A B hSC B₂ (jointEffect A B hSC hB₁ ξ) η)
    generateFrom_jointRectangles isSetSemiring_jointRectangles.isPiSystem ?_ ?_ ?_ ?_ B₂ hB₂
  · intro ξ η
    rw [Set.inter_empty]; simp [crossMeasureForm]
  · rintro _ ⟨S₂, T₂, hS₂, hT₂, rfl⟩ ξ η
    rw [crossMeasureForm_inter_rect A B hSC hS₂ hT₂ hB₁ ξ η,
      ← jointEffect_inner A B hSC hB₁ ξ (jointEffect A B hSC (hS₂.prod hT₂) η),
      ← jointEffect_inner A B hSC (hS₂.prod hT₂) (jointEffect A B hSC hB₁ ξ) η,
      jointEffect_swap A B hSC hB₁ ξ (jointEffect A B hSC (hS₂.prod hT₂) η)]
  · intro t htm ih ξ η
    have hd : Disjoint (B₁ ∩ t) (B₁ ∩ tᶜ) := by
      rw [Set.disjoint_left]; rintro x ⟨_, hxt⟩ ⟨_, hxtc⟩; exact hxtc hxt
    have hunion : (B₁ ∩ t) ∪ (B₁ ∩ tᶜ) = B₁ := by
      rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
    have hkey : crossMeasureForm A B hSC B₁ ξ η
        = crossMeasureForm A B hSC (B₁ ∩ t) ξ η + crossMeasureForm A B hSC (B₁ ∩ tᶜ) ξ η := by
      conv_lhs => rw [← hunion]
      exact crossMeasureForm_union2 A B hSC (hB₁.inter htm) (hB₁.inter htm.compl) hd ξ η
    rw [crossMeasureForm_compl A B hSC htm, ← ih ξ η,
      jointEffect_swap A B hSC hB₁ ξ η, jointEffect_inner A B hSC hB₁ ξ η, hkey]
    ring
  · intro g hgd hgm ih ξ η
    rw [Set.inter_iUnion,
      crossMeasureForm_iUnion A B hSC
        (fun i j hij => (hgd hij).mono Set.inter_subset_right Set.inter_subset_right)
        (fun i => hB₁.inter (hgm i)),
      crossMeasureForm_iUnion A B hSC hgd hgm]
    exact tsum_congr fun i => ih i ξ η

/-- **Operator multiplicativity of the joint effects** (`IsProjective` on the nose).
`jointEffect (B₁ ∩ B₂) = jointEffect B₁ · jointEffect B₂`.  From the form identity
`crossMeasureForm_inter` by full sesquilinear extensionality (`ext_inner_left`) + the swap. -/
theorem jointEffect_inter (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B)
    {B₁ B₂ : Set (ℝ × ℝ)} (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    jointEffect A B hSC (h₁.inter h₂) = jointEffect A B hSC h₁ * jointEffect A B hSC h₂ := by
  refine ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => ?_
  rw [jointEffect_inner, crossMeasureForm_inter A B hSC h₁ h₂ ξ η,
    ← jointEffect_inner A B hSC h₂ (jointEffect A B hSC h₁ ξ) η,
    jointEffect_swap A B hSC h₁ ξ (jointEffect A B hSC h₂ η), ContinuousLinearMap.mul_apply]

/-- **G2.4 — the joint POVM is projective.**  Immediate from `jointEffect_inter`. -/
theorem jointPOVM_isProjective (A B : Observable.UnboundedObservable H) (hSC : StronglyCommute A B) :
    (jointPOVM A B hSC).IsProjective :=
  fun _ _ h₁ h₂ => (jointEffect_inter A B hSC h₁ h₂).symm

/-- `[needs spectralPVM + 2D Bochner]` **Commutativity ⟺ a joint spectral measure.**

* **Forward** (`StronglyCommute ⟹ joint PVM`): the multivariate spectral theorem — the commuting
  PVMs generate a joint PVM on `ℝ²` with the right cylinder marginals.  This is the genuine new
  construction (still a `sorry`); it is the two-dimensional analogue of the in-house Herglotz/Stone
  build (or the product of the two commuting `spectralPVM`s).
* **Backward** (`joint PVM ⟹ StronglyCommute`): **proved**, `stronglyCommute_of_jointPVM`.

This replaces the naive `commute_iff_joint_law`: the witness is an operator-valued PVM (`IsJointOf`),
not a per-state coupling, which is why the equivalence has content. -/
theorem stronglyCommute_iff_jointPVM (A B : UnboundedObservable H) :
    StronglyCommute A B ↔ ∃ M : POVM H (ℝ × ℝ), M.IsProjective ∧ M.IsJointOf A B :=
  ⟨fun hSC => ⟨jointPOVM A B hSC, jointPOVM_isProjective A B hSC, jointPOVM_isJointOf A B hSC⟩,
    fun ⟨_M, hproj, hjoint⟩ => stronglyCommute_of_jointPVM hproj hjoint⟩

/-! ### G3 — Step B: the coordinate second moments and integrability of `xy`

The marginals of `μ_ξ = jointScalarMeasure A B hSC ξ` are `A`'s and `B`'s Born measures
(`jointBornMeasure_fst/_snd` via `jointPOVM_isJointOf`), so the coordinate second moments are the
1-D second moments `‖Aξ‖²`, `‖Bξ‖²` (`spectralPVM_integral_sq`).  Cauchy–Schwarz (`MemLp.integrable_mul`,
`2·2 → 1`) then gives `xy ∈ L¹(μ_ξ)`. -/

/-- **A-coordinate second moment.**  `∫ p.1² dμ_ξ = ‖Aξ‖²` (needs `ξ ∈ D(A)`): push the integral to the
first marginal `μ_ξ.fst = A.spectralPVM.diag ξ` (`jointBornMeasure_fst`, `integral_map`) and apply the
1-D second moment `spectralPVM_integral_sq`. -/
theorem jointScalarMeasure_integral_fst_sq (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {ξ : H} (hξA : ξ ∈ A.domain) :
    ∫ p : ℝ × ℝ, p.1 ^ 2 ∂(jointScalarMeasure A B hSC ξ) = ‖A.toLinearPMap ⟨ξ, hξA⟩‖ ^ 2 := by
  have hfst : (jointScalarMeasure A B hSC ξ).fst = A.spectralPVM.diag ξ :=
    jointBornMeasure_fst (jointPOVM_isJointOf A B hSC) ξ
  calc ∫ p : ℝ × ℝ, p.1 ^ 2 ∂(jointScalarMeasure A B hSC ξ)
      = ∫ s : ℝ, s ^ 2 ∂((jointScalarMeasure A B hSC ξ).fst) :=
        (integral_map measurable_fst.aemeasurable (continuous_pow 2).aestronglyMeasurable).symm
    _ = ∫ s : ℝ, s ^ 2 ∂(A.spectralPVM.diag ξ) := by rw [hfst]
    _ = ‖A.toLinearPMap ⟨ξ, hξA⟩‖ ^ 2 := SpectralTheory.spectralPVM_integral_sq A.selfAdjoint ξ hξA

/-- **B-coordinate second moment.**  `∫ p.2² dμ_ξ = ‖Bξ‖²` (needs `ξ ∈ D(B)`). -/
theorem jointScalarMeasure_integral_snd_sq (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {ξ : H} (hξB : ξ ∈ B.domain) :
    ∫ p : ℝ × ℝ, p.2 ^ 2 ∂(jointScalarMeasure A B hSC ξ) = ‖B.toLinearPMap ⟨ξ, hξB⟩‖ ^ 2 := by
  have hsnd : (jointScalarMeasure A B hSC ξ).snd = B.spectralPVM.diag ξ :=
    jointBornMeasure_snd (jointPOVM_isJointOf A B hSC) ξ
  calc ∫ p : ℝ × ℝ, p.2 ^ 2 ∂(jointScalarMeasure A B hSC ξ)
      = ∫ t : ℝ, t ^ 2 ∂((jointScalarMeasure A B hSC ξ).snd) :=
        (integral_map measurable_snd.aemeasurable (continuous_pow 2).aestronglyMeasurable).symm
    _ = ∫ t : ℝ, t ^ 2 ∂(B.spectralPVM.diag ξ) := by rw [hsnd]
    _ = ‖B.toLinearPMap ⟨ξ, hξB⟩‖ ^ 2 := SpectralTheory.spectralPVM_integral_sq B.selfAdjoint ξ hξB

/-- **`p.1²` is integrable** for `ξ ∈ D(A)` (the first marginal is `A`'s Born measure, whose second
moment `‖Aξ‖²` is finite, `spectralPVM_integrable_sq`). -/
theorem jointScalarMeasure_integrable_fst_sq (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {ξ : H} (hξA : ξ ∈ A.domain) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (jointScalarMeasure A B hSC ξ) := by
  have hfst : (jointScalarMeasure A B hSC ξ).fst = A.spectralPVM.diag ξ :=
    jointBornMeasure_fst (jointPOVM_isJointOf A B hSC) ξ
  have h2 : Integrable (fun s : ℝ => s ^ 2) ((jointScalarMeasure A B hSC ξ).fst) := by
    rw [hfst]; exact SpectralTheory.spectralPVM_integrable_sq A.selfAdjoint ξ hξA
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    measurable_fst.aemeasurable).mp h2

/-- **`p.2²` is integrable** for `ξ ∈ D(B)`. -/
theorem jointScalarMeasure_integrable_snd_sq (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {ξ : H} (hξB : ξ ∈ B.domain) :
    Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (jointScalarMeasure A B hSC ξ) := by
  have hsnd : (jointScalarMeasure A B hSC ξ).snd = B.spectralPVM.diag ξ :=
    jointBornMeasure_snd (jointPOVM_isJointOf A B hSC) ξ
  have h2 : Integrable (fun t : ℝ => t ^ 2) ((jointScalarMeasure A B hSC ξ).snd) := by
    rw [hsnd]; exact SpectralTheory.spectralPVM_integrable_sq B.selfAdjoint ξ hξB
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    measurable_snd.aemeasurable).mp h2

/-- **The symbol `xy` is integrable** for `ξ ∈ D(A) ∩ D(B)`: both coordinates are in `L²(μ_ξ)`
(`memLp_two_iff_integrable_sq` + the second moments), so their product is in `L¹` (`MemLp.integrable_mul`,
Hölder `2·2 → 1`).  The L¹ membership that makes `∫ xy dμ_ξ` an honest absolutely-convergent integral. -/
theorem jointScalarMeasure_integrable_mul (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {ξ : H} (hξA : ξ ∈ A.domain) (hξB : ξ ∈ B.domain) :
    Integrable (fun p : ℝ × ℝ => p.1 * p.2) (jointScalarMeasure A B hSC ξ) := by
  have hf : MemLp (fun p : ℝ × ℝ => p.1) 2 (jointScalarMeasure A B hSC ξ) :=
    (memLp_two_iff_integrable_sq continuous_fst.aestronglyMeasurable).mpr
      (jointScalarMeasure_integrable_fst_sq A B hSC hξA)
  have hg : MemLp (fun p : ℝ × ℝ => p.2) 2 (jointScalarMeasure A B hSC ξ) :=
    (memLp_two_iff_integrable_sq continuous_snd.aestronglyMeasurable).mpr
      (jointScalarMeasure_integrable_snd_sq A B hSC hξB)
  simpa [Pi.mul_def] using hf.integrable_mul hg

/-! ### G3 — Step A/C infrastructure: the joint functional calculus engine

The correlation proof is the two-dimensional analogue of `weak_first_moment`: truncate the symbol
`xy` to the box `[-N,N]²`, identify the truncated integral with the operator product
`Φ_A(x·1_N)·Φ_B(y·1_N)` (the bounded functional calculi of the two commuting generators), and pass
to the limit `N → ∞`.  The novelty over the 1-D case is the operator product, which replaces the
unavailable Fubini (`μ_ξ` is **not** a product measure).  Its limit `Φ_A(f_N)Φ_B(g_N)ξ → A(Bξ)`
needs `E_B(T)` (a `B`-projection) to preserve `D(A)` and commute with `A` — the *external*
commutation supplied by `StronglyCommute` through the cross-group engines of `Joint.lean §0`. -/

section G3Correlation

open Spectra.QuantumMechanics.SpectralTheory Spectra.YosidaHille
  Spectra.OneParameterUnitaryGroup Spectra.Borel

/-- **Generic difference-quotient intertwining.**  A bounded operator `C` commuting with the group
`U` intertwines the generator's difference quotient: `genDiffQuot (C x) = C ∘ genDiffQuot x`. -/
private lemma genDiffQuot_commute {U_grp : OneParameterUnitaryGroup (H := H)} (C : H →L[ℂ] H)
    (hC : ∀ t, U_grp.U t * C = C * U_grp.U t) (x : H) :
    genDiffQuot U_grp (C x) = fun t => C (genDiffQuot U_grp x t) := by
  funext t
  have hcomm : C (U_grp.U t x) = U_grp.U t (C x) := by
    have h := DFunLike.congr_fun (hC t) x
    simpa only [ContinuousLinearMap.mul_apply] using h.symm
  simp only [genDiffQuot_apply, map_smul, map_sub, hcomm]

/-- **A bounded operator commuting with the group preserves the generator's domain.**  The generic
form of `spectralCalculus_mem_generatorDomain_of_mem`: the only property of `Φ(g)` it uses is
commutation with `U(t)`.  Applied with `C = E_B(T)` (and the external commutation from
`StronglyCommute`) it gives `E_B(T) D(A) ⊆ D(A)`. -/
private lemma mem_generatorDomain_of_commute {U_grp : OneParameterUnitaryGroup (H := H)}
    (C : H →L[ℂ] H) (hC : ∀ t, U_grp.U t * C = C * U_grp.U t) (x : (generator U_grp).domain) :
    (C (x : H)) ∈ (generator U_grp).domain :=
  mem_generatorDomain.mpr ⟨C (generator U_grp x), by
    rw [genDiffQuot_commute C hC]
    exact (C.continuous.tendsto _).comp (generator_tendsto U_grp x)⟩

/-- **A bounded operator commuting with the group commutes with the generator on its domain**:
`A (C x) = C (A x)`. -/
private lemma generator_commute {U_grp : OneParameterUnitaryGroup (H := H)} (C : H →L[ℂ] H)
    (hC : ∀ t, U_grp.U t * C = C * U_grp.U t) (x : (generator U_grp).domain) :
    generator U_grp ⟨C (x : H), mem_generatorDomain_of_commute C hC x⟩ = C (generator U_grp x) :=
  tendsto_nhds_unique
    (generator_tendsto U_grp ⟨_, mem_generatorDomain_of_commute C hC x⟩)
    (by rw [genDiffQuot_commute C hC]
        exact (C.continuous.tendsto _).comp (generator_tendsto U_grp x))

/-- **Cross-group commutation**: the unitary group of `A` commutes with the spectral projections of
`B`, for strongly-commuting `A, B`.  One application of the projection→calculus engine
`commute_spectralCalculus_of_commute_proj` (lifting the `A`-indicators to a character), then
`spectralCalculus_char`.  This is the hypothesis the domain-commutation engine above consumes. -/
private lemma commute_groupA_projB (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) (t : ℝ) {T : Set ℝ} (hT : MeasurableSet T) :
    (genToGroup A.selfAdjoint).U t * B.spectralPVM.proj T hT
      = B.spectralPVM.proj T hT * (genToGroup A.selfAdjoint).U t := by
  have h := commute_spectralCalculus_of_commute_proj (genToGroup A.selfAdjoint)
    (B.spectralPVM.proj T hT) (fun S hS => hSC S T hS hT) (char_measurable t) (char_bdd t)
  rw [spectralCalculus_char] at h
  exact h.eq

/-- **The `B`-section identity (Step A base case).**  Integrating a bounded `x`-symbol `f` against
the `y`-cylinder `T` recovers the operator pairing: `∫ f(x)·1_T(y) dμ_ξ = ⟪ξ, Φ_A(f) E_B(T) ξ⟫`.
Route: the `y`-cylinder section of `μ_ξ` pushed to the `x`-axis is `μ^A_{E_B(T)ξ}`
(`jointScalarMeasure_prod`), so the integral is `∫ f dμ^A_{E_B(T)ξ} = ⟪E_B(T)ξ, Φ_A(f) E_B(T)ξ⟫`
(`spectralForm_self`, `inner_spectralCalculus`), and the left `E_B(T)` drops by self-adjointness +
idempotence + the calculus/projection commutation. -/
private lemma joint_section_inner (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {f : ℝ → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ ω, ‖f ω‖ ≤ C)
    (ξ : H) {T : Set ℝ} (hT : MeasurableSet T) :
    ∫ p, f p.1 * Set.indicator T (fun _ => (1 : ℂ)) p.2 ∂(jointScalarMeasure A B hSC ξ)
      = ⟪ξ, spectralCalculus (genToGroup A.selfAdjoint) f hfm hfb
          (B.spectralPVM.proj T hT ξ)⟫_ℂ := by
  set UA := genToGroup A.selfAdjoint with hUA
  set EB := B.spectralPVM.proj T hT with hEB
  set Φf := spectralCalculus UA f hfm hfb with hΦf
  -- rewrite the integrand as the indicator of the cylinder `univ ×ˢ T`
  have hpt : ∀ p : ℝ × ℝ, f p.1 * Set.indicator T (fun _ => (1 : ℂ)) p.2
      = Set.indicator (Set.univ ×ˢ T) (fun p => f p.1) p := by
    intro p
    by_cases h : p.2 ∈ T
    · rw [Set.indicator_of_mem h, mul_one, Set.indicator_of_mem (by simp [h])]
    · rw [Set.indicator_of_notMem h, mul_zero, Set.indicator_of_notMem (by simp [h])]
  -- the cylinder section pushed to the `x`-axis is `μ^A_{E_B(T)ξ}`
  have hmap : (jointScalarMeasure A B hSC ξ |>.restrict (Set.univ ×ˢ T)).map Prod.fst
      = A.spectralPVM.diag (EB ξ) := by
    ext S hS
    rw [Measure.map_apply measurable_fst hS, Measure.restrict_apply (measurable_fst hS)]
    have hset : Prod.fst ⁻¹' S ∩ (Set.univ ×ˢ T) = S ×ˢ T := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    rw [hset, jointScalarMeasure_prod A B hSC ξ hS hT]
  -- the calculus commutes with `E_B(T)` (external projection commutation from `StronglyCommute`)
  have hcomm : Commute Φf EB :=
    commute_spectralCalculus_of_commute_proj UA EB (fun S hS => hSC S T hS hT) hfm hfb
  have hidem : EB * EB = EB := B.spectralPVM.proj_idem T hT
  have hadj : ContinuousLinearMap.adjoint EB = EB := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact B.spectralPVM.isSelfAdjoint_proj T hT
  have hdrop : EB (Φf (EB ξ)) = Φf (EB ξ) := by
    have hop : EB * Φf * EB = Φf * EB := by rw [← hcomm.eq, mul_assoc, hidem]
    have := congrArg (fun M : H →L[ℂ] H => M ξ) hop
    simpa only [ContinuousLinearMap.mul_apply] using this
  calc ∫ p, f p.1 * Set.indicator T (fun _ => (1 : ℂ)) p.2 ∂(jointScalarMeasure A B hSC ξ)
      = ∫ p, Set.indicator (Set.univ ×ˢ T) (fun p => f p.1) p ∂(jointScalarMeasure A B hSC ξ) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ p in Set.univ ×ˢ T, f p.1 ∂(jointScalarMeasure A B hSC ξ) :=
        integral_indicator (MeasurableSet.univ.prod hT)
    _ = ∫ x, f x ∂(A.spectralPVM.diag (EB ξ)) := by
        rw [← hmap, integral_map measurable_fst.aemeasurable hfm.aestronglyMeasurable]
    _ = ∫ l, f l ∂(borelMeasure UA (EB ξ)) := rfl
    _ = spectralForm UA (EB ξ) (EB ξ) f := (spectralForm_self UA (EB ξ) hfm hfb).symm
    _ = ⟪EB ξ, Φf (EB ξ)⟫_ℂ := (inner_spectralCalculus UA f hfm hfb (EB ξ) (EB ξ)).symm
    _ = ⟪ξ, EB (Φf (EB ξ))⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_left EB (Φf (EB ξ)) ξ, hadj]
    _ = ⟪ξ, Φf (EB ξ)⟫_ℂ := by rw [hdrop]

/-- A simple function `ℝ → ℂ` is bounded (finite range). -/
private lemma simpleFunc_bdd (s : MeasureTheory.SimpleFunc ℝ ℂ) :
    ∃ C, ∀ ω, ‖(s : ℝ → ℂ) ω‖ ≤ C := by
  have hbdd : BddAbove (Set.range (fun ω => ‖(s : ℝ → ℂ) ω‖)) := by
    have hr : Set.range (fun ω => ‖(s : ℝ → ℂ) ω‖)
        = (fun z : ℂ => ‖z‖) '' Set.range (s : ℝ → ℂ) := Set.range_comp _ _
    rw [hr]; exact (s.finite_range.image _).bddAbove
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨C, fun ω => hC ⟨ω, rfl⟩⟩

/-- **Step A on simple `y`-symbols.**  For a simple function `s`, the product moment
`∫ f(x)·s(y) dμ_ξ` equals the `B`-spectral form `spectralForm_B (Φ_A(f)† ξ) ξ s`.  By
`SimpleFunc.induction`: the indicator base case is `joint_section_inner` (scaled), and additivity is
the bilinearity of both the integral and `spectralForm` (`spectralForm_add_fun`). -/
private lemma joint_product_form_simple (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {f : ℝ → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ ω, ‖f ω‖ ≤ C)
    (ξ : H) (s : MeasureTheory.SimpleFunc ℝ ℂ) :
    ∫ p, f p.1 * (s : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ)
      = spectralForm (genToGroup B.selfAdjoint)
          (ContinuousLinearMap.adjoint (spectralCalculus (genToGroup A.selfAdjoint) f hfm hfb) ξ)
          ξ (s : ℝ → ℂ) := by
  set UA := genToGroup A.selfAdjoint with hUA
  set UB := genToGroup B.selfAdjoint with hUB
  set Φf := spectralCalculus UA f hfm hfb with hΦf
  set η := ContinuousLinearMap.adjoint Φf ξ with hη
  -- finite measure ⟹ `f(x)·h(y)` is integrable for any bounded measurable `h`
  have hintegrable : ∀ {h : ℝ → ℂ}, Measurable h → (∃ C, ∀ ω, ‖h ω‖ ≤ C) →
      Integrable (fun p : ℝ × ℝ => f p.1 * h p.2) (jointScalarMeasure A B hSC ξ) := by
    intro h hhm hhb
    obtain ⟨Cf, hCf⟩ := hfb
    obtain ⟨Ch, hCh⟩ := hhb
    refine Integrable.mono' (integrable_const (max Cf 0 * max Ch 0))
      ((hfm.comp measurable_fst).mul (hhm.comp measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul]
    exact mul_le_mul ((hCf _).trans (le_max_left _ _)) ((hCh _).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  -- the indicator base identity (Step A on a single cylinder)
  have hbase : ∀ {S : Set ℝ} (hS : MeasurableSet S),
      spectralForm UB η ξ (Set.indicator S (fun _ => (1 : ℂ)))
        = ⟪ξ, Φf (B.spectralPVM.proj S hS ξ)⟫_ℂ := by
    intro S hS
    have h1 : spectralCalculus UB (Set.indicator S (fun _ => (1 : ℂ)))
        (measurable_const.indicator hS) (indicator_one_bdd S) = B.spectralPVM.proj S hS := rfl
    rw [← inner_spectralCalculus UB (Set.indicator S (fun _ => (1 : ℂ)))
      (measurable_const.indicator hS) (indicator_one_bdd S) η ξ, h1, hη,
      ContinuousLinearMap.adjoint_inner_left]
  -- the induction
  induction s using MeasureTheory.SimpleFunc.induction with
  | @const c S hS =>
    -- base: `s = c · 1_S`
    have hcoe : ((MeasureTheory.SimpleFunc.piecewise S hS (MeasureTheory.SimpleFunc.const ℝ c)
        (MeasureTheory.SimpleFunc.const ℝ 0)) : ℝ → ℂ) = Set.indicator S (fun _ => c) := by
      ext y; by_cases h : y ∈ S <;>
        simp [MeasureTheory.SimpleFunc.piecewise_apply, h, Set.indicator_of_mem,
          Set.indicator_of_notMem]
    rw [hcoe]
    have hci : ∀ y : ℝ, Set.indicator S (fun _ => c) y
        = c * Set.indicator S (fun _ => (1 : ℂ)) y := by
      intro y; by_cases h : y ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    calc ∫ p, f p.1 * Set.indicator S (fun _ => c) p.2 ∂(jointScalarMeasure A B hSC ξ)
        = ∫ p, c * (f p.1 * Set.indicator S (fun _ => (1 : ℂ)) p.2)
            ∂(jointScalarMeasure A B hSC ξ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          by_cases h : p.2 ∈ S
          · simp only [Set.indicator_of_mem h]; ring
          · simp only [Set.indicator_of_notMem h]; ring
      _ = c * ∫ p, f p.1 * Set.indicator S (fun _ => (1 : ℂ)) p.2
            ∂(jointScalarMeasure A B hSC ξ) := integral_const_mul _ _
      _ = c * ⟪ξ, Φf (B.spectralPVM.proj S hS ξ)⟫_ℂ := by
          rw [joint_section_inner A B hSC hfm hfb ξ hS]
      _ = c * spectralForm UB η ξ (Set.indicator S (fun _ => (1 : ℂ))) := by rw [hbase hS]
      _ = spectralForm UB η ξ (Set.indicator S (fun _ => c)) := by
          rw [← spectralForm_smul_fun UB η ξ c (Set.indicator S (fun _ => (1 : ℂ)))]
          congr 1; ext y; rw [hci y]
  | @add s₁ s₂ hdisj h₁ h₂ =>
    -- additive step
    obtain ⟨C₁, hC₁⟩ := simpleFunc_bdd s₁
    obtain ⟨C₂, hC₂⟩ := simpleFunc_bdd s₂
    have hcoe : ((s₁ + s₂ : MeasureTheory.SimpleFunc ℝ ℂ) : ℝ → ℂ)
        = fun y => (s₁ : ℝ → ℂ) y + (s₂ : ℝ → ℂ) y := by
      ext y; simp [MeasureTheory.SimpleFunc.coe_add]
    rw [hcoe]
    calc ∫ p, f p.1 * ((s₁ : ℝ → ℂ) p.2 + (s₂ : ℝ → ℂ) p.2) ∂(jointScalarMeasure A B hSC ξ)
        = ∫ p, (f p.1 * (s₁ : ℝ → ℂ) p.2 + f p.1 * (s₂ : ℝ → ℂ) p.2)
            ∂(jointScalarMeasure A B hSC ξ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_); ring
      _ = (∫ p, f p.1 * (s₁ : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ))
            + ∫ p, f p.1 * (s₂ : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ) :=
          integral_add (hintegrable s₁.measurable ⟨C₁, hC₁⟩) (hintegrable s₂.measurable ⟨C₂, hC₂⟩)
      _ = spectralForm UB η ξ (s₁ : ℝ → ℂ) + spectralForm UB η ξ (s₂ : ℝ → ℂ) := by rw [h₁, h₂]
      _ = spectralForm UB η ξ (fun y => (s₁ : ℝ → ℂ) y + (s₂ : ℝ → ℂ) y) :=
          (spectralForm_add_fun UB η ξ s₁.measurable ⟨C₁, hC₁⟩ s₂.measurable ⟨C₂, hC₂⟩).symm

/-- **Step A — the bounded product-moment identity.**  For bounded measurable `f, g`, the joint
integral of the product symbol equals the operator-product matrix element:
`∫ f(x)·g(y) dμ_ξ = ⟪ξ, Φ_A(f) Φ_B(g) ξ⟫`.  Extends `joint_product_form_simple` from simple to
bounded `g` by approximating with `SimpleFunc.approxOn` and dominated convergence on both sides (the
left integral over the finite `μ_ξ`; the right `spectralForm`, a fixed combination of integrals over
the finite measures `μ^B_w`).  The operator product `Φ_A(f)Φ_B(g)` is what replaces the unavailable
Fubini. -/
private lemma joint_product_form (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {f g : ℝ → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ ω, ‖f ω‖ ≤ C)
    (hgm : Measurable g) (hgb : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (ξ : H) :
    ∫ p, f p.1 * g p.2 ∂(jointScalarMeasure A B hSC ξ)
      = ⟪ξ, spectralCalculus (genToGroup A.selfAdjoint) f hfm hfb
          (spectralCalculus (genToGroup B.selfAdjoint) g hgm hgb ξ)⟫_ℂ := by
  set UA := genToGroup A.selfAdjoint with hUA
  set UB := genToGroup B.selfAdjoint with hUB
  set Φf := spectralCalculus UA f hfm hfb with hΦf
  set η := ContinuousLinearMap.adjoint Φf ξ with hη
  -- it suffices to prove the `spectralForm` version, then convert through the adjoint
  suffices hform : ∫ p, f p.1 * g p.2 ∂(jointScalarMeasure A B hSC ξ) = spectralForm UB η ξ g by
    rw [hform, ← inner_spectralCalculus UB g hgm hgb η ξ]
    exact ContinuousLinearMap.adjoint_inner_left Φf (spectralCalculus UB g hgm hgb ξ) ξ
  obtain ⟨Cg, hCg⟩ := hgb
  -- the approximating simple functions
  set gN : ℕ → MeasureTheory.SimpleFunc ℝ ℂ :=
    fun n => MeasureTheory.SimpleFunc.approxOn g hgm Set.univ 0 (Set.mem_univ 0) n with hgN
  have hgN_tendsto : ∀ y, Filter.Tendsto (fun n => (gN n : ℝ → ℂ) y) atTop (𝓝 (g y)) := fun y =>
    MeasureTheory.SimpleFunc.tendsto_approxOn hgm (Set.mem_univ 0) (by simp)
  have hgN_bound : ∀ n y, ‖(gN n : ℝ → ℂ) y‖ ≤ 2 * Cg := by
    intro n y
    have h := MeasureTheory.SimpleFunc.norm_approxOn_y₀_le hgm (Set.mem_univ (0 : ℂ)) y n
    simp only [sub_zero] at h
    calc ‖(gN n : ℝ → ℂ) y‖ ≤ ‖g y‖ + ‖g y‖ := h
      _ ≤ Cg + Cg := add_le_add (hCg y) (hCg y)
      _ = 2 * Cg := by ring
  -- LHS: dominated convergence over the finite measure `μ_ξ`
  have hLHS : Filter.Tendsto
      (fun n => ∫ p, f p.1 * (gN n : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ)) atTop
      (𝓝 (∫ p, f p.1 * g p.2 ∂(jointScalarMeasure A B hSC ξ))) := by
    obtain ⟨Cf, hCf⟩ := hfb
    refine tendsto_integral_of_dominated_convergence (fun _ => max Cf 0 * (2 * Cg))
      (fun n => ((hfm.comp measurable_fst).mul
        ((gN n).measurable.comp measurable_snd)).aestronglyMeasurable)
      (integrable_const _) (fun n => Filter.Eventually.of_forall fun p => ?_)
      (Filter.Eventually.of_forall fun p => ?_)
    · rw [norm_mul]
      exact mul_le_mul ((hCf _).trans (le_max_left _ _)) (hgN_bound n p.2)
        (norm_nonneg _) (le_max_right _ _)
    · exact tendsto_const_nhds.mul (hgN_tendsto p.2)
  -- RHS: each of the four `spectralForm` integrals converges by dominated convergence
  have hconv : ∀ w : H, Filter.Tendsto (fun n => ∫ l, (gN n : ℝ → ℂ) l ∂(borelMeasure UB w)) atTop
      (𝓝 (∫ l, g l ∂(borelMeasure UB w))) := by
    intro w
    haveI : MeasureTheory.IsFiniteMeasure (borelMeasure UB w) := borelMeasure_isFiniteMeasure UB w
    exact tendsto_integral_of_dominated_convergence (fun _ => 2 * Cg)
      (fun n => (gN n).measurable.aestronglyMeasurable) (integrable_const _)
      (fun n => Filter.Eventually.of_forall fun l => hgN_bound n l)
      (Filter.Eventually.of_forall hgN_tendsto)
  have hRHS : Filter.Tendsto (fun n => spectralForm UB η ξ (gN n : ℝ → ℂ)) atTop
      (𝓝 (spectralForm UB η ξ g)) := by
    simp only [spectralForm]
    exact (((hconv (η + ξ)).sub (hconv (η - ξ))).add
      (((hconv (η - I • ξ)).sub (hconv (η + I • ξ))).mul_const I)).div_const 4
  -- the per-`n` simple-function identity, then identify the limits
  have heq : Filter.Tendsto
      (fun n => ∫ p, f p.1 * (gN n : ℝ → ℂ) p.2 ∂(jointScalarMeasure A B hSC ξ)) atTop
      (𝓝 (spectralForm UB η ξ g)) := by
    refine hRHS.congr fun n => ?_
    exact (joint_product_form_simple A B hSC hfm hfb ξ (gN n)).symm
  exact tendsto_nhds_unique hLHS heq

/-- **Step C — the truncated vector identity.**  The operator product applied to `ξ` collapses to
nested truncated projections of `A(Bξ)`:
`Φ_A(x·1_N) Φ_B(y·1_N) ξ = E_A([-N,N]) E_B([-N,N]) (A(Bξ))`.  Inside out: `Φ_B(y·1_N)ξ = E_B([-N,N])(Bξ)`
(`generator_spectralProjection`), then `E_B([-N,N])` preserves `D(A)` and commutes with `A`
(`generator_commute` + `commute_groupA_projB`), so `Φ_A(x·1_N)` acting on it is `E_A([-N,N])` applied
to `E_B([-N,N])(A(Bξ))`. -/
private lemma joint_truncated_vector (A B : Observable.UnboundedObservable H)
    (hSC : StronglyCommute A B) {ξ : H} (hξ : ξ ∈ B.domain)
    (hξ' : B.toLinearPMap ⟨ξ, hξ⟩ ∈ A.domain) (N : ℕ) :
    spectralCalculus (genToGroup A.selfAdjoint)
        (fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
        (id_indicator_measurable measurableSet_Icc)
        (id_indicator_bdd (fun _x hx => abs_le_max_of_mem_Icc hx))
        (spectralCalculus (genToGroup B.selfAdjoint)
          (fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable measurableSet_Icc)
          (id_indicator_bdd (fun _x hx => abs_le_max_of_mem_Icc hx)) ξ)
      = A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
            (A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩)) := by
  set UA := genToGroup A.selfAdjoint with hUA
  set UB := genToGroup B.selfAdjoint with hUB
  set IccN := Set.Icc (-(N : ℝ)) (N : ℝ) with hIccN
  have habs : ∀ x ∈ IccN, |x| ≤ max |(-(N : ℝ))| |(N : ℝ)| := fun x hx => abs_le_max_of_mem_Icc hx
  set ψ := B.toLinearPMap ⟨ξ, hξ⟩ with hψ
  set EB := B.spectralPVM.proj IccN measurableSet_Icc with hEB
  -- inner truncation: `Φ_B(y·1_N) ξ = E_B(N) (Bξ)`
  have hξB' : ξ ∈ (generator UB).domain := by rw [generator_genToGroup]; exact hξ
  have hBval : generator UB ⟨ξ, hξB'⟩ = ψ := (le_of_eq (generator_genToGroup B.selfAdjoint)).2 rfl
  have h1 : spectralCalculus UB
        (fun l => (l : ℂ) * Set.indicator IccN (fun _ => (1 : ℂ)) l)
        (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs) ξ = EB ψ := by
    have h := generator_spectralProjection_comm (B := IccN) UB measurableSet_Icc ⟨ξ, hξB'⟩
    rw [hBval] at h
    rw [← generator_spectralProjection UB measurableSet_Icc habs ξ]
    exact h
  -- `E_B(N)` preserves `D(A)` and commutes with `A`
  have hψA : ψ ∈ (generator UA).domain := by rw [generator_genToGroup]; exact hξ'
  have hAval : generator UA ⟨ψ, hψA⟩ = A.toLinearPMap ⟨ψ, hξ'⟩ :=
    (le_of_eq (generator_genToGroup A.selfAdjoint)).2 rfl
  have hC : ∀ t, UA.U t * EB = EB * UA.U t := fun t => commute_groupA_projB A B hSC t measurableSet_Icc
  have hχA : EB ψ ∈ (generator UA).domain := mem_generatorDomain_of_commute EB hC ⟨ψ, hψA⟩
  have hgenχ : generator UA ⟨EB ψ, hχA⟩ = EB (A.toLinearPMap ⟨ψ, hξ'⟩) := by
    rw [generator_commute EB hC ⟨ψ, hψA⟩, hAval]
  -- outer truncation: `Φ_A(x·1_N) (E_B(N)ψ) = E_A(N) (generator_A (E_B(N)ψ)) = E_A(N) E_B(N) (Aψ)`
  rw [h1]
  have h2 := generator_spectralProjection_comm (B := IccN) UA measurableSet_Icc ⟨EB ψ, hχA⟩
  rw [hgenχ] at h2
  rw [← generator_spectralProjection UA measurableSet_Icc habs (EB ψ)]
  exact h2

/-- **The truncation converges to the identity in two coordinates.**  For any vector `v`,
`E_A([-N,N]) E_B([-N,N]) v → v`: `E_B([-N,N])v → v` and `E_A([-N,N])v → v`
(`tendsto_spectralProjection_Icc_univ`), and `E_A` is a contraction, so the composite differs from
`v` by at most `‖E_B([-N,N])v − v‖ + ‖E_A([-N,N])v − v‖ → 0`. -/
private lemma joint_truncated_tendsto (A B : Observable.UnboundedObservable H) (v : H) :
    Filter.Tendsto (fun N : ℕ =>
        A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc v)) atTop (𝓝 v) := by
  have hA : Filter.Tendsto (fun N : ℕ =>
      A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc v) atTop (𝓝 v) :=
    tendsto_spectralProjection_Icc_univ (genToGroup A.selfAdjoint) v
  have hB : Filter.Tendsto (fun N : ℕ =>
      B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc v) atTop (𝓝 v) :=
    tendsto_spectralProjection_Icc_univ (genToGroup B.selfAdjoint) v
  rw [tendsto_iff_norm_sub_tendsto_zero] at hA hB ⊢
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using hB.add hA)
  set EA := A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc with hEA
  set EB := B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc with hEB
  calc ‖EA (EB v) - v‖ = ‖(EA (EB v) - EA v) + (EA v - v)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖EA (EB v) - EA v‖ + ‖EA v - v‖ := norm_add_le _ _
    _ = ‖EA (EB v - v)‖ + ‖EA v - v‖ := by rw [← map_sub]
    _ ≤ ‖EB v - v‖ + ‖EA v - v‖ := by
        gcongr
        exact A.spectralPVM.norm_proj_apply_le _ measurableSet_Icc _

/-- **The correlation.**  The content a generic coupling lacks: the genuine joint law reproduces
`⟪ξ, AB ξ⟫` (the cross-moment), the bridge to Bell/CHSH.

Stated for the **canonical projective joint PVM** `M = jointPOVM A B hSC` (so
`jointBornMeasure = jointScalarMeasure = μ_ξ`).  This specialization is essential, **not** cosmetic:
for a *generic* `M` with only `M.IsJointOf A B`, the cross-moment `∫ xy dμ_ξ` is **under-determined** —
`IsJointOf` fixes only the cylinder marginals (`jointBornMeasure_fst/_snd`), leaving the rectangle
coupling free (`POVM.ext_of_diag`), so the identity would be false.  Projectivity forces the rectangle
values `μ_ξ(S×T) = ⟪ξ, E_A(S)E_B(T)ξ⟫`, which is what carries the correlation.

The domain hypotheses are `ξ ∈ D(A) ∩ D(B)` and `Bξ ∈ D(A)`: `ξ ∈ D(B)` and `Bξ ∈ D(A)` make the RHS
`⟪ξ, A(Bξ)⟫` meaningful, and `ξ ∈ D(A)` is needed for integrability of the symbol `xy` on the LHS
(`∫ x² dμ_ξ = ‖Aξ‖² < ∞` via the first marginal, then Cauchy–Schwarz with `∫ y² = ‖Bξ‖²`).

Proof (planned): the 2-D analogue of `weak_first_moment` — truncate `xy` to the box `[-N,N]²`, identify
the truncated integral via the commuting bounded calculi `Φ_A(x·1_N)Φ_B(y·1_N)`, then dominated
convergence (left) and the domain-commutation engine `generator_spectralProjection_comm` (right) as
`N → ∞`.  See the Vault plan `Plan - G3 Correlation.md`. -/
theorem jointBornMeasure_correlation {A B : Observable.UnboundedObservable H}
    (hSC : StronglyCommute A B) {ξ : H} (hξA : ξ ∈ A.domain) (hξ : ξ ∈ B.domain)
    (hξ' : (B.toLinearPMap ⟨ξ, hξ⟩) ∈ A.domain) :
    ∫ p, p.1 * p.2 ∂(jointBornMeasure (jointPOVM A B hSC) ξ)
      = (⟪ξ, A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩⟫_ℂ).re := by
  show ∫ p, p.1 * p.2 ∂(jointScalarMeasure A B hSC ξ)
    = (⟪ξ, A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩⟫_ℂ).re
  -- the truncated box integral `∫_{[-N,N]²} xy dμ_ξ` equals the truncated operator matrix element
  have key : ∀ N : ℕ,
      (∫ p, Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ))
          (fun q : ℝ × ℝ => q.1 * q.2) p ∂(jointScalarMeasure A B hSC ξ))
        = (⟪ξ, A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
            (B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
              (A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩))⟫_ℂ).re := by
    intro N
    -- Step A: the box integral (complex symbols) is the operator product;
    -- Step C: the operator product collapses to nested truncations of `A(Bξ)`
    have hjpf := joint_product_form A B hSC
      (f := fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
      (g := fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
      (id_indicator_measurable measurableSet_Icc)
      (id_indicator_bdd (fun x hx => abs_le_max_of_mem_Icc hx))
      (id_indicator_measurable measurableSet_Icc)
      (id_indicator_bdd (fun x hx => abs_le_max_of_mem_Icc hx)) ξ
    rw [joint_truncated_vector A B hSC hξ hξ' N] at hjpf
    -- the complex box integral is the `ofReal` of the real box integral
    have hcoe : (∫ p : ℝ × ℝ, (p.1 : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ))
              (fun _ => (1 : ℂ)) p.1
            * ((p.2 : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ))
              (fun _ => (1 : ℂ)) p.2) ∂(jointScalarMeasure A B hSC ξ))
        = ((∫ p, Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ))
            (fun q : ℝ × ℝ => q.1 * q.2) p ∂(jointScalarMeasure A B hSC ξ) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      by_cases h1 : p.1 ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
      · by_cases h2 : p.2 ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
        · simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
            Set.indicator_of_mem (Set.mem_prod.mpr ⟨h1, h2⟩), mul_one, Complex.ofReal_mul]
        · simp only [Set.indicator_of_notMem h2,
            Set.indicator_of_notMem (show p ∉ Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ)
              from fun hh => h2 hh.2), mul_zero, Complex.ofReal_zero]
      · simp only [Set.indicator_of_notMem h1,
          Set.indicator_of_notMem (show p ∉ Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ)
            from fun hh => h1 hh.1), zero_mul, mul_zero, Complex.ofReal_zero]
    rw [← (hcoe.symm.trans hjpf), Complex.ofReal_re]
  -- LHS: dominated convergence (the box exhausts `ℝ²`; dominant `|xy| ∈ L¹` from Step B)
  have hDCT : Filter.Tendsto (fun N : ℕ => ∫ p, Set.indicator
        (Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ)) (fun q : ℝ × ℝ => q.1 * q.2) p
        ∂(jointScalarMeasure A B hSC ξ)) atTop
      (𝓝 (∫ p, p.1 * p.2 ∂(jointScalarMeasure A B hSC ξ))) := by
    refine tendsto_integral_of_dominated_convergence (fun p => ‖p.1 * p.2‖)
      (fun N => ((measurable_fst.mul measurable_snd).indicator
        (measurableSet_Icc.prod measurableSet_Icc)).aestronglyMeasurable)
      (jointScalarMeasure_integrable_mul A B hSC hξA hξ).norm
      (fun N => Filter.Eventually.of_forall fun p => norm_indicator_le_norm_self _ _)
      (Filter.Eventually.of_forall fun p => ?_)
    apply tendsto_const_nhds.congr'
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max |p.1| |p.2|)
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    have hNN : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hp : p ∈ Set.Icc (-(N : ℝ)) (N : ℝ) ×ˢ Set.Icc (-(N : ℝ)) (N : ℝ) := by
      have hb1 : |p.1| ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) hN₀) hNN
      have hb2 : |p.2| ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) hN₀) hNN
      exact ⟨⟨by have := neg_abs_le p.1; linarith, by have := le_abs_self p.1; linarith⟩,
        ⟨by have := neg_abs_le p.2; linarith, by have := le_abs_self p.2; linarith⟩⟩
    exact (Set.indicator_of_mem hp (fun q : ℝ × ℝ => q.1 * q.2)).symm
  -- RHS: the truncations converge to `A(Bξ)` and the inner product is continuous
  have hlim : Filter.Tendsto (fun N : ℕ => (⟪ξ,
        A.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (B.spectralPVM.proj (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
            (A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩))⟫_ℂ).re) atTop
      (𝓝 ((⟪ξ, A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩⟫_ℂ).re)) := by
    have hcont : Continuous (fun y : H => (⟪ξ, y⟫_ℂ).re) :=
      Complex.continuous_re.comp (continuous_const.inner continuous_id)
    exact (hcont.tendsto _).comp
      (joint_truncated_tendsto A B (A.toLinearPMap ⟨B.toLinearPMap ⟨ξ, hξ⟩, hξ'⟩))
  exact tendsto_nhds_unique hDCT (hlim.congr fun N => (key N).symm)

end G3Correlation

end Spectra.QuantumMechanics.BornRule

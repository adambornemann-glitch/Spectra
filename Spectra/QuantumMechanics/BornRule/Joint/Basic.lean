/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.Joint.Defs
import Spectra.ProjValMeasure.PdInterface
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Algebra.Star.StarProjection
/-!
# Joint spectral measures — reusable infrastructure and the rectangle foundation

This file collects the infrastructure the forward construction (`Joint.Measure`, `Joint.Forward`)
builds on: generic `ProjValMeasure` σ-additivity facts, the axis-grid sign-atom refinement, the
measurable-rectangle semiring of `ℝ × ℝ`, and the rectangle-level foundation (Route B) through
G2.1 — the rectangle effect `E_A(S)·E_B(T)` is an orthogonal projection, with the content bridge
and marginal-defect estimates that drive the tightness argument in `Joint.Measure`.

## Main definitions

* `Spectra.AxisGrid.signAtom` — the Boolean sign-atom of a finite indexed family of measurable
  sets, the refinement primitive for the joint-measure grid additivity.
* `jointRectangles` — the measurable rectangles of `ℝ × ℝ`, the semiring underlying the
  Carathéodory extension in `Joint.Measure`.

## Main statements

* `Spectra.ProjValMeasure.proj_biUnion`, `tendsto_proj_biUnion` — finite/countable additivity of a
  `ProjValMeasure`'s projections, reusable outside this development.
* `Spectra.AxisGrid.proj_eq_sum_signAtom` — the sign-atom refinement, turning a spectral projection
  of `S j` into a finite sum of projections of atoms (hence a product `E_A(S)·E_B(T)` into a double
  sum over a common grid).
* `isSetSemiring_jointRectangles` — the measurable rectangles of `ℝ × ℝ` form a set semiring, the
  base for the Carathéodory extension in `Joint.Measure`.
* `jointRect_isStarProjection`, `jointRect_mul` — G2.1: the rectangle effect is an orthogonal
  projection and composes like the spectral projections.
* `jointRect_orthogonal`, `jointContent_hasSum`, `jointContent_hasSum_diag` — the orthogonality of
  the `T`-slot rectangle vectors and the resulting one-variable σ-additivity of the rectangle
  content, in norm² and bimeasure form.
* `jointRect_diff_defect_le` — the marginal-defect estimate feeding the compact-inner-regularity
  (Alexandrov) discharge of `jointContentRing_tendsto_empty` in `Joint.Measure`.

## Implementation notes

The results before the `Spectra.QuantumMechanics.BornRule` namespace (`Spectra.ProjValMeasure.*`,
`Spectra.AxisGrid.*`, `jointRectangles`) are generic and reusable; only the `jointRect_*` /
`jointContent_*` theorems mention the commuting operator pair.  The forward construction that
consumes them is complete and `sorry`-free: the joint Carathéodory extension lives in
`Joint.Measure` (`jointScalarMeasure`) and the operator-field polarization in `Joint.Forward`
(`jointEffect`, `stronglyCommute_iff_jointPVM`).

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*][reedsimon1980],
  §§VII–VIII (the spectral theorem, its projection-valued measure, and §VIII.5 the joint spectral
  measure of commuting self-adjoint operators).
* [Hall, *Quantum Theory for Mathematicians*][hall2013], Chapters 7, 10 (joint measurability).

## Tags

joint spectral measure, projection-valued measure, strong commutativity, bimeasure, sign atom,
set semiring, rectangle, Carathéodory extension
-/

open MeasureTheory Complex Spectra Filter Topology
open scoped InnerProductSpace
open Spectra.Operator

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

A reusable refinement primitive for the joint-measure grid additivity.  The **sign atom** of a
finite indexed family `S : ι → Set ℝ` for a sign vector `c : ι → Bool` is the cell
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

omit [Fintype ι] [DecidableEq ι] in
lemma signAtom_measurableSet [Finite ι] {S : ι → Set ℝ} (hS : ∀ i, MeasurableSet (S i))
    (c : ι → Bool) :
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
projections of the sign atoms with positive `j`-coordinate (`proj_biUnion` over the disjoint
atoms). -/
lemma proj_eq_sum_signAtom (P : Spectra.ProjValMeasure H) {S : ι → Set ℝ}
    (hS : ∀ i, MeasurableSet (S i)) (j : ι) (hSj : MeasurableSet (S j)) :
    P.proj (S j) hSj = ∑ c ∈ Finset.univ.filter (fun c : ι → Bool => c j = true),
      P.proj (signAtom S c) (signAtom_measurableSet hS c) := by
  classical
  have hU : MeasurableSet
      (⋃ c ∈ Finset.univ.filter (fun c : ι → Bool => c j = true), signAtom S c) :=
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
spectral measure of `A` at the vector `E_B(T) ξ`.  (And symmetrically in `S`.)  These reductions
are `sorry`-free, and so is the rest of the forward construction they feed: the joint Carathéodory
extension is discharged in `Joint.Measure` (`jointScalarMeasure`) and the operator-field
polarization in `Joint.Forward` (`jointEffect`, `stronglyCommute_iff_jointPVM`). -/

/-- **The rectangle value is a 1-D spectral measure (A-slot).**  For strongly-commuting `A, B`,
`⟪ξ, E_A(S)·E_B(T) ξ⟫ = μ^A_{E_B(T)ξ}(S)`, where `μ^A_v = A.spectralPVM.diag v` is the existing
Born/spectral measure.  Hence, for fixed `T`, the bimeasure is countably additive in `S` for free.
Proof: `E_A(S)·E_B(T) = E_B(T)·E_A(S)·E_B(T)` (commute + `E_B(T)` idempotent), then move a
self-adjoint `E_B(T)` across the inner product and read off `inner_proj`. -/
theorem jointRect_inner_eq_diag_left (A B : Spectra.Operator.SelfAdjointOperator H)
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
theorem jointRect_re_nonneg (A B : Spectra.Operator.SelfAdjointOperator H)
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
theorem jointRect_orthogonal (A B : Spectra.Operator.SelfAdjointOperator H)
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
theorem jointContent_hasSum (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B)
    {S : Set ℝ} (hS : MeasurableSet S) {T : ℕ → Set ℝ} (hT : ∀ n, MeasurableSet (T n))
    (hd : Pairwise (fun i j => Disjoint (T i) (T j))) (ξ : H) :
    HasSum (fun n => ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj (T n) (hT n)) ξ‖ ^ 2)
      (‖(A.spectralPVM.proj S hS
          * B.spectralPVM.proj (⋃ n, T n) (MeasurableSet.iUnion hT)) ξ‖ ^ 2) := by
  set EA := A.spectralPVM.proj S hS with _hEA
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

Scope: the σ-additivity delivered here is *one-variable* (the `T`-slot, for a fixed `S`, in
`.toReal` form).  The `ℝ≥0∞` lift and the finite additivity over *arbitrary* disjoint rectangle
partitions (the `AddContent.sUnion'` obligation, via grid/atom refinement) are carried out in
`Joint.Measure`, which assembles these pieces into the finite measure `jointScalarMeasure`. -/

/-- **G2.1 — the rectangle effect is an orthogonal projection.**  For strongly-commuting `A, B`, the
operator `E_A(S)·E_B(T)` is self-adjoint and idempotent (`IsStarProjection`): the product of the two
*commuting* projections is again a projection.  This is the effect the joint PVM assigns to the
rectangle `S × T`. -/
theorem jointRect_isStarProjection (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    IsStarProjection (A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) :=
  IsStarProjection.mul
    ⟨A.spectralPVM.proj_idem S hS, A.spectralPVM.isSelfAdjoint_proj S hS⟩
    ⟨B.spectralPVM.proj_idem T hT, B.spectralPVM.isSelfAdjoint_proj T hT⟩
    (hSC S T hS hT)

/-- **G2.1 — rectangle multiplicativity.**  The rectangle effects compose like the spectral
projections: `(E_A(S₁)E_B(T₁))·(E_A(S₂)E_B(T₂)) = E_A(S₁∩S₂)·E_B(T₁∩T₂)`.  Strong commutativity is
exactly what lets the inner `E_B(T₁)` and `E_A(S₂)` swap; `proj_inter` closes each slot.  This is
the `proj_inter` of the joint PVM on rectangles — the rectangle case of `IsProjective` (G2.4). -/
theorem jointRect_mul (A B : Spectra.Operator.SelfAdjointOperator H) (hSC : StronglyCommute A B)
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
`‖E_A(S)E_B(T)ξ‖² = ⟪ξ, E_A(S)E_B(T)ξ⟫.re = μ^A_{E_B(T)ξ}(S)`.  This reconciles the norm² form of
the σ-additivity crux (`jointContent_hasSum`) with the bimeasure (`jointRect_inner_eq_diag_left`) —
the nonnegative content the `AddContent` extension (G2.2) actually sums. -/
theorem jointRect_norm_sq_eq_diag (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (ξ : H) :
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
theorem jointRect_norm_sq_le_diag_left (A B : Spectra.Operator.SelfAdjointOperator H)
    (hSC : StronglyCommute A B) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (ξ : H) :
    ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2
      ≤ ((A.spectralPVM.diag ξ) S).toReal := by
  have hcomm : A.spectralPVM.proj S hS * B.spectralPVM.proj T hT
      = B.spectralPVM.proj T hT * A.spectralPVM.proj S hS := (hSC S T hS hT).eq
  rw [hcomm, ContinuousLinearMap.mul_apply, ← A.spectralPVM.norm_sq_proj_apply S hS ξ]
  gcongr
  exact B.spectralPVM.norm_proj_apply_le T hT _

/-- **B-marginal domination of the rectangle content.**  `‖E_A(S)E_B(T)ξ‖² ≤ μ^B_ξ(T)`.  `E_A(S)`
is a contraction (`norm_proj_apply_le`) and `‖E_B(T)ξ‖² = μ^B_ξ(T)` (`norm_sq_proj_apply`).  No
commutation needed. -/
theorem jointRect_norm_sq_le_diag_right (A B : Spectra.Operator.SelfAdjointOperator H)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (ξ : H) :
    ‖(A.spectralPVM.proj S hS * B.spectralPVM.proj T hT) ξ‖ ^ 2
      ≤ ((B.spectralPVM.diag ξ) T).toReal := by
  rw [ContinuousLinearMap.mul_apply, ← B.spectralPVM.norm_sq_proj_apply T hT ξ]
  gcongr
  exact A.spectralPVM.norm_proj_apply_le S hS _

/-- **The marginal-defect estimate — the key tightness input.**  The two rectangle pieces of the
semiring difference `(S×T) ∖ (S'×T') = (S∖S')×T ⊔ (S∩S')×(T∖T')` have total content bounded by the
two marginal defects:
`‖E_A(S∖S')E_B(T)ξ‖² + ‖E_A(S∩S')E_B(T∖T')ξ‖² ≤ μ^A_ξ(S∖S') + μ^B_ξ(T∖T')`.
First piece bounded via `jointRect_norm_sq_le_diag_left` (A-marginal), second via
`jointRect_norm_sq_le_diag_right` (B-marginal).  When `S'⊆S, T'⊆T` the LHS is exactly
`mR((S×T) ∖ (S'×T'))` (finite additivity over the two disjoint pieces), so a compact inner
approximation `S'×T' ⊆ S×T` with both marginal defects small makes the joint content defect small —
the regularity that drives the Alexandrov discharge of `jointContentRing_tendsto_empty`. -/
theorem jointRect_diff_defect_le (A B : Spectra.Operator.SelfAdjointOperator H)
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
theorem jointContent_hasSum_diag (A B : Spectra.Operator.SelfAdjointOperator H)
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


end Spectra.QuantumMechanics.BornRule

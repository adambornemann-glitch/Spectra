/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Algebra.Order.Ring.Star

/-!
# Density of rectangle-simple kernels in `L²(μ × ν)`

Finite ℂ-linear combinations of indicators of **finite-measure** measurable rectangles are dense in
`L²(μ × ν)` (σ-finite `μ`, `ν`).  This is the density input for proving that integral operators
with `L²` kernels are compact (`Spectra/SpectralTheory/IntegralOperator.lean`).  Mathlib lacks this;
the proof goes via `MemLp.induction_dense` + the rectangle π-system + a σ-finite exhaustion (the
`spanningSets`) handling the complement step, using
`exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring`.
-/

open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal

namespace Spectra.CompactOperator


/-- The family of measurable rectangles in `α × β`. -/
def rectangles (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Set (Set (α × β)) :=
  image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }

/-- Measurable rectangles form a set semiring. -/
lemma isSetSemiring_rectangles {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    IsSetSemiring (rectangles α β) := by
  constructor
  · -- empty
    refine ⟨∅, MeasurableSet.empty, ∅, MeasurableSet.empty, by simp⟩
  · -- inter
    rintro _ ⟨A₁, hA₁, B₁, hB₁, rfl⟩ _ ⟨A₂, hA₂, B₂, hB₂, rfl⟩
    refine ⟨A₁ ∩ A₂, hA₁.inter hA₂, B₁ ∩ B₂, hB₁.inter hB₂, ?_⟩
    rw [Set.prod_inter_prod]
  · -- diff = disjoint union
    rintro _ ⟨A₁, hA₁, B₁, hB₁, rfl⟩ _ ⟨A₂, hA₂, B₂, hB₂, rfl⟩
    classical
    -- (A₁ ×ˢ B₁) \ (A₂ ×ˢ B₂) = (A₁ \ A₂) ×ˢ B₁  ∪  (A₁ ∩ A₂) ×ˢ (B₁ \ B₂)
    refine ⟨{(A₁ \ A₂) ×ˢ B₁, (A₁ ∩ A₂) ×ˢ (B₁ \ B₂)}, ?_, ?_, ?_⟩
    · intro s hs
      simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · exact ⟨A₁ \ A₂, hA₁.diff hA₂, B₁, hB₁, rfl⟩
      · exact ⟨A₁ ∩ A₂, hA₁.inter hA₂, B₁ \ B₂, hB₁.diff hB₂, rfl⟩
    · -- pairwise disjoint
      rw [Finset.coe_insert, Finset.coe_singleton]
      rw [Set.pairwiseDisjoint_insert]
      refine ⟨Set.pairwiseDisjoint_singleton _ _, ?_⟩
      intro t ht hne
      simp only [mem_singleton_iff] at ht
      subst ht
      simp only [id]
      rw [Set.disjoint_left]
      rintro ⟨x, y⟩ hx hy
      simp only [Set.mem_prod, Set.mem_diff, Set.mem_inter_iff] at hx hy
      exact hx.1.2 hy.1.2
    · -- the union equals the difference
      rw [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton]
      ext ⟨x, y⟩
      simp only [Set.mem_diff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hxA1, hyB1⟩, hnot⟩
        by_cases hxA2 : x ∈ A₂
        · refine Or.inr ⟨⟨hxA1, hxA2⟩, hyB1, ?_⟩
          intro hyB2
          exact hnot ⟨hxA2, hyB2⟩
        · exact Or.inl ⟨⟨hxA1, hxA2⟩, hyB1⟩
      · rintro (⟨⟨hxA1, hxA2⟩, hyB1⟩ | ⟨⟨hxA1, _hxA2⟩, hyB1, hyB2⟩)
        · exact ⟨⟨hxA1, hyB1⟩, fun h => hxA2 h.1⟩
        · exact ⟨⟨hxA1, hyB1⟩, fun h => hyB2 h.2⟩

/-- A "rectangle-simple" function: a finite ℂ-linear combination of indicators of measurable
    rectangles `Aᵢ ×ˢ Bᵢ`, where each side has finite measure. -/
def IsRectSimple {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (g : α × β → ℂ) : Prop :=
  ∃ (s : Finset ℕ) (A : ℕ → Set α) (B : ℕ → Set β) (c : ℕ → ℂ),
    (∀ i, MeasurableSet (A i)) ∧ (∀ i, MeasurableSet (B i)) ∧
    (∀ i, μ (A i) ≠ ∞) ∧ (∀ i, ν (B i) ≠ ∞) ∧
    g = fun p => ∑ i ∈ s, c i * (A i ×ˢ B i).indicator (fun _ => (1 : ℂ)) p

/-- `IsRectSimple` is closed under addition. -/
lemma IsRectSimple.add {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    {f g : α × β → ℂ} (hf : IsRectSimple μ ν f) (hg : IsRectSimple μ ν g) :
    IsRectSimple μ ν (f + g) := by
  classical
  obtain ⟨s, A, B, c, hA, hB, hμA, hνB, rfl⟩ := hf
  obtain ⟨s', A', B', c', hA', hB', hμA', hνB', rfl⟩ := hg
  -- reindex onto disjoint copies of ℕ via Nat.succ-style embedding using even/odd
  refine ⟨s.map ⟨fun n => 2 * n, fun a b h => by dsimp at h; omega⟩ ∪
          s'.map ⟨fun n => 2 * n + 1, fun a b h => by dsimp at h; omega⟩,
        fun n => if n % 2 = 0 then A (n / 2) else A' (n / 2),
        fun n => if n % 2 = 0 then B (n / 2) else B' (n / 2),
        fun n => if n % 2 = 0 then c (n / 2) else c' (n / 2), ?_, ?_, ?_, ?_, ?_⟩
  · intro i; dsimp only; split <;> [exact hA _; exact hA' _]
  · intro i; dsimp only; split <;> [exact hB _; exact hB' _]
  · intro i; dsimp only; split <;> [exact hμA _; exact hμA' _]
  · intro i; dsimp only; split <;> [exact hνB _; exact hνB' _]
  · ext p
    simp only [Pi.add_apply]
    rw [Finset.sum_union]
    · rw [Finset.sum_map, Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        have h1 : (2 * i) % 2 = 0 := by omega
        have h2 : (2 * i) / 2 = i := by omega
        simp [h1, h2]
      · apply Finset.sum_congr rfl
        intro i _
        have h1 : (2 * i + 1) % 2 = 1 := by omega
        have h2 : (2 * i + 1) / 2 = i := by omega
        simp [h1, h2]
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hx'
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, hb⟩ := hx'
      omega

/-- An `IsRectSimple` function is `AEStronglyMeasurable`. -/
lemma IsRectSimple.aestronglyMeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {g : α × β → ℂ} (hg : IsRectSimple μ ν g) :
    AEStronglyMeasurable g (μ.prod ν) := by
  obtain ⟨s, A, B, c, hA, hB, _hμA, _hνB, rfl⟩ := hg
  have : (fun p => ∑ i ∈ s, c i * (A i ×ˢ B i).indicator (fun _ => (1 : ℂ)) p)
      = ∑ i ∈ s, fun p => c i * (A i ×ˢ B i).indicator (fun _ => (1 : ℂ)) p := by
    ext p; simp [Finset.sum_apply]
  rw [this]
  apply Finset.aestronglyMeasurable_sum
  intro i _
  apply AEStronglyMeasurable.const_mul
  apply (StronglyMeasurable.indicator _ ((hA i).prod (hB i))).aestronglyMeasurable
  exact stronglyMeasurable_const

/-- The zero function is `IsRectSimple`. -/
lemma isRectSimple_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} :
    IsRectSimple μ ν (fun _ : α × β => (0 : ℂ)) :=
  ⟨∅, fun _ => ∅, fun _ => ∅, fun _ => 0, fun _ => MeasurableSet.empty,
    fun _ => MeasurableSet.empty, fun _ => by simp, fun _ => by simp, by ext p; simp⟩

/-- A single scaled rectangle indicator is `IsRectSimple`. -/
lemma isRectSimple_single {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (c : ℂ) {A : Set α} {B : Set β} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ A ≠ ∞) (hνB : ν B ≠ ∞) :
    IsRectSimple μ ν (fun p => c * (A ×ˢ B).indicator (fun _ => (1 : ℂ)) p) :=
  ⟨{0}, fun _ => A, fun _ => B, fun _ => c, fun _ => hA, fun _ => hB,
    fun _ => hμA, fun _ => hνB, by ext p; simp⟩

/-- `IsRectSimple` is closed under finite sums indexed by a `Finset`. -/
lemma isRectSimple_finset_sum {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (s : Finset γ) (g : γ → α × β → ℂ) (hg : ∀ i ∈ s, IsRectSimple μ ν (g i)) :
    IsRectSimple μ ν (fun p => ∑ i ∈ s, g i p) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isRectSimple_zero
  | insert a s ha ih =>
    have hsum : (fun p => ∑ i ∈ insert a s, g i p)
        = (g a) + (fun p => ∑ i ∈ s, g i p) := by
      ext p; rw [Finset.sum_insert ha]; rfl
    rw [hsum]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

/-- If `T` is a finite union of disjoint measurable rectangles (a `Finpartition` with rectangle
parts) and `R₀ = A₀ ×ˢ B₀` is a rectangle with finite-measure sides, then `c • 𝟙_{T ∩ R₀}` is
`IsRectSimple`. -/
lemma isRectSimple_indicator_inter_rect {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (c : ℂ) {T : Set (α × β)} (P : Finpartition T) (hP : ↑P.parts ⊆ rectangles α β)
    {A₀ : Set α} {B₀ : Set β} (hA₀ : MeasurableSet A₀) (hB₀ : MeasurableSet B₀)
    (hμA₀ : μ A₀ ≠ ∞) (hνB₀ : ν B₀ ≠ ∞) :
    IsRectSimple μ ν (fun p => c * (T ∩ (A₀ ×ˢ B₀)).indicator (fun _ => (1 : ℂ)) p) := by
  classical
  set R₀ := A₀ ×ˢ B₀ with hR₀
  -- ⋃ R ∈ parts, (R ∩ R₀) = T ∩ R₀, pairwise disjoint
  have hTeq : (⋃ R ∈ P.parts, R) = T := by
    have := Finset.sup_set_eq_biUnion P.parts (id : Set (α × β) → Set (α × β))
    simp only [id] at this
    rw [← this]; exact P.sup_parts
  have hdisj : (↑P.parts : Set (Set (α × β))).PairwiseDisjoint id := Finpartition.disjoint P
  have hdisj' : (↑P.parts : Set (Set (α × β))).PairwiseDisjoint (fun R => R ∩ R₀) := by
    intro x hx y hy hxy
    exact (hdisj hx hy hxy).mono (Set.inter_subset_left) (Set.inter_subset_left)
  have hunion : (⋃ R ∈ P.parts, (R ∩ R₀)) = T ∩ R₀ := by
    rw [← Set.iUnion₂_inter, hTeq]
  have hindeq : ∀ p, c * (T ∩ R₀).indicator (fun _ => (1 : ℂ)) p
      = ∑ R ∈ P.parts, c * (R ∩ R₀).indicator (fun _ => (1 : ℂ)) p := by
    intro p
    rw [← Finset.mul_sum]
    congr 1
    have key := Finset.indicator_biUnion_apply P.parts (fun R => R ∩ R₀)
      (f := fun _ => (1 : ℂ)) hdisj' p
    rw [← key, hunion]
  have : (fun p => c * (T ∩ R₀).indicator (fun _ => (1 : ℂ)) p)
      = (fun p => ∑ R ∈ P.parts, c * (R ∩ R₀).indicator (fun _ => (1 : ℂ)) p) := by
    ext p; exact hindeq p
  rw [this]
  apply isRectSimple_finset_sum
  intro R hR
  obtain ⟨A, hA, B, hB, rfl⟩ := hP hR
  rw [hR₀, Set.prod_inter_prod]
  refine isRectSimple_single c (hA.inter hA₀) (hB.inter hB₀) ?_ ?_
  · exact ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.2 hμA₀)).ne
  · exact ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.2 hνB₀)).ne

/-- The `h0P` step: a finite-measure measurable set's scaled indicator can be approximated in
`L²` by an `IsRectSimple` function. -/
lemma h0P_rect {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    (c : ℂ) {S : Set (α × β)} (hS : MeasurableSet S) (hSfin : (μ.prod ν) S < ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α × β → ℂ,
      eLpNorm (g - S.indicator (fun _ => c)) 2 (μ.prod ν) ≤ ε ∧ IsRectSimple μ ν g := by
  classical
  set ρ := μ.prod ν with hρ
  -- exhausting rectangles
  set E : ℕ → Set (α × β) := fun n => spanningSets μ n ×ˢ spanningSets ν n with hE
  have hEmeas : ∀ n, MeasurableSet (E n) := fun n =>
    (measurableSet_spanningSets μ n).prod (measurableSet_spanningSets ν n)
  have hEmono : Monotone E := by
    intro m n hmn
    exact Set.prod_mono (monotone_spanningSets μ hmn) (monotone_spanningSets ν hmn)
  have hEunion : (⋃ n, E n) = univ := by
    rw [hE]
    rw [Set.iUnion_prod_of_monotone (monotone_spanningSets μ) (monotone_spanningSets ν),
      iUnion_spanningSets μ, iUnion_spanningSets ν, univ_prod_univ]
  have hEfin : ∀ n, ρ (E n) < ∞ := by
    intro n
    rw [hρ, hE, Measure.prod_prod]
    exact ENNReal.mul_lt_top (measure_spanningSets_lt_top μ n) (measure_spanningSets_lt_top ν n)
  -- Handle ε = ∞ trivially.
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact ⟨fun _ => 0, le_top, isRectSimple_zero⟩
  -- Handle c = 0.
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨fun _ => 0, ?_, isRectSimple_zero⟩
    rw [show ((fun _ => (0:ℂ)) - S.indicator (fun _ => (0:ℂ))) = (fun _ => (0:ℂ)) by
      ext p; simp]
    simp
  -- Main case: ε ≠ 0, ε ≠ ∞, c ≠ 0.
  set en : ℝ≥0∞ := ‖c‖ₑ with hen
  have hen0 : en ≠ 0 := by simp [hen, hc]
  have hentop : en ≠ ∞ := by simp [hen]
  -- budget δ
  set δ : ℝ≥0∞ := (ε / en) ^ (2:ℝ) with hδdef
  have hdiv0 : ε / en ≠ 0 := ENNReal.div_ne_zero.2 ⟨hε, hentop⟩
  have _hdivtop : ε / en ≠ ∞ := ENNReal.div_ne_top hεtop hen0
  have hδ0 : δ ≠ 0 := by
    rw [hδdef]; simp [hdiv0]
  have _hδ0' : 0 < δ := pos_iff_ne_zero.2 hδ0
  -- key: en * δ^(1/2) ≤ ε
  have hbudget : en * δ ^ ((1:ℝ)/2) ≤ ε := by
    have hpow : δ ^ ((1:ℝ)/2) = ε / en := by
      rw [hδdef, ← ENNReal.rpow_mul]
      norm_num
    rw [hpow, ENNReal.mul_div_cancel hen0 hentop]
  -- half budget
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ0
  -- Step 1: pick n with ρ (S \ E n) < δ / 2.
  have hSdiff : ∃ n, ρ (S \ E n) < δ / 2 := by
    have hmono : Monotone (fun n => S ∩ E n) := fun m n hmn =>
      Set.inter_subset_inter_right S (hEmono hmn)
    have hunion : (⋃ n, S ∩ E n) = S := by
      rw [← Set.inter_iUnion, hEunion, Set.inter_univ]
    have htend : Filter.Tendsto (fun n => ρ (S ∩ E n)) Filter.atTop (nhds (ρ S)) := by
      have := tendsto_measure_iUnion_atTop (μ := ρ) hmono
      rwa [hunion] at this
    have hSEle : ∀ n, ρ (S ∩ E n) ≤ ρ S := fun n => measure_mono Set.inter_subset_left
    have htend2 : Filter.Tendsto (fun n => ρ S - ρ (S ∩ E n)) Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_const_sub_nhds_zero_iff hSfin.ne hSEle).2 htend
    have heq : ∀ n, ρ (S \ E n) = ρ S - ρ (S ∩ E n) := by
      intro n
      rw [← measure_inter_add_diff S (hEmeas n)]  -- ρ(S∩Eₙ) + ρ(S\Eₙ) = ρ S
      rw [ENNReal.add_sub_cancel_left ((lt_of_le_of_lt (hSEle n) hSfin).ne)]
    have : Filter.Tendsto (fun n => ρ (S \ E n)) Filter.atTop (nhds 0) := by
      simp only [heq]; exact htend2
    obtain ⟨n, hn⟩ := ((this.eventually_lt_const hδ2)).exists
    exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hSdiff
  -- Step 2: approximate S in the finite measure m := ρ.restrict (E n).
  have hmfin : IsFiniteMeasure (ρ.restrict (E n)) :=
    isFiniteMeasure_restrict.2 (hEfin n).ne
  -- covering condition: D = { Aₖ ×ˢ Bₗ } countable, complement null (in fact empty)
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (α × β))
      = generateFrom (rectangles α β) := by
    unfold rectangles; exact generateFrom_prod.symm
  have hcover : ∃ D : Set (Set (α × β)), D.Countable ∧ D ⊆ rectangles α β ∧
      (ρ.restrict (E n)) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{ R | ∃ k l, R = spanningSets μ k ×ˢ spanningSets ν l }, ?_, ?_, ?_⟩
    · -- countable
      apply Set.Countable.mono
        (s₂ := ⋃ k, ⋃ l, {spanningSets μ k ×ˢ spanningSets ν l})
      · rintro R ⟨k, l, rfl⟩; simp only [Set.mem_iUnion, Set.mem_singleton_iff]; exact ⟨k, l, rfl⟩
      · exact Set.countable_iUnion (fun k =>
          Set.countable_iUnion (fun l => Set.countable_singleton _))
    · rintro R ⟨k, l, rfl⟩
      exact ⟨_, measurableSet_spanningSets μ k, _, measurableSet_spanningSets ν l, rfl⟩
    · -- complement is empty
      convert measure_empty (μ := ρ.restrict (E n))
      rw [Set.compl_empty_iff]
      apply Set.eq_univ_of_univ_subset
      intro p _
      simp only [Set.mem_sUnion, Set.mem_setOf_eq]
      have hpμ : p.1 ∈ ⋃ k, spanningSets μ k := by rw [iUnion_spanningSets]; trivial
      have hpν : p.2 ∈ ⋃ l, spanningSets ν l := by rw [iUnion_spanningSets]; trivial
      simp only [Set.mem_iUnion] at hpμ hpν
      obtain ⟨k, hk⟩ := hpμ
      obtain ⟨l, hl⟩ := hpν
      exact ⟨_, ⟨k, l, rfl⟩, ⟨hk, hl⟩⟩
  obtain ⟨T, hTsup, hTapprox⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring isSetSemiring_rectangles
      hcover hgen hS hδ2
  -- m(T △ S) = ρ ((T △ S) ∩ E n) < δ/2
  have hTmeas : MeasurableSet T := by
    rw [hgen]; exact measurableSet_generateFrom_of_mem_supClosure hTsup
  have hTapprox' : ρ ((T ∆ S) ∩ E n) < δ / 2 := by
    rwa [Measure.restrict_apply ((hTmeas.symmDiff hS))] at hTapprox
  -- Build the rect-simple function g = c • 𝟙_{T ∩ E n}.
  obtain ⟨P, hP⟩ := (isSetSemiring_rectangles.mem_supClosure_iff).mp hTsup
  set T' : Set (α × β) := T ∩ E n with hT'def
  have hgrect : IsRectSimple μ ν (fun p => c * (T').indicator (fun _ => (1:ℂ)) p) := by
    rw [hT'def, hE]
    exact isRectSimple_indicator_inter_rect c P hP (measurableSet_spanningSets μ n)
      (measurableSet_spanningSets ν n) (measure_spanningSets_lt_top μ n).ne
      (measure_spanningSets_lt_top ν n).ne
  refine ⟨fun p => c * (T').indicator (fun _ => (1:ℂ)) p, ?_, hgrect⟩
  -- compute the eLpNorm
  have hT'meas : MeasurableSet T' := hTmeas.inter (hEmeas n)
  have hgeq : (fun p => c * (T').indicator (fun _ => (1:ℂ)) p) = (T').indicator (fun _ => c) := by
    ext p; by_cases h : p ∈ T' <;> simp [Set.indicator, h]
  rw [hgeq]
  rw [eLpNorm_indicator_sub_indicator]
  rw [eLpNorm_indicator_const (hT'meas.symmDiff hS) (by norm_num) (by norm_num)]
  -- now: ‖c‖ₑ * ρ(T' △ S)^(1/2) ≤ ε
  simp only [ENNReal.toReal_ofNat]
  -- bound ρ(T' △ S) ≤ δ
  have hsymm_le : ρ (T' ∆ S) ≤ δ := by
    have hsub : T' ∆ S ⊆ ((T ∆ S) ∩ E n) ∪ (S \ E n) := by
      intro x hx
      rw [Set.mem_symmDiff] at hx
      rcases hx with ⟨hxT', hxS⟩ | ⟨hxT', hxS⟩
      · -- x ∈ T', x ∉ S
        have hxT'' : x ∈ T ∩ E n := hxT'
        obtain ⟨hxT, hxE⟩ := hxT''
        left
        exact ⟨Set.mem_symmDiff.2 (Or.inl ⟨hxT, hxS⟩), hxE⟩
      · -- second disjunct: x ∈ S, x ∉ T'
        have hxSmem : x ∈ S := hxT'
        have hxT'' : x ∉ T ∩ E n := hxS
        by_cases hxE : x ∈ E n
        · left
          refine ⟨Set.mem_symmDiff.2 (Or.inr ⟨hxSmem, ?_⟩), hxE⟩
          intro hxT; exact hxT'' ⟨hxT, hxE⟩
        · right; exact ⟨hxSmem, hxE⟩
    calc ρ (T' ∆ S) ≤ ρ (((T ∆ S) ∩ E n) ∪ (S \ E n)) := measure_mono hsub
      _ ≤ ρ ((T ∆ S) ∩ E n) + ρ (S \ E n) := measure_union_le _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add hTapprox'.le hn.le
      _ = δ := ENNReal.add_halves δ
  calc en * ρ (T' ∆ S) ^ ((1:ℝ)/2) ≤ en * δ ^ ((1:ℝ)/2) := by
        gcongr
      _ ≤ ε := hbudget

/-- Finite ℂ-linear combinations of indicators of finite-measure measurable rectangles are dense
in `L²(μ × ν)` for σ-finite `μ`, `ν`. -/
theorem rectSimple_dense {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    {f : α × β → ℂ} (hf : MemLp f 2 (μ.prod ν)) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α × β → ℂ, eLpNorm (f - g) 2 (μ.prod ν) ≤ ε ∧ IsRectSimple μ ν g := by
  refine MemLp.induction_dense (E := ℂ) (p := 2) (μ := μ.prod ν)
    (by norm_num) (IsRectSimple μ ν) ?_ ?_ ?_ hf hε
  · -- h0P
    intro c s hs hsfin η hη
    -- induction_dense wants  eLpNorm (g - s.indicator (fun _ => c)) ≤ η
    exact h0P_rect c hs hsfin hη
  · -- h1P : closed under addition
    intro f g hf hg
    exact hf.add hg
  · -- h2P : AEStronglyMeasurable
    intro f hf
    exact hf.aestronglyMeasurable


end Spectra.CompactOperator

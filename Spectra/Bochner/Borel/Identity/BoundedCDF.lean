/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.Borel.CDF
import Spectra.Herglotz.Stieltjes.IntegralConv

/-!
# Bounded-window convergence of Riemann–Stieltjes integrals

## Main statements

* `integral_Ioc_tendsto_of_cdf_tendsto`: if a sequence of monotone, right-continuous CDFs
  `F (φ k)` converges pointwise to a monotone `G` at every continuity point of `G`, then for
  any bounded window `Ioc a b` with `a`, `b` continuity points of `G` and any continuous `g`,
  the Riemann–Stieltjes integrals over that window converge:
  `∫_{Ioc a b} g dμ_{F (φ k)} → ∫_{Ioc a b} g dμ_G`.

## Implementation notes

This is the bounded-window counterpart of `integral_tendsto_of_cdf_tendsto`
(`Herglotz/Stieltjes/IntegralConv.lean`), which additionally assumes `F`/`G` are supported on
`[0, 2π]`. Once the window `[a, b]` is bounded and its endpoints are continuity points of `G`,
those support hypotheses become unnecessary: the same partition-and-triangle-inequality
argument goes through, with the `Icc`-first-cell decomposition of the unbounded case replaced
by a decomposition entirely in terms of `Ioc` cells — slightly simpler here, since `a` and `b`
are already continuity points of `G`, so there is no asymmetric first cell to special-case.

The proof fixes a partition `a = t 0 < t 1 < ⋯ < t n = b` of continuity points of `G` whose mesh
is below the modulus of uniform continuity of `g` on `[a, b]`, then approximates each of
`∫ g dμ_{F(φ k)}` and `∫ g dμ_G` by the Riemann–Stieltjes sum over that partition. The final
bound is a triangle inequality through those two sums,
`‖∫ g dμ_{F(φ k)} − ∫ g dμ_G‖ ≤ ‖∫ g dμ_{F(φ k)} − RS k‖ + ‖RS k − RS_inf‖ + ‖RS_inf − ∫ g dμ_G‖`,
where the outer two terms are controlled by the oscillation bound on each cell and the middle
term by convergence of the cell masses themselves.

## References

* [Billingsley, *Convergence of Probability Measures*][billingsley1999], for the portmanteau
  theorem underlying this style of weak-convergence argument.
* `Herglotz/Stieltjes/IntegralConv.lean`, for the unbounded/`[0, 2π]`-supported sibling result
  `integral_tendsto_of_cdf_tendsto`.

## Tags

Riemann–Stieltjes integral, portmanteau lemma, weak convergence, cumulative distribution
function
-/

open Complex MeasureTheory Filter Topology
open Spectra.Herglotz
open scoped ENNReal

namespace Spectra.Borel

/-- Bounded-window version of `integral_tendsto_of_cdf_tendsto`.
The `[0,2π]`/support hypotheses are unused once the interval is bounded — what survives
is the same partition argument with `Icc` first-cell replaced by an all-`Ioc` decomposition
(slightly cleaner since both endpoints are continuity points of `G`). -/
lemma integral_Ioc_tendsto_of_cdf_tendsto
    {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {φ : ℕ → ℕ}
    (mono_F : ∀ N, Monotone (F N)) (mono_G : Monotone G)
    (rc_F : ∀ N x, Function.rightLim (F N) x = F N x)
    (conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)))
    {a b : ℝ} (hab : a ≤ b) (ha : ContinuousAt G a) (hb : ContinuousAt G b)
    {g : ℝ → ℂ} (hg : Continuous g) :
    Tendsto (fun k => ∫ x in Set.Ioc a b, g x ∂((mono_F (φ k)).stieltjesFunction.measure))
      atTop (𝓝 (∫ x in Set.Ioc a b, g x ∂(mono_G.stieltjesFunction.measure))) := by
  -- ══════ TRIVIAL CASE  a = b ══════
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · rw [hab_eq, show Set.Ioc b b = (∅ : Set ℝ) from Set.Ioc_eq_empty_of_le (le_refl b)]
    simp only [setIntegral_empty]
    exact tendsto_const_nhds
  -- ══════ SETUP  (case a < b) ══════
  set μk : ℕ → Measure ℝ := fun k => (mono_F (φ k)).stieltjesFunction.measure with _hμk_def
  set μ  : Measure ℝ     := mono_G.stieltjesFunction.measure                  with _hμ_def
  -- Cell-mass identity (F-side: rc_F directly).
  have mass_k : ∀ k c d, c ≤ d →
      (μk k (Set.Ioc c d)).toReal = F (φ k) d - F (φ k) c := by
    intro k c d hcd
    change ((mono_F (φ k)).stieltjesFunction.measure (Set.Ioc c d)).toReal = F (φ k) d - F (φ k) c
    rw [StieltjesFunction.measure_Ioc,
        (mono_F (φ k)).stieltjesFunction_eq, (mono_F (φ k)).stieltjesFunction_eq,
        rc_F (φ k) d, rc_F (φ k) c,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (mono_F (φ k) hcd))]
  -- Cell-mass identity (G-side: at continuity points only).
  have mass_G_cont : ∀ c d, c ≤ d → ContinuousAt G c → ContinuousAt G d →
      (μ (Set.Ioc c d)).toReal = G d - G c := by
    intro c d hcd hcc hdd
    change (mono_G.stieltjesFunction.measure (Set.Ioc c d)).toReal = G d - G c
    rw [StieltjesFunction.measure_Ioc,
        stieltjes_eq_at_continuousAt G mono_G d hdd,
        stieltjes_eq_at_continuousAt G mono_G c hcc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (mono_G hcd))]
  set M : ℝ := G b - G a with hM_def
  -- Not referenced by name below: `positivity` uses it to prove `0 < M + 1` (hence `0 < ε`) and
  -- `field_simp` uses it to discharge `M + 1 ≠ 0` in `hε_safe`, both via local-context search.
  have hM_nn : 0 ≤ M := sub_nonneg.mpr (mono_G hab)
  have hMk_tendsto : Tendsto (fun k => F (φ k) b - F (φ k) a) atTop (𝓝 M) :=
    (conv b hb).sub (conv a ha)
  -- ══════ ε-δ UNWRAP ══════
  rw [Metric.tendsto_atTop]
  intro ε₀ hε₀
  set ε := ε₀ / (4 * (M + 1)) with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_safe : ε * (M + 1) = ε₀ / 4 := by
    rw [hε_def]; field_simp
  -- Uniform continuity on the compact [a, b].
  have huc : UniformContinuousOn g (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  obtain ⟨δ, hδ_pos, hδ_uc⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε_pos
  -- ══════ PARTITION ══════
  -- a = t 0 < t 1 < ⋯ < t n = b, all t_i continuity points of G, gaps < δ.
  have hS : {x : ℝ | ¬ ContinuousAt G x}.Countable := mono_G.countable_not_continuousAt
  have ha' : a ∉ {x | ¬ ContinuousAt G x} := fun h => h ha
  have hb' : b ∉ {x | ¬ ContinuousAt G x} := fun h => h hb
  obtain ⟨n, t, _hn, h_t0, h_tn, h_mono_t, h_gap, h_notS⟩ :=
    exists_partition_avoiding_countable hS hab_lt ha' hb' hδ_pos
  have h_cont_t : ∀ i ≤ n, ContinuousAt G (t i) := fun i hi => not_not.mp (h_notS i hi)
  -- t monotone in i; t_i ∈ [a, b]
  have h_tmono : ∀ j, j ≤ n → ∀ i, i ≤ j → t i ≤ t j := by
    intro j
    induction j with
    | zero => intro _ i hi; obtain rfl := Nat.le_zero.mp hi; exact le_refl _
    | succ m ih =>
        intro hsm i hi
        have hmn : m < n := Nat.lt_of_succ_le hsm
        rcases eq_or_lt_of_le hi with heq | hlt
        · subst heq; exact le_refl _
        · exact le_trans (ih (le_of_lt hmn) i (Nat.lt_succ_iff.mp hlt))
            (le_of_lt (h_mono_t m hmn))
  have h_tmem : ∀ i, i ≤ n → t i ∈ Set.Icc a b := fun i hi =>
    ⟨by rw [← h_t0]; exact h_tmono i hi 0 (Nat.zero_le i),
     by rw [← h_tn]; exact h_tmono n (le_refl n) i hi⟩
  -- ══════ INTEGRABILITY ══════
  have hg_int : ∀ (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (c d : ℝ),
      IntegrableOn g (Set.Ioc c d) ν := by
    intro ν _ c d
    exact (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  -- ══════ INTEGRAL SPLIT  Ioc a b = ⨆ Ioc-cells ══════
  have split_lemma : ∀ (ν : Measure ℝ) [IsLocallyFiniteMeasure ν],
      ∫ x in Set.Ioc a b, g x ∂ν
        = ∑ i ∈ Finset.range n, ∫ x in Set.Ioc (t i) (t (i + 1)), g x ∂ν := by
    intro ν _
    have hind : ∀ m, m ≤ n →
        ∫ x in Set.Ioc (t 0) (t m), g x ∂ν
          = ∑ i ∈ Finset.range m, ∫ x in Set.Ioc (t i) (t (i + 1)), g x ∂ν := by
      intro m
      induction m with
      | zero =>
          intro _
          rw [show Set.Ioc (t 0) (t 0) = (∅ : Set ℝ) from
                Set.Ioc_eq_empty_of_le (le_refl _),
              setIntegral_empty, Finset.sum_range_zero]
      | succ k ih =>
          intro hk
          have hk' : k ≤ n := by omega
          have hkn : k < n := by omega
          have h_t0_le : t 0 ≤ t k := h_tmono k hk' 0 (Nat.zero_le k)
          have h_tk_le : t k ≤ t (k + 1) := le_of_lt (h_mono_t k hkn)
          have hsplit : Set.Ioc (t 0) (t (k + 1)) =
              Set.Ioc (t 0) (t k) ∪ Set.Ioc (t k) (t (k + 1)) :=
            (Set.Ioc_union_Ioc_eq_Ioc h_t0_le h_tk_le).symm
          have hdisj : Disjoint (Set.Ioc (t 0) (t k))
              (Set.Ioc (t k) (t (k + 1))) := by
            rw [Set.disjoint_left]
            rintro x ⟨_, hx2⟩ ⟨hx3, _⟩
            exact absurd hx3 (not_lt.mpr hx2)
          rw [hsplit,
              setIntegral_union hdisj measurableSet_Ioc
                (hg_int ν (t 0) (t k)) (hg_int ν (t k) (t (k + 1))),
              ih hk', Finset.sum_range_succ]
    have hmain := hind n (le_refl n)
    rw [h_t0, h_tn] at hmain
    exact hmain
  -- ══════ CELL MASS CONVERGENCE ══════
  have cell_mass_F : ∀ k i, i < n →
      (μk k (Set.Ioc (t i) (t (i + 1)))).toReal
        = F (φ k) (t (i + 1)) - F (φ k) (t i) :=
    fun k i hi => mass_k k _ _ (le_of_lt (h_mono_t i hi))
  have cell_mass_G : ∀ i, i < n →
      (μ (Set.Ioc (t i) (t (i + 1)))).toReal = G (t (i + 1)) - G (t i) :=
    fun i hi => mass_G_cont _ _ (le_of_lt (h_mono_t i hi))
      (h_cont_t i (le_of_lt hi)) (h_cont_t (i + 1) hi)
  have cell_mass_tendsto : ∀ i, i < n →
      Tendsto (fun k => (μk k (Set.Ioc (t i) (t (i + 1)))).toReal) atTop
        (𝓝 ((μ (Set.Ioc (t i) (t (i + 1)))).toReal)) := by
    intro i hi
    rw [cell_mass_G i hi]
    refine ((conv (t (i + 1)) (h_cont_t (i + 1) hi)).sub
      (conv (t i) (h_cont_t i (le_of_lt hi)))).congr' ?_
    exact Eventually.of_forall (fun k => (cell_mass_F k i hi).symm)
  -- ══════ RIEMANN–STIELTJES SUMS ══════
  set RS : ℕ → ℂ := fun k =>
    ∑ i ∈ Finset.range n,
      (μk k (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1)) with _hRS_def
  set RS_inf : ℂ :=
    ∑ i ∈ Finset.range n,
      (μ (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1)) with hRS_inf_def
  have hRS_tendsto : Tendsto RS atTop (𝓝 RS_inf) := by
    change Tendsto (fun k => ∑ i ∈ Finset.range n,
        (μk k (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))) atTop
      (𝓝 (∑ i ∈ Finset.range n,
        (μ (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))))
    refine tendsto_finsetSum _ (fun i hi => ?_)
    exact (cell_mass_tendsto i (Finset.mem_range.mp hi)).smul_const (g (t (i + 1)))
  -- ══════ PER-CELL ERROR BOUND ══════
  have cell_bound : ∀ (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (i : ℕ), i < n →
      ‖(∫ x in Set.Ioc (t i) (t (i + 1)), g x ∂ν)
          - (ν (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))‖
        ≤ ε * (ν (Set.Ioc (t i) (t (i + 1)))).toReal := by
    intro ν _ i hi
    -- oscillation control on this cell
    have h_osc : ∀ x ∈ Set.Ioc (t i) (t (i + 1)), ‖g x - g (t (i + 1))‖ ≤ ε := by
      intro x hx
      have ht_i_mem : t i ∈ Set.Icc a b := h_tmem i (le_of_lt hi)
      have ht_ip1_mem : t (i + 1) ∈ Set.Icc a b := h_tmem (i + 1) hi
      have hx_mem : x ∈ Set.Icc a b :=
        ⟨le_trans ht_i_mem.1 (le_of_lt hx.1), le_trans hx.2 ht_ip1_mem.2⟩
      have hdist : dist x (t (i + 1)) < δ := by
        rw [Real.dist_eq, abs_lt]
        refine ⟨by linarith [hx.1, h_gap i hi], by linarith [hx.2, hδ_pos]⟩
      have h := hδ_uc x hx_mem (t (i + 1)) ht_ip1_mem hdist
      rw [dist_eq_norm] at h
      exact le_of_lt h
    have hS_fin : ν (Set.Ioc (t i) (t (i + 1))) < ∞ := measure_Ioc_lt_top
    have hg_intS : IntegrableOn g (Set.Ioc (t i) (t (i + 1))) ν := hg_int ν _ _
    have h_const_intS : IntegrableOn (fun _ : ℝ => g (t (i + 1)))
        (Set.Ioc (t i) (t (i + 1))) ν := integrableOn_const hS_fin.ne
    -- ∫ S g - μ(S).toReal • c = ∫ S (g - c) via setIntegral_const + measureReal_def
    have h1 : (∫ x in Set.Ioc (t i) (t (i + 1)), (g x - g (t (i + 1))) ∂ν)
        = (∫ x in Set.Ioc (t i) (t (i + 1)), g x ∂ν)
          - ∫ x in Set.Ioc (t i) (t (i + 1)), g (t (i + 1)) ∂ν :=
      integral_sub hg_intS h_const_intS
    have h_diff : (∫ x in Set.Ioc (t i) (t (i + 1)), g x ∂ν)
          - (ν (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))
        = ∫ x in Set.Ioc (t i) (t (i + 1)), (g x - g (t (i + 1))) ∂ν := by
      rw [h1, setIntegral_const, measureReal_def]
    rw [h_diff]
    have h_bd := norm_setIntegral_le_of_norm_le_const (μ := ν)
      (s := Set.Ioc (t i) (t (i + 1))) (C := ε) hS_fin h_osc
    rwa [measureReal_def] at h_bd
  -- ══════ TOTAL APPROXIMATION BOUND ══════
  have total_bound : ∀ (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (totalMass : ℝ),
      ∑ i ∈ Finset.range n, (ν (Set.Ioc (t i) (t (i + 1)))).toReal = totalMass →
      ‖(∫ x in Set.Ioc a b, g x ∂ν)
          - ∑ i ∈ Finset.range n,
              (ν (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))‖
        ≤ ε * totalMass := by
    intro ν _ totalMass h_total
    rw [split_lemma ν]
    have h_combine : (∑ i ∈ Finset.range n, ∫ x in Set.Ioc (t i) (t (i + 1)), g x ∂ν)
          - ∑ i ∈ Finset.range n,
              (ν (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))
        = ∑ i ∈ Finset.range n,
            ((∫ x in Set.Ioc (t i) (t (i + 1)), g x ∂ν)
              - (ν (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))) := by
      rw [Finset.sum_sub_distrib]
    rw [h_combine]
    refine le_trans (norm_sum_le _ _) ?_
    rw [← h_total, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => cell_bound ν i (Finset.mem_range.mp hi))
  -- Telescoping (∑ cell masses = total mass)
  have sum_masses_F : ∀ k,
      ∑ i ∈ Finset.range n, (μk k (Set.Ioc (t i) (t (i + 1)))).toReal
        = F (φ k) b - F (φ k) a := by
    intro k
    rw [Finset.sum_congr rfl
      (fun i hi => cell_mass_F k i (Finset.mem_range.mp hi))]
    have htel : ∑ i ∈ Finset.range n, (F (φ k) (t (i + 1)) - F (φ k) (t i))
        = F (φ k) (t n) - F (φ k) (t 0) :=
      Finset.sum_range_sub (fun i => F (φ k) (t i)) n
    rw [htel, h_tn, h_t0]
  have sum_masses_G :
      ∑ i ∈ Finset.range n, (μ (Set.Ioc (t i) (t (i + 1)))).toReal = M := by
    rw [Finset.sum_congr rfl
      (fun i hi => cell_mass_G i (Finset.mem_range.mp hi))]
    have htel : ∑ i ∈ Finset.range n, (G (t (i + 1)) - G (t i))
        = G (t n) - G (t 0) :=
      Finset.sum_range_sub (fun i => G (t i)) n
    rw [htel, h_tn, h_t0, hM_def]
  -- ══════ COMBINE  (triangle inequality) ══════
  obtain ⟨K₁, hK₁⟩ : ∃ K, ∀ k ≥ K, F (φ k) b - F (φ k) a ≤ M + 1 := by
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hMk_tendsto 1 (by norm_num)
    refine ⟨K, fun k hk => ?_⟩
    have := hK k hk; rw [Real.dist_eq, abs_lt] at this; linarith
  obtain ⟨K₂, hK₂⟩ : ∃ K, ∀ k ≥ K, ‖RS k - RS_inf‖ < ε₀ / 2 := by
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hRS_tendsto (ε₀ / 2) (by linarith)
    refine ⟨K, fun k hk => ?_⟩
    have := hK k hk; rwa [dist_eq_norm] at this
  refine ⟨max K₁ K₂, fun k hk => ?_⟩
  have hk1 : k ≥ K₁ := le_of_max_le_left hk
  have hk2 : k ≥ K₂ := le_of_max_le_right hk
  set intFk := ∫ x in Set.Ioc a b, g x ∂(μk k)
  set RSk := RS k
  set RSinf := RS_inf
  set intG := ∫ x in Set.Ioc a b, g x ∂μ
  have h_tri : ‖intFk - intG‖ ≤ ‖intFk - RSk‖ + ‖RSk - RSinf‖ + ‖RSinf - intG‖ := by
    have heq : intFk - intG = (intFk - RSk) + ((RSk - RSinf) + (RSinf - intG)) := by ring
    calc ‖intFk - intG‖ = ‖(intFk - RSk) + ((RSk - RSinf) + (RSinf - intG))‖ := by rw [heq]
      _ ≤ ‖intFk - RSk‖ + ‖(RSk - RSinf) + (RSinf - intG)‖ := norm_add_le _ _
      _ ≤ ‖intFk - RSk‖ + (‖RSk - RSinf‖ + ‖RSinf - intG‖) := by gcongr; exact norm_add_le _ _
      _ = ‖intFk - RSk‖ + ‖RSk - RSinf‖ + ‖RSinf - intG‖ := by ring
  have hAB : ‖intFk - RSk‖ ≤ ε * (F (φ k) b - F (φ k) a) := by
    change ‖(∫ x in Set.Ioc a b, g x ∂(μk k))
        - ∑ i ∈ Finset.range n,
            (μk k (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))‖
        ≤ ε * (F (φ k) b - F (φ k) a)
    exact total_bound (μk k) _ (sum_masses_F k)
  have hCD : ‖RSinf - intG‖ ≤ ε * M := by
    change ‖RS_inf - ∫ x in Set.Ioc a b, g x ∂μ‖ ≤ ε * M
    rw [norm_sub_rev]
    change ‖(∫ x in Set.Ioc a b, g x ∂μ)
        - ∑ i ∈ Finset.range n,
            (μ (Set.Ioc (t i) (t (i + 1)))).toReal • g (t (i + 1))‖ ≤ ε * M
    exact total_bound μ _ sum_masses_G
  have hAB' : ε * (F (φ k) b - F (φ k) a) ≤ ε₀ / 4 :=
    calc ε * (F (φ k) b - F (φ k) a)
        ≤ ε * (M + 1) := mul_le_mul_of_nonneg_left (hK₁ k hk1) hε_pos.le
      _ = ε₀ / 4 := hε_safe
  rw [dist_eq]
  calc ‖intFk - intG‖
      ≤ ‖intFk - RSk‖ + ‖RSk - RSinf‖ + ‖RSinf - intG‖ := h_tri
    _ < ε * (F (φ k) b - F (φ k) a) + ε₀ / 2 + ε * M := by
        linarith [hAB, hK₂ k hk2, hCD]
    _ ≤ ε₀ / 4 + ε₀ / 2 + ε₀ / 4 := by linarith
    _ = ε₀ := by ring

end Spectra.Borel

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Herglotz.Stieltjes.Hellys
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.IntervalCases

/-!
# Portmanteau-style convergence of Stieltjes integrals

This file proves the portmanteau-style convergence of integrals against Stieltjes measures needed
to pass Helly's selection theorem through the Herglotz representation: if a sequence of monotone
CDFs `F_n` converges pointwise to a monotone limit `G` at every continuity point of `G`, then
`∫ f dF_n → ∫ f dG` for every bounded continuous `f`.

The proof partitions `[0, 2π]` at continuity points of `G` with mesh below any prescribed `δ`
(`exists_cont_partition`), approximates each integral by a Riemann–Stieltjes sum tagged at the
partition's right endpoints (`approx_bound`), and passes to the limit using that the *right
limits* of the approximating CDFs converge to `G` at continuity points (`rightLim_tendsto`). A
general-purpose partition lemma avoiding any prescribed countable "bad" set
(`exists_partition_avoiding_countable`) underlies the construction.

## Main results

* `integral_tendsto_of_cdf_tendsto` : the portmanteau convergence theorem for Stieltjes integrals.
* `fourier_integral_tendsto_of_cdf_tendsto` : its specialization to Fourier coefficients,
  `∫ e^{inθ} dF_n → ∫ e^{inθ} dG`.
* `exists_partition_avoiding_countable` : given a countable `S` and endpoints outside `S`, a
  partition with prescribed mesh bound and all breakpoints outside `S`.
-/

open Complex MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Herglotz

/-! ### Convergence of integrals (portmanteau-style) -/

section IntegralConvergence

/-- At continuity points of `G`, the Stieltjes regularization agrees with `G`. -/
lemma stieltjes_eq_at_continuousAt (G : ℝ → ℝ) (h_mono : Monotone G)
    (x : ℝ) (hx : ContinuousAt G x) :
    h_mono.stieltjesFunction x = G x := by
  rw [h_mono.stieltjesFunction_eq]
  exact (h_mono.continuousWithinAt_Ioi_iff_rightLim_eq).mp hx.continuousWithinAt

/-- Telescoping sum over `Ico 1 n`. -/
private lemma sum_Ico_telescope (g : ℕ → ℝ) : ∀ n, 1 ≤ n →
    ∑ i ∈ Finset.Ico 1 n, (g (i + 1) - g i) = g n - g 1 := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by norm_num)
  | succ m ih =>
    intro _
    rcases Nat.lt_or_ge m 1 with hm | hm
    · interval_cases m; simp
    · rw [Finset.sum_Ico_succ_top hm, ih hm]; ring

/-- Mass of `(a, b]` under a right-continuous monotone CDF `F` equals `F b - F a`. -/
private lemma cdf_mass_toReal {F : ℝ → ℝ} (hF : Monotone F)
    (hF_rc : ∀ x, Function.rightLim F x = F x) {a b : ℝ} (hab : a ≤ b) :
    (hF.stieltjesFunction.measure (Set.Ioc a b)).toReal = F b - F a := by
  rw [StieltjesFunction.measure_Ioc, hF.stieltjesFunction_eq, hF.stieltjesFunction_eq,
      hF_rc, hF_rc, ENNReal.toReal_ofReal (sub_nonneg.mpr (hF hab))]

/-- If `F (φ k) → G` at the continuity points `a, b` of `G`, the masses of `(a, b]`
under the approximating Stieltjes measures converge to the mass under `G`'s measure. (Currently
unused.) -/
private lemma cdf_mass_tendsto {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {φ : ℕ → ℕ}
    (h_mono_F : ∀ N, Monotone (F N)) (h_mono_G : Monotone G)
    (hF_rc : ∀ N x, Function.rightLim (F N) x = F N x)
    (h_conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)))
    {a b : ℝ} (hab : a ≤ b) (ha : ContinuousAt G a) (hb : ContinuousAt G b) :
    Tendsto (fun k => ((h_mono_F (φ k)).stieltjesFunction.measure (Set.Ioc a b)).toReal)
      atTop (𝓝 ((h_mono_G.stieltjesFunction.measure (Set.Ioc a b)).toReal)) := by
  have hGmass : (h_mono_G.stieltjesFunction.measure (Set.Ioc a b)).toReal = G b - G a := by
    rw [StieltjesFunction.measure_Ioc,
        stieltjes_eq_at_continuousAt G h_mono_G b hb,
        stieltjes_eq_at_continuousAt G h_mono_G a ha,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (h_mono_G hab))]
  rw [hGmass]
  simp_rw [fun k => cdf_mass_toReal (h_mono_F (φ k)) (hF_rc (φ k)) hab]
  exact (h_conv b hb).sub (h_conv a ha)

/-- **Part 3 (partition).** For every mesh bound `δ > 0`, `[0, 2π]` admits breakpoints
`0 = t₀ < t₁ < ⋯ < tₙ = 2π` whose *interior* points are continuity points of the monotone
limit `G`, with every gap `< δ`. The endpoints are deliberately unconstrained. -/
private lemma exists_cont_partition {G : ℝ → ℝ} (hG : Monotone G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (t : ℕ → ℝ),
      0 < n ∧ t 0 = 0 ∧ t n = 2 * Real.pi ∧
      (∀ i, i < n → t i < t (i + 1)) ∧
      (∀ i, i < n → t (i + 1) - t i < δ) ∧
      (∀ i, 0 < i → i < n → ContinuousAt G (t i)) := by
  classical
  -- (a) continuity points of a monotone function are dense
  have hDense : Dense {x : ℝ | ContinuousAt G x} := by
    have heq : {x : ℝ | ContinuousAt G x} = {x : ℝ | ¬ ContinuousAt G x}ᶜ := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_not]
    rw [heq]; exact (hG.countable_not_continuousAt).dense_compl ℝ
  -- (b) grid size and spacing
  set K : ℕ := ⌈3 * Real.pi / δ⌉₊ + 1 with hK_def
  have hKpos : 0 < K := Nat.succ_pos _
  have hK2 : 2 ≤ K := by
    have : 0 < ⌈3 * Real.pi / δ⌉₊ := Nat.ceil_pos.mpr (by positivity)
    omega
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  set h : ℝ := 2 * Real.pi / (K : ℝ) with hh_def
  have hh_pos : 0 < h := by rw [hh_def]; positivity
  have hKh : (K : ℝ) * h = 2 * Real.pi := by rw [hh_def]; field_simp
  have hKbig : (3 * Real.pi / δ : ℝ) < (K : ℝ) := by
    have h1 : (3 * Real.pi / δ : ℝ) ≤ (⌈3 * Real.pi / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈3 * Real.pi / δ⌉₊ : ℕ) : ℝ) < (K : ℝ) := by rw [hK_def]; push_cast; linarith
    linarith
  have hmesh : 3 * h / 2 < δ := by
    have e : 3 * h / 2 = 3 * Real.pi / (K : ℝ) := by rw [hh_def]; ring
    rw [e, div_lt_iff₀ hKR]
    have h3 : 3 * Real.pi < (K : ℝ) * δ := (div_lt_iff₀ hδ).mp hKbig
    linarith [h3, mul_comm (K : ℝ) δ]
  -- (c) a continuity point in each window  i·h ± h/4
  have hwin : ∀ j : ℕ, ∃ z, ContinuousAt G z ∧
      z ∈ Set.Ioo ((j : ℝ) * h - h / 4) ((j : ℝ) * h + h / 4) := by
    intro j
    have hlt : (j : ℝ) * h - h / 4 < (j : ℝ) * h + h / 4 := by linarith [hh_pos]
    obtain ⟨z, hz1, hz2⟩ := hDense.exists_between hlt
    exact ⟨z, hz1, hz2⟩
  choose c hcA hcMem using hwin
  have cL : ∀ j : ℕ, (j : ℝ) * h - h / 4 < c j := fun j => (hcMem j).1
  have cU : ∀ j : ℕ, c j < (j : ℝ) * h + h / 4 := fun j => (hcMem j).2
  -- (d) breakpoints
  set t : ℕ → ℝ :=
    (fun i => if i = 0 then 0 else if K ≤ i then 2 * Real.pi else c i) with ht
  have tval : ∀ i, t i = if i = 0 then 0 else if K ≤ i then 2 * Real.pi else c i :=
    fun i => by simp only [ht]
  have tmid : ∀ i, i ≠ 0 → ¬ K ≤ i → t i = c i := by
    intro i h0 hK; rw [tval i, if_neg h0, if_neg hK]
  have t0 : t 0 = 0 := by rw [tval 0, if_pos rfl]
  have tK : t K = 2 * Real.pi := by
    rw [tval K, if_neg (by omega : K ≠ 0), if_pos (le_refl K)]
  refine ⟨K, t, hKpos, t0, tK, ?_, ?_, ?_⟩
  · -- adjacent strict monotonicity
    intro i hi
    have ex : ((i : ℝ) + 1) * h = (i : ℝ) * h + h := by ring
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      change t 0 < t 1
      rw [t0, tmid 1 (by omega) (by omega)]
      have := cL 1; push_cast at this; linarith [hh_pos, this]
    · have hi1 : i + 1 ≤ K := hi
      rcases lt_or_eq_of_le hi1 with hlt | heq
      · rw [tmid i (by omega) (by omega), tmid (i + 1) (by omega) (by omega)]
        have a1 := cU i; have a2 := cL (i + 1); push_cast at a2
        linarith [hh_pos, ex, a1, a2]
      · rw [tmid i (by omega) (by omega), show i + 1 = K from heq, tK]
        have a1 := cU i
        have hiK : (i : ℝ) = (K : ℝ) - 1 := by
          have : (i : ℝ) + 1 = (K : ℝ) := by exact_mod_cast heq
          linarith
        have expand : ((K : ℝ) - 1) * h + h / 4 = 2 * Real.pi - 3 * h / 4 := by
          rw [← hKh]; ring
        have key : (i : ℝ) * h + h / 4 < 2 * Real.pi := by
          rw [hiK, expand]; linarith [hh_pos]
        linarith [a1, key]
  · -- gaps < δ
    intro i hi
    have ex : ((i : ℝ) + 1) * h = (i : ℝ) * h + h := by ring
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      change t 1 - t 0 < δ
      rw [t0, tmid 1 (by omega) (by omega), sub_zero]
      have := cU 1; push_cast at this; linarith [hh_pos, hmesh, this]
    · have hi1 : i + 1 ≤ K := hi
      rcases lt_or_eq_of_le hi1 with hlt | heq
      · rw [tmid i (by omega) (by omega), tmid (i + 1) (by omega) (by omega)]
        have a1 := cU (i + 1); have a2 := cL i; push_cast at a1
        linarith [hh_pos, hmesh, ex, a1, a2]
      · rw [tmid i (by omega) (by omega), show i + 1 = K from heq, tK]
        have a2 := cL i
        have hiK : (i : ℝ) = (K : ℝ) - 1 := by
          have : (i : ℝ) + 1 = (K : ℝ) := by exact_mod_cast heq
          linarith
        have expand : 2 * Real.pi - (((K : ℝ) - 1) * h - h / 4) = 5 * h / 4 := by
          rw [← hKh]; ring
        have key : 2 * Real.pi - ((i : ℝ) * h - h / 4) < δ := by
          rw [hiK, expand]; linarith [hh_pos, hmesh]
        linarith [a2, key]
  · -- interior breakpoints are continuity points
    intro i hi0 hiK
    rw [tmid i (by omega) (by omega)]
    exact hcA i

/-- Splitting `∫_{[0, tₙ]} f` over the partition cells:
the closed first cell `[t₀, t₁]` plus the half-open cells `(tᵢ, tᵢ₊₁]`. -/
private lemma integral_Icc_split {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {f : ℝ → ℂ} (hf : Continuous f) {t : ℕ → ℝ} {n : ℕ}
    (hmono : ∀ i, i < n → t i < t (i + 1)) (hn : 0 < n) :
    (∫ x in Set.Icc (t 0) (t n), f x ∂μ)
      = (∫ x in Set.Icc (t 0) (t 1), f x ∂μ)
        + ∑ i ∈ Finset.Ico 1 n, ∫ x in Set.Ioc (t i) (t (i + 1)), f x ∂μ := by
  have htle : ∀ i j, i ≤ j → j ≤ n → t i ≤ t j := by
    intro i j hij
    induction hij with
    | refl => intro _; exact le_refl _
    | @step m _hm ih =>
        intro hmn
        exact le_trans (ih (by omega)) (le_of_lt (hmono m (by omega)))
  have add_lemma : ∀ m, m + 1 ≤ n →
      (∫ x in Set.Icc (t 0) (t (m + 1)), f x ∂μ)
        = (∫ x in Set.Icc (t 0) (t 1), f x ∂μ)
          + ∑ i ∈ Finset.Ico 1 (m + 1), ∫ x in Set.Ioc (t i) (t (i + 1)), f x ∂μ := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have hIH := ih (by omega)
        have hle1 : t 0 ≤ t (k + 1) := htle 0 (k + 1) (by omega) (by omega)
        have hle2 : t (k + 1) ≤ t (k + 1 + 1) := le_of_lt (hmono (k + 1) (by omega))
        have hsplit : Set.Icc (t 0) (t (k + 1 + 1)) =
            Set.Icc (t 0) (t (k + 1)) ∪ Set.Ioc (t (k + 1)) (t (k + 1 + 1)) :=
          (Set.Icc_union_Ioc_eq_Icc hle1 hle2).symm
        have hdisj : Disjoint (Set.Icc (t 0) (t (k + 1)))
            (Set.Ioc (t (k + 1)) (t (k + 1 + 1))) := by
          rw [Set.disjoint_left]
          rintro x ⟨_, hx2⟩ ⟨hx3, _⟩
          exact absurd hx3 (not_lt.mpr hx2)
        have hi1 : IntegrableOn f (Set.Icc (t 0) (t (k + 1))) μ :=
          hf.continuousOn.integrableOn_compact isCompact_Icc
        have hi2 : IntegrableOn f (Set.Ioc (t (k + 1)) (t (k + 1 + 1))) μ :=
          (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
        calc (∫ x in Set.Icc (t 0) (t (k + 1 + 1)), f x ∂μ)
            = ∫ x in Set.Icc (t 0) (t (k + 1)) ∪ Set.Ioc (t (k + 1)) (t (k + 1 + 1)), f x ∂μ := by
                rw [hsplit]
          _ = (∫ x in Set.Icc (t 0) (t (k + 1)), f x ∂μ)
                + ∫ x in Set.Ioc (t (k + 1)) (t (k + 1 + 1)), f x ∂μ :=
              setIntegral_union hdisj measurableSet_Ioc hi1 hi2
          _ = ((∫ x in Set.Icc (t 0) (t 1), f x ∂μ)
                + ∑ i ∈ Finset.Ico 1 (k + 1), ∫ x in Set.Ioc (t i) (t (i + 1)), f x ∂μ)
                + ∫ x in Set.Ioc (t (k + 1)) (t (k + 1 + 1)), f x ∂μ := by rw [hIH]
          _ = (∫ x in Set.Icc (t 0) (t 1), f x ∂μ)
                + ∑ i ∈ Finset.Ico 1 (k + 1 + 1),
                    ∫ x in Set.Ioc (t i) (t (i + 1)), f x ∂μ := by
                rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]; ring
  have := add_lemma (n - 1) (by omega)
  rwa [Nat.sub_add_cancel hn] at this

/-- If `f` oscillates by `≤ ε` on each partition cell, the
integral is within `ε · (total cell mass)` of the Riemann–Stieltjes sum tagged at right
endpoints. -/
private lemma approx_bound {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {f : ℝ → ℂ} (hf : Continuous f) {t : ℕ → ℝ} {n : ℕ} {ε : ℝ}
    (hmono : ∀ i, i < n → t i < t (i + 1)) (hn : 0 < n)
    (hosc1 : ∀ x ∈ Set.Icc (t 0) (t 1), ‖f x - f (t 1)‖ ≤ ε)
    (hoscI : ∀ i, 1 ≤ i → i < n →
        ∀ x ∈ Set.Ioc (t i) (t (i + 1)), ‖f x - f (t (i + 1))‖ ≤ ε) :
    ‖(∫ x in Set.Icc (t 0) (t n), f x ∂μ)
        - ((μ (Set.Icc (t 0) (t 1))).toReal • f (t 1)
            + ∑ i ∈ Finset.Ico 1 n,
                (μ (Set.Ioc (t i) (t (i + 1)))).toReal • f (t (i + 1)))‖
      ≤ ε * ((μ (Set.Icc (t 0) (t 1))).toReal
            + ∑ i ∈ Finset.Ico 1 n, (μ (Set.Ioc (t i) (t (i + 1)))).toReal) := by
  -- per-cell bound: ‖∫_S f − mass • c‖ ≤ ε·mass when f stays within ε of c on S
  have cell_bound : ∀ (S : Set ℝ) (c : ℂ), μ S < ∞ → IntegrableOn f S μ →
      (∀ x ∈ S, ‖f x - c‖ ≤ ε) →
      ‖(∫ x in S, f x ∂μ) - (μ S).toReal • c‖ ≤ ε * (μ S).toReal := by
    intro S c hSfin hSint hSosc
    have hcint : IntegrableOn (fun _ : ℝ => c) S μ := by
      simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrableOn_const_iff, enorm_eq_zero];
      exact Or.symm (Or.intro_left (c = 0) hSfin)
    have h1 : (∫ x in S, (f x - c) ∂μ) = (∫ x in S, f x ∂μ) - ∫ _x in S, c ∂μ :=
      integral_sub hSint hcint
    have key : (∫ x in S, f x ∂μ) - (μ S).toReal • c = ∫ x in S, (f x - c) ∂μ := by
      rw [h1, setIntegral_const, MeasureTheory.measureReal_def]
    rw [key]
    have hb := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := S) (C := ε)
      (f := fun x => f x - c) hSfin (fun x hx => hSosc x hx)
    rwa [MeasureTheory.measureReal_def] at hb
  have hintIcc : IntegrableOn f (Set.Icc (t 0) (t 1)) μ :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hfinIcc : μ (Set.Icc (t 0) (t 1)) < ∞ := measure_Icc_lt_top
  rw [integral_Icc_split hf hmono hn]
  have hregroup :
      ((∫ x in Set.Icc (t 0) (t 1), f x ∂μ)
          + ∑ i ∈ Finset.Ico 1 n, ∫ x in Set.Ioc (t i) (t (i + 1)), f x ∂μ)
        - ((μ (Set.Icc (t 0) (t 1))).toReal • f (t 1)
            + ∑ i ∈ Finset.Ico 1 n,
                (μ (Set.Ioc (t i) (t (i + 1)))).toReal • f (t (i + 1)))
      = ((∫ x in Set.Icc (t 0) (t 1), f x ∂μ) - (μ (Set.Icc (t 0) (t 1))).toReal • f (t 1))
        + ∑ i ∈ Finset.Ico 1 n,
            ((∫ x in Set.Ioc (t i) (t (i + 1)), f x ∂μ)
              - (μ (Set.Ioc (t i) (t (i + 1)))).toReal • f (t (i + 1))) := by
    rw [Finset.sum_sub_distrib]; abel
  have hfinIoc : ∀ i, μ (Set.Ioc (t i) (t (i + 1))) < ∞ :=
    fun i => lt_of_le_of_lt (measure_mono Set.Ioc_subset_Icc_self) measure_Icc_lt_top
  have hintIoc : ∀ i, IntegrableOn f (Set.Ioc (t i) (t (i + 1))) μ :=
    fun i => (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hA : ‖(∫ x in Set.Icc (t 0) (t 1), f x ∂μ) - (μ (Set.Icc (t 0) (t 1))).toReal • f (t 1)‖
      ≤ ε * (μ (Set.Icc (t 0) (t 1))).toReal :=
    cell_bound _ _ hfinIcc hintIcc hosc1
  have hB : ‖∑ i ∈ Finset.Ico 1 n,
          ((∫ x in Set.Ioc (t i) (t (i + 1)), f x ∂μ)
            - (μ (Set.Ioc (t i) (t (i + 1)))).toReal • f (t (i + 1)))‖
      ≤ ∑ i ∈ Finset.Ico 1 n, ε * (μ (Set.Ioc (t i) (t (i + 1)))).toReal := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact cell_bound _ _ (hfinIoc i) (hintIoc i) (hoscI i hi.1 hi.2)
  rw [hregroup]
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add hA hB) (le_of_eq ?_))
  rw [mul_add, Finset.mul_sum]

/-- The Stieltjes function of a left-flat CDF has left limit `0` at `0`. -/
lemma stieltjes_leftLim_zero {F : ℝ → ℝ} (hF : Monotone F)
    (hzero : ∀ x ≤ (0 : ℝ), F x = 0) :
    Function.leftLim (hF.stieltjesFunction) 0 = 0 := by
  have hsf0 : ∀ y < (0 : ℝ), hF.stieltjesFunction y = 0 := by
    intro y hy
    rw [hF.stieltjesFunction_eq]
    have h1 : (0 : ℝ) ≤ Function.rightLim F y := by
      rw [← hzero y (le_of_lt hy)]; exact hF.le_rightLim (le_refl y)
    have h2 : Function.rightLim F y ≤ 0 := by
      have hr : Function.rightLim F y ≤ F (y / 2) := hF.rightLim_le (by linarith)
      rwa [hzero (y / 2) (by linarith)] at hr
    linarith
  have htend : Tendsto (hF.stieltjesFunction) (𝓝[<] (0 : ℝ)) (𝓝 0) := by
    have heq : (hF.stieltjesFunction : ℝ → ℝ) =ᶠ[𝓝[<] (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hy using hsf0 y hy
    rw [Filter.tendsto_congr' heq]; exact tendsto_const_nhds
  exact tendsto_nhds_unique (hF.stieltjesFunction.mono.tendsto_leftLim 0) htend

/-- The Stieltjes function of a CDF that is eventually constant `M` to the right of `a`
has right limit `M` at `a`. -/
lemma stieltjes_rightLim_const {F : ℝ → ℝ} (hF : Monotone F) {a M : ℝ}
    (hconst : ∀ x, a < x → F x = M) :          -- was  a ≤ x
    Function.rightLim F a = M := by
  have htend : Tendsto F (𝓝[>] a) (𝓝 M) := by
    have heq : F =ᶠ[𝓝[>] a] (fun _ => M) := by
      filter_upwards [self_mem_nhdsWithin] with y hy using hconst y hy   -- was  (le_of_lt hy)
    rw [Filter.tendsto_congr' heq]; exact tendsto_const_nhds
  exact tendsto_nhds_unique (hF.tendsto_rightLim a) htend

/-- Mass of a half-open cell as a difference of right limits. -/
private lemma stieltjes_mass_Ioc {F : ℝ → ℝ} (hF : Monotone F) {a b : ℝ} (hab : a ≤ b) :
    (hF.stieltjesFunction.measure (Set.Ioc a b)).toReal
      = Function.rightLim F b - Function.rightLim F a := by
  rw [StieltjesFunction.measure_Ioc, hF.stieltjesFunction_eq, hF.stieltjesFunction_eq,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (hF.rightLim hab))]

/-- Mass of the closed first cell `[0, c]` as a right limit (uses left-flatness at `0`). -/
private lemma stieltjes_mass_Icc0 {F : ℝ → ℝ} (hF : Monotone F)
    (hzero : ∀ x ≤ (0 : ℝ), F x = 0) {c : ℝ} (hc : 0 ≤ c) :
    (hF.stieltjesFunction.measure (Set.Icc 0 c)).toReal = Function.rightLim F c := by
  have hnn : (0 : ℝ) ≤ Function.rightLim F c := by
    have h1 : F 0 ≤ Function.rightLim F c := le_trans (hF hc) (hF.le_rightLim (le_refl c))
    rwa [hzero 0 (le_refl 0)] at h1
  rw [StieltjesFunction.measure_Icc, stieltjes_leftLim_zero hF hzero, sub_zero,
      hF.stieltjesFunction_eq, ENNReal.toReal_ofReal hnn]

/-- **The squeeze (analytic heart of the as-is version).** At a continuity point `x` of the
limit `G`, the *right limits* of the approximating CDFs converge to `G x` — recovering the
value-convergence we'd otherwise get for free under right-continuity. -/
private lemma rightLim_tendsto {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {φ : ℕ → ℕ}
    (h_mono_F : ∀ N, Monotone (F N))
    (hDense : Dense {x : ℝ | ContinuousAt G x})
    (h_conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)))
    {x : ℝ} (hx : ContinuousAt G x) :
    Tendsto (fun k => Function.rightLim (F (φ k)) x) atTop (𝓝 (G x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδ_prop⟩ := Metric.continuousAt_iff.mp hx (ε / 2) (by linarith)
  obtain ⟨p, hp_cont, hp_mem⟩ := hDense.exists_between (show x - δ < x by linarith)
  obtain ⟨q, hq_cont, hq_mem⟩ := hDense.exists_between (show x < x + δ by linarith)
  have hGp : dist (G p) (G x) < ε / 2 :=
    hδ_prop (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hp_mem.1], by linarith [hp_mem.2]⟩)
  have hGq : dist (G q) (G x) < ε / 2 :=
    hδ_prop (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hq_mem.1], by linarith [hq_mem.2]⟩)
  have hcp := Metric.tendsto_atTop.mp (h_conv p hp_cont) (ε / 2) (by linarith)
  have hcq := Metric.tendsto_atTop.mp (h_conv q hq_cont) (ε / 2) (by linarith)
  obtain ⟨Kp, hKp⟩ := hcp
  obtain ⟨Kq, hKq⟩ := hcq
  refine ⟨max Kp Kq, fun k hk => ?_⟩
  have ep := hKp k (le_of_max_le_left hk)
  have eq := hKq k (le_of_max_le_right hk)
  have hlow : F (φ k) p ≤ Function.rightLim (F (φ k)) x :=
    le_trans (h_mono_F (φ k) (le_of_lt hp_mem.2)) ((h_mono_F (φ k)).le_rightLim (le_refl x))
  have hupp : Function.rightLim (F (φ k)) x ≤ F (φ k) q :=
    (h_mono_F (φ k)).rightLim_le hq_mem.1
  rw [Real.dist_eq, abs_lt] at ep eq hGp hGq ⊢
  exact ⟨by linarith [hlow, ep.1, hGp.1], by linarith [hupp, eq.2, hGq.2]⟩

/-- **Portmanteau lemma for Stieltjes measures**: if `F_n → G` pointwise
at all continuity points of `G`, and `f` is bounded and continuous, then
`∫ f dF_n → ∫ f dG`. -/
lemma integral_tendsto_of_cdf_tendsto
    (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (φ : ℕ → ℕ)
    (h_mono_F : ∀ N, Monotone (F N)) (h_mono_G : Monotone G)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bnd : ∀ N x, F N x ∈ Set.Icc 0 M) (h_bnd_G : ∀ x, G x ∈ Set.Icc 0 M)
    (h_conv : ∀ x, ContinuousAt G x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)))
    (f : ℝ → ℂ) (hf_cont : Continuous f) (_hf_bnd : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (h_supp_F : ∀ N, F N 0 = 0 ∧ ∀ x, 2 * Real.pi < x → F N x = M)
    (h_supp_G : G 0 = 0 ∧ ∀ x, 2 * Real.pi < x → G x = M) :
    Tendsto (fun k => ∫ θ in Set.Icc 0 (2 * Real.pi), f θ
        ∂((h_mono_F (φ k)).stieltjesFunction.measure)) atTop
      (𝓝 (∫ θ in Set.Icc 0 (2 * Real.pi), f θ ∂(h_mono_G.stieltjesFunction.measure))) := by
  -- abbreviate the two integrals (folds them out of the goal)
  set IF : ℕ → ℂ := fun k => ∫ θ in Set.Icc 0 (2 * Real.pi), f θ
      ∂((h_mono_F (φ k)).stieltjesFunction.measure) with hIF_def
  set IG : ℂ := ∫ θ in Set.Icc 0 (2 * Real.pi), f θ
      ∂(h_mono_G.stieltjesFunction.measure) with hIG_def
  -- left-flatness / right-constancy of the CDFs
  have hFzero : ∀ k, ∀ x ≤ (0 : ℝ), F (φ k) x = 0 := by
    intro k x hx
    have hle : F (φ k) x ≤ F (φ k) 0 := h_mono_F (φ k) hx
    rw [(h_supp_F (φ k)).1] at hle
    linarith [(h_bnd (φ k) x).1]
  have hGzero : ∀ x ≤ (0 : ℝ), G x = 0 := by
    intro x hx
    have hle : G x ≤ G 0 := h_mono_G hx
    rw [h_supp_G.1] at hle
    linarith [(h_bnd_G x).1]
  -- continuity points of G are dense
  have hDense : Dense {x : ℝ | ContinuousAt G x} := by
    have h := (h_mono_G.countable_not_continuousAt).dense_compl ℝ
    have hset : {x : ℝ | ¬ ContinuousAt G x}ᶜ = {x : ℝ | ContinuousAt G x} := by
      ext x; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    rwa [hset] at h
  rw [Metric.tendsto_atTop]
  intro ε₀ hε₀
  -- the working tolerance
  have _hMp : (0 : ℝ) < M + 1 := by linarith
  set ε := ε₀ / (4 * (M + 1)) with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; exact div_pos hε₀ (by linarith)
  have hεM : ε * M ≤ ε₀ / 4 := by
    have _h1 : ε * M ≤ ε * (M + 1) := by nlinarith [hε_pos.le]
    have h2 : ε * (M + 1) ≤ ε₀ / 4 := by
      rw [hε_def, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      apply le_of_eq; ring
    linarith
  -- mesh from uniform continuity on the compact interval
  have huc : UniformContinuousOn f (Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf_cont.continuousOn
  obtain ⟨δ, hδ_pos, hδ_uc⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε_pos
  -- partition with continuity-point breakpoints
  obtain ⟨n, t, hn, h_t0, h_tn, hmono, hgap, hpart_cont⟩ := exists_cont_partition h_mono_G hδ_pos
  -- t is monotone on {0,…,n}, hence lands in [0,2π]
  have htmono : ∀ j, j ≤ n → ∀ i, i ≤ j → t i ≤ t j := by
    intro j
    induction j with
    | zero => intro _ i hi; obtain rfl := Nat.le_zero.mp hi; exact le_refl _
    | succ m ih =>
      intro hsm i hi
      have hmn : m < n := Nat.lt_of_succ_le hsm
      rcases eq_or_lt_of_le hi with heq | hlt
      · subst heq; exact le_refl _
      · exact le_trans (ih (le_of_lt hmn) i (Nat.lt_succ_iff.mp hlt)) (le_of_lt (hmono m hmn))
  have htmem : ∀ i, i ≤ n → t i ∈ Set.Icc 0 (2 * Real.pi) := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← h_t0]; exact htmono i hi 0 (Nat.zero_le i)
    · rw [← h_tn]; exact htmono n (le_refl n) i hi
  -- the key unification of value- and seam-convergence
  have rightLim_conv : ∀ j, 1 ≤ j → j ≤ n →
      Tendsto (fun k => Function.rightLim (F (φ k)) (t j)) atTop
        (𝓝 (Function.rightLim G (t j))) := by
    intro j hj1 hjn
    rcases hjn.lt_or_eq with hjlt | hjeq
    · have hcont : ContinuousAt G (t j) := hpart_cont j hj1 hjlt
      have hRG : Function.rightLim G (t j) = G (t j) := by
        rw [← h_mono_G.stieltjesFunction_eq];
        exact stieltjes_eq_at_continuousAt G h_mono_G (t j) (hpart_cont j hj1 hjlt)
      rw [hRG]
      exact rightLim_tendsto h_mono_F hDense h_conv hcont
    · rw [hjeq, h_tn, stieltjes_rightLim_const h_mono_G h_supp_G.2]
      have hconstF : ∀ k, Function.rightLim (F (φ k)) (2 * Real.pi) = M := fun k =>
        stieltjes_rightLim_const (h_mono_F (φ k)) (h_supp_F (φ k)).2
      simp_rw [hconstF]; exact tendsto_const_nhds
  -- each Riemann–Stieltjes "bracket" of total cell mass telescopes to M
  have bracket_eq : ∀ (V : ℝ → ℝ) (hV : Monotone V), (∀ x ≤ (0 : ℝ), V x = 0) →
      (∀ x, 2 * Real.pi < x → V x = M) →
      (hV.stieltjesFunction.measure (Set.Icc 0 (t 1))).toReal
        + ∑ i ∈ Finset.Ico 1 n,
            (hV.stieltjesFunction.measure (Set.Ioc (t i) (t (i + 1)))).toReal = M := by
    intro V hV hVz hVc
    have h01 := stieltjes_mass_Icc0 hV hVz (htmem 1 (by omega)).1
    have hsum : ∑ i ∈ Finset.Ico 1 n,
        (hV.stieltjesFunction.measure (Set.Ioc (t i) (t (i + 1)))).toReal
          = ∑ i ∈ Finset.Ico 1 n,
              (Function.rightLim V (t (i + 1)) - Function.rightLim V (t i)) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_Ico] at hi
      exact stieltjes_mass_Ioc hV (le_of_lt (hmono i hi.2))
    have htel := sum_Ico_telescope (fun i => Function.rightLim V (t i)) n hn
    have hVn : Function.rightLim V (t n) = M := by
      rw [h_tn];
      exact stieltjes_rightLim_const hV hVc
    rw [h01, hsum, htel, hVn]; ring
    -- name the two Riemann–Stieltjes sums
  set RSF : ℕ → ℂ := fun k =>
    (((h_mono_F (φ k)).stieltjesFunction.measure) (Set.Icc 0 (t 1))).toReal • f (t 1)
      + ∑ i ∈ Finset.Ico 1 n,
    (((h_mono_F (φ k)).stieltjesFunction.measure) (Set.Ioc (t i) (t (i + 1)))).toReal
      • f (t (i + 1)) with hRSF_def
  set RSG : ℂ :=
    (h_mono_G.stieltjesFunction.measure (Set.Icc 0 (t 1))).toReal • f (t 1)
      + ∑ i ∈ Finset.Ico 1 n,
    (h_mono_G.stieltjesFunction.measure (Set.Ioc (t i) (t (i + 1)))).toReal
      • f (t (i + 1)) with hRSG_def
  -- oscillation control on cells (width < δ, contained in [0,2π])
  have hosc1 : ∀ x ∈ Set.Icc (t 0) (t 1), ‖f x - f (t 1)‖ ≤ ε := by
    intro x hx
    rw [h_t0] at hx
    have hg0 : t 1 - t 0 < δ := by simpa using hgap 0 hn
    have hxmem : x ∈ Set.Icc 0 (2 * Real.pi) := ⟨hx.1, le_trans hx.2 (htmem 1 (by omega)).2⟩
    have hdist : dist x (t 1) < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1, h_t0], by linarith [hx.2, hδ_pos]⟩
    have := hδ_uc x hxmem (t 1) (htmem 1 (by omega)) hdist;
      rw [dist_eq_norm] at this; exact le_of_lt this
  have hoscI : ∀ i, 1 ≤ i → i < n →
    ∀ x ∈ Set.Ioc (t i) (t (i + 1)), ‖f x - f (t (i + 1))‖ ≤ ε := by
      intro i _ hin x hx
      have hti : t i ∈ Set.Icc 0 (2 * Real.pi) := htmem i (le_of_lt hin)
      have hti1 : t (i + 1) ∈ Set.Icc 0 (2 * Real.pi) := htmem (i + 1) (by omega)
      have hxmem : x ∈ Set.Icc 0 (2 * Real.pi) :=
      ⟨le_trans hti.1 (le_of_lt hx.1), le_trans hx.2 hti1.2⟩
      have hdist : dist x (t (i + 1)) < δ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [hx.1, hgap i hin], by linarith [hx.2, hδ_pos]⟩
      have := hδ_uc x hxmem (t (i + 1)) hti1 hdist
      rw [dist_eq_norm] at this; exact le_of_lt this
      -- mass convergences
  have ha : Tendsto (fun k => (((h_mono_F (φ k)).stieltjesFunction.measure)
    (Set.Icc 0 (t 1))).toReal) atTop
    (𝓝 ((h_mono_G.stieltjesFunction.measure (Set.Icc 0 (t 1))).toReal)) := by
    have hF1 : ∀ k, (((h_mono_F (φ k)).stieltjesFunction.measure) (Set.Icc 0 (t 1))).toReal
      = Function.rightLim (F (φ k)) (t 1) :=
    fun k => stieltjes_mass_Icc0 (h_mono_F (φ k)) (hFzero k) (htmem 1 (by omega)).1
    rw [stieltjes_mass_Icc0 h_mono_G hGzero (htmem 1 (by omega)).1]
    simp_rw [hF1]
    exact rightLim_conv 1 (le_refl 1) (by omega)
  have hb : ∀ i ∈ Finset.Ico 1 n,
    Tendsto (fun k => (((h_mono_F (φ k)).stieltjesFunction.measure)
    (Set.Ioc (t i) (t (i + 1)))).toReal) atTop
    (𝓝 ((h_mono_G.stieltjesFunction.measure (Set.Ioc (t i) (t (i + 1)))).toReal)) := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
      have hFi : ∀ k, (((h_mono_F (φ k)).stieltjesFunction.measure)
        (Set.Ioc (t i) (t (i + 1)))).toReal
        = Function.rightLim (F (φ k)) (t (i + 1)) - Function.rightLim (F (φ k)) (t i) :=
        fun k => stieltjes_mass_Ioc (h_mono_F (φ k)) (le_of_lt (hmono i hi2))
      rw [stieltjes_mass_Ioc h_mono_G (le_of_lt (hmono i hi2))]
      simp_rw [hFi]
      exact (rightLim_conv (i + 1) (by omega) (by omega)).sub (rightLim_conv i hi1 (le_of_lt hi2))
  have hRS : Tendsto RSF atTop (𝓝 RSG) := by
    simp only [hRSF_def, hRSG_def]
    refine Tendsto.add (ha.smul_const (f (t 1))) ?_
    exact tendsto_finsetSum _ (fun i hi => (hb i hi).smul_const (f (t (i + 1))))
  -- approximation bounds
  have hbound_F : ∀ k, ‖IF k - RSF k‖ ≤ ε * M := by
    intro k
    simp only [hIF_def, hRSF_def]
    have hab := approx_bound (μ := (h_mono_F (φ k)).stieltjesFunction.measure)
      hf_cont hmono hn hosc1 hoscI
    rw [h_t0, h_tn, bracket_eq (F (φ k)) (h_mono_F (φ k)) (hFzero k) (h_supp_F (φ k)).2] at hab
    exact hab
  have hbound_G : ‖IG - RSG‖ ≤ ε * M := by
    simp only [hIG_def, hRSG_def]
    have hab := approx_bound (μ := h_mono_G.stieltjesFunction.measure)
      hf_cont hmono hn hosc1 hoscI
    rw [h_t0, h_tn, bracket_eq G h_mono_G hGzero h_supp_G.2] at hab
    exact hab
  -- combine 3ε
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hRS (ε₀ / 2) (by linarith)
  refine ⟨K, fun k hk => ?_⟩
  have h2 : ‖RSF k - RSG‖ < ε₀ / 2 := by have := hK k hk; rwa [dist_eq_norm] at this
  have h3 : ‖RSG - IG‖ ≤ ε * M := by rw [norm_sub_rev]; exact hbound_G
  have he : IF k - IG = (IF k - RSF k) + ((RSF k - RSG) + (RSG - IG)) := by ring
  rw [dist_eq_norm, he]
  have ht1 := norm_add_le (IF k - RSF k) ((RSF k - RSG) + (RSG - IG))
  have ht2 := norm_add_le (RSF k - RSG) (RSG - IG)
  linarith [hbound_F k, h2, h3, hεM, ht1, ht2]

/-- Specialization: convergence of Fourier integrals.
`∫ e^{inθ} dF_{N_k} → ∫ e^{inθ} dG` as `k → ∞`. -/
lemma fourier_integral_tendsto_of_cdf_tendsto
    (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (φ : ℕ → ℕ)
    (h_mono_F : ∀ N, Monotone (F N))
    (h_mono_G : Monotone G)
    (M : ℝ) (hM : 0 ≤ M)
    (h_bnd : ∀ N x, F N x ∈ Set.Icc 0 M)
    (h_bnd_G : ∀ x, G x ∈ Set.Icc 0 M)
    (h_conv : ∀ x, ContinuousAt G x →
      Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)))
    (h_supp_F : ∀ N, F N 0 = 0 ∧ ∀ x, 2 * Real.pi < x → F N x = M)
    (h_supp_G : G 0 = 0 ∧ ∀ x, 2 * Real.pi < x → G x = M)
    (n : ℤ) :
    Tendsto
      (fun k => ∫ θ in Set.Icc 0 (2 * Real.pi),
        exp (I * n * θ) ∂((h_mono_F (φ k)).stieltjesFunction.measure))
      atTop
      (𝓝 (∫ θ in Set.Icc 0 (2 * Real.pi),
        exp (I * n * θ) ∂(h_mono_G.stieltjesFunction.measure))) :=
  integral_tendsto_of_cdf_tendsto F G φ h_mono_F h_mono_G M hM h_bnd h_bnd_G
    h_conv (fun θ => exp (I * n * θ))
    (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal))
    ⟨1, fun x => by rw [norm_exp]; simp [Complex.mul_re, Complex.I_re, Complex.I_im]⟩
    h_supp_F h_supp_G

/-- Given a countable "bad" set `S ⊆ ℝ` and endpoints `a < b` both outside `S`,
there is a partition `a = t 0 < t 1 < ⋯ < t n = b` with all `t i ∉ S` and all
gaps strictly below a prescribed `δ > 0`.

The proof picks a lattice with spacing `h = L/K` where `K` is chosen so that
`3h/2 < δ`, then perturbs each interior lattice point within a window of width
`h/2` to land outside `S` (possible since `Sᶜ` is dense in ℝ). A uniform
"lattice offset" bound `|t i - (a + i·h)| ≤ h/4` then handles both strict
monotonicity (`t(i+1) - t i ≥ h/2 > 0`) and the gap bound
(`t(i+1) - t i ≤ 3h/2 < δ`) without case-analysis at the endpoints. -/
lemma exists_partition_avoiding_countable {S : Set ℝ} (hS : S.Countable)
    {a b : ℝ} (hab : a < b) (ha : a ∉ S) (hb : b ∉ S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (t : ℕ → ℝ), 0 < n ∧ t 0 = a ∧ t n = b ∧
      (∀ i < n, t i < t (i + 1)) ∧
      (∀ i < n, t (i + 1) - t i < δ) ∧
      (∀ i ≤ n, t i ∉ S) := by
  classical
  set L : ℝ := b - a with hL_def
  have hL_pos : 0 < L := sub_pos.mpr hab
  -- Choose K ∈ ℕ⁺ so that h := L/K satisfies 3h/2 < δ.
  set K : ℕ := ⌈3 * L / δ⌉₊ + 1 with hK_def
  have hKpos : 0 < K := Nat.succ_pos _
  have hKR : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hKpos
  set h : ℝ := L / (K : ℝ) with hh_def
  have hh_pos : 0 < h := div_pos hL_pos hKR
  have hKh : (K : ℝ) * h = L := by rw [hh_def]; field_simp
  have _hKh_b : a + (K : ℝ) * h = b := by rw [hKh, hL_def]; ring
  have hmesh : 3 * h / 2 < δ := by
    have hKbig : (3 * L / δ : ℝ) < (K : ℝ) := by
      have h1 : (3 * L / δ : ℝ) ≤ (⌈3 * L / δ⌉₊ : ℕ) := Nat.le_ceil _
      have h2 : ((⌈3 * L / δ⌉₊ : ℕ) : ℝ) < (K : ℝ) := by
        rw [hK_def]; push_cast; linarith
      linarith
    have hKδ : 3 * L < (K : ℝ) * δ := (div_lt_iff₀ hδ).mp hKbig
    have h2K_pos : (0 : ℝ) < 2 * (K : ℝ) := by linarith
    rw [show (3 * h / 2 : ℝ) = 3 * L / (2 * (K : ℝ)) from by rw [hh_def]; ring,
        div_lt_iff₀ h2K_pos]
    nlinarith
  -- `Sᶜ` is dense in `ℝ`.
  have hDense : Dense (Sᶜ : Set ℝ) := hS.dense_compl ℝ
  -- Pick a point `c j ∉ S` inside the window of width `h/2` around `a + j·h`.
  have hwin : ∀ j : ℕ, ∃ z, z ∉ S ∧
      z ∈ Set.Ioo (a + (j : ℝ) * h - h / 4) (a + (j : ℝ) * h + h / 4) := by
    intro j
    have hlt : a + (j : ℝ) * h - h / 4 < a + (j : ℝ) * h + h / 4 := by linarith
    exact hDense.exists_between hlt
  choose c hcS hcMem using hwin
  have hcL : ∀ j, a + (j : ℕ) * h - h / 4 < c j := fun j => (hcMem j).1
  have hcU : ∀ j, c j < a + (j : ℝ) * h + h / 4 := fun j => (hcMem j).2
  -- Piecewise partition: pin endpoints, use `c i` in the interior.
  set t : ℕ → ℝ :=
    (fun i => if i = 0 then a else if K ≤ i then b else c i) with ht_def
  have tval : ∀ i, t i = if i = 0 then a else if K ≤ i then b else c i :=
    fun i => by simp only [ht_def]
  have t0 : t 0 = a := by rw [tval 0]; exact if_pos rfl
  have tK : t K = b := by
    rw [tval K, if_neg hKpos.ne', if_pos (le_refl K)]
  have tmid : ∀ i, i ≠ 0 → i < K → t i = c i := fun i h0 hiK => by
    rw [tval i, if_neg h0, if_neg (not_le.mpr hiK)]
  -- The key uniform bound: every `t i` is within `h/4` of the lattice point.
  have h_offset : ∀ i, i ≤ K → |t i - (a + (i : ℝ) * h)| ≤ h / 4 := by
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [t0]
      simp only [Nat.cast_zero, zero_mul, add_zero, sub_self, abs_zero]
      linarith
    · by_cases hiK : K ≤ i
      · have hieq : i = K := le_antisymm hi hiK
        subst hieq
        rw [tK, show b - (a + (K : ℝ) * h) = 0 from by linarith, abs_zero]
        linarith
      · push Not at hiK
        rw [tmid i hi0 hiK, abs_le]
        exact ⟨by linarith [hcL i], by linarith [hcU i]⟩
  refine ⟨K, t, hKpos, t0, tK, ?_, ?_, ?_⟩
  -- Strict monotonicity.
  · intro i hi
    have ho1 := abs_le.mp (h_offset i hi.le)
    have ho2 := abs_le.mp (h_offset (i + 1) hi)
    push_cast at ho2
    have hexp : ((i : ℝ) + 1) * h = (i : ℝ) * h + h := by ring
    linarith [ho1.1, ho1.2, ho2.1, ho2.2, hh_pos, hexp]
  -- Gap bound.
  · intro i hi
    have ho1 := abs_le.mp (h_offset i hi.le)
    have ho2 := abs_le.mp (h_offset (i + 1) hi)
    push_cast at ho2
    have hexp : ((i : ℝ) + 1) * h = (i : ℝ) * h + h := by ring
    linarith [ho1.1, ho1.2, ho2.1, ho2.2, hmesh, hexp]
  -- All `t i` lie outside `S`.
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0; rw [t0]; exact ha
    · by_cases hiK : K ≤ i
      · have hieq : i = K := le_antisymm hi hiK
        subst hieq; rw [tK]; exact hb
      · push Not at hiK
        rw [tmid i hi0 hiK]
        exact hcS i

end IntegralConvergence

end Spectra.Herglotz

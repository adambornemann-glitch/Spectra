/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.IntegralOperator
import Spectra.SpectralTheory.RectangleSimple

/-!
# Integral operators with an `L²` kernel are compact

This file closes the **A3 gate** of the hydrogen continuous-spectrum program: *every* integral
operator `T_K f(x) = ∫ K(x,y) f(y) dy` with kernel `K ∈ L²(μ × ν)` is a compact operator
`L²(ν) →L[ℂ] L²(μ)`. Mathlib has no Hilbert–Schmidt / kernel-operator API, so we assemble it from:

* `Spectra.SpectralTheory.IntegralOperator` — the analytic core: `T_K` as a CLM with
  `‖T_K‖ ≤ ‖K‖`, the continuous dependence `integralOperatorCLM : K ↦ T_K`, and the rank-one
  fact `isCompactOperator_integralOperator_indicatorRect` (a single rectangle indicator gives a
  finite-rank, hence compact, operator).
* `Spectra.SpectralTheory.RectangleSimple` — the density input `rectSimple_dense`: finite
  ℂ-combinations of finite-measure rectangle indicators are dense in `L²(μ × ν)`.

The assembly is two steps:

1. `isCompactOperator_of_isRectSimple` — a rect-simple kernel gives a finite sum of rank-one
   operators, hence compact (K-linearity of `T_K` + closure of compacts under finite sums).
2. `isCompactOperator_integralOperator` — **the headline**: approximate an arbitrary `K` in
   `L²`-norm by rect-simple kernels (density), and use that the compact operators are closed
   (`isCompactOperator_of_tendsto`, via continuity of `K ↦ T_K`).
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace Spectra.CompactOperator

/-- A finite sum of compact operators is compact. -/
theorem isCompactOperator_finset_sum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (s : Finset ι) (T : ι → (E →L[ℂ] F))
    (h : ∀ i ∈ s, IsCompactOperator (T i)) : IsCompactOperator (⇑(∑ i ∈ s, T i)) := by
  classical
  rw [ContinuousLinearMap.coe_sum']
  induction s using Finset.induction with
  | empty => simpa using isCompactOperator_zero
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a t)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] [SigmaFinite ν] in
/-- Coercion commutes with finite `Lp` sums (a.e.). -/
theorem coeFn_lpSum {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 (μ.prod ν)) :
    (⇑(∑ i ∈ s, f i) : α × β → ℂ) =ᵐ[μ.prod ν] ∑ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℂ 2 (μ.prod ν)
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ t, f i), ih] with x h1 h2
      simp only [h1, Pi.add_apply, h2]

/-- **A rect-simple kernel yields a compact (finite-rank) operator.** -/
theorem isCompactOperator_of_isRectSimple {g : α × β → ℂ} (hrect : IsRectSimple μ ν g)
    (hg : MemLp g 2 (μ.prod ν)) : IsCompactOperator (integralOperator (hg.toLp g)) := by
  classical
  obtain ⟨s, A, B, c, hA, hB, hμA, hνB, rfl⟩ := hrect
  -- each rectangle has finite product measure
  have hAB : ∀ i, (μ.prod ν) (A i ×ˢ B i) ≠ ⊤ := fun i => by
    rw [Measure.prod_prod]; exact ENNReal.mul_ne_top (hμA i) (hνB i)
  -- the building-block kernels: rectangle indicators in `L²`
  set K : ℕ → Lp ℂ 2 (μ.prod ν) :=
    fun i => indicatorConstLp 2 ((hA i).prod (hB i)) (hAB i) (1 : ℂ) with hK
  have hKcoe : ∀ i, (⇑(K i) : α × β → ℂ) =ᵐ[μ.prod ν]
      (A i ×ˢ B i).indicator (fun _ => (1 : ℂ)) := by
    intro i; simp only [hK]; exact indicatorConstLp_coeFn
  -- the `Lp` element `toLp g` decomposes as a finite ℂ-combination of the `K i`
  have hdecomp : hg.toLp _ = ∑ i ∈ s, c i • K i := by
    apply Lp.ext
    refine (MemLp.coeFn_toLp hg).trans ?_
    refine EventuallyEq.symm ((coeFn_lpSum s (fun i => c i • K i)).trans ?_)
    have hper : ∀ i ∈ s, (⇑(c i • K i) : α × β → ℂ) =ᵐ[μ.prod ν]
        fun p => c i * (A i ×ˢ B i).indicator (fun _ => (1 : ℂ)) p := by
      intro i _
      filter_upwards [Lp.coeFn_smul (c i) (K i), hKcoe i] with p hsm hind
      simp only [hsm, Pi.smul_apply, hind, smul_eq_mul]
    filter_upwards [(eventually_all_finset s).2 hper] with p hp
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i hi => hp i hi
  rw [hdecomp]
  -- push `integralOperator` through the finite sum by K-linearity
  have hpush : integralOperator (∑ i ∈ s, c i • K i) = ∑ i ∈ s, c i • integralOperator (K i) := by
    rw [← integralOperatorCLM_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, integralOperatorCLM_apply]
  rw [hpush]
  -- each summand is a scalar multiple of a rank-one (hence compact) operator
  apply isCompactOperator_finset_sum s (fun i => c i • integralOperator (K i))
  intro i _
  simpa using
    (isCompactOperator_integralOperator_indicatorRect (hA i) (hB i) (hμA i) (hνB i) (hAB i)).smul
      (c i)

/-- **Every `L²(μ × ν)` kernel gives a compact integral operator.**

The compactness gate for the hydrogen continuous spectrum: rect-simple kernels are dense in
`L²` (`rectSimple_dense`) and give compact operators (`isCompactOperator_of_isRectSimple`), and the
compact operators are closed under the operator-norm limit (`isCompactOperator_of_tendsto`, using
that `K ↦ T_K` is continuous with `‖T_K‖ ≤ ‖K‖`). -/
theorem isCompactOperator_integralOperator (K : Lp ℂ 2 (μ.prod ν)) :
    IsCompactOperator (integralOperator K) := by
  -- a rect-simple `1/(n+1)`-approximant of `K`, with the operator it induces compact
  have key : ∀ n : ℕ, ∃ g : α × β → ℂ, ∃ hg : MemLp g 2 (μ.prod ν),
      IsCompactOperator (integralOperator (hg.toLp g)) ∧
        ‖K - hg.toLp g‖ ≤ (1 / (n + 1) : ℝ) := by
    intro n
    obtain ⟨g, hclose, hrect⟩ := rectSimple_dense (Lp.memLp K)
      (ε := ENNReal.ofReal (1 / (n + 1)))
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    -- `g` is in `L²` since it is `K` minus an `L²` error
    have hKg : MemLp ((⇑K : α × β → ℂ) - g) 2 (μ.prod ν) :=
      ⟨(Lp.aestronglyMeasurable K).sub hrect.aestronglyMeasurable,
        lt_of_le_of_lt hclose ENNReal.ofReal_lt_top⟩
    have hgmem : MemLp g 2 (μ.prod ν) := by
      have h := (Lp.memLp K).sub hKg
      rwa [sub_sub_cancel] at h
    refine ⟨g, hgmem, isCompactOperator_of_isRectSimple hrect hgmem, ?_⟩
    -- transfer the `L²`-distance bound through `toLp`
    rw [Lp.norm_def]
    have hcoe : (⇑(K - hgmem.toLp g) : α × β → ℂ) =ᵐ[μ.prod ν] (⇑K : α × β → ℂ) - g := by
      filter_upwards [Lp.coeFn_sub K (hgmem.toLp g), MemLp.coeFn_toLp hgmem] with p h1 h2
      simp only [h1, Pi.sub_apply, h2]
    rw [eLpNorm_congr_ae hcoe]
    calc (eLpNorm ((⇑K : α × β → ℂ) - g) 2 (μ.prod ν)).toReal
        ≤ (ENNReal.ofReal (1 / (n + 1))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hclose
      _ = 1 / (n + 1) := ENNReal.toReal_ofReal (by positivity)
  choose g hgmem hcompact hnorm using key
  -- the approximating sequence of compact operators
  set T : ℕ → (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ) := fun n => integralOperator ((hgmem n).toLp (g n)) with hT
  -- `T n → integralOperator K` in operator norm
  have htend : Tendsto T atTop (𝓝 (integralOperator K)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    -- `‖T n − T_K‖ = ‖T_{toLp gₙ − K}‖ ≤ ‖toLp gₙ − K‖ = ‖K − toLp gₙ‖ ≤ 1/(n+1)`
    have hlin : T n - integralOperator K = integralOperator ((hgmem n).toLp (g n) - K) := by
      rw [hT]
      simp only [← integralOperatorCLM_apply, ← map_sub]
    rw [hlin]
    refine (norm_integralOperator_le _).trans ?_
    rw [norm_sub_rev]
    exact hnorm n
  exact isCompactOperator_of_tendsto htend (Eventually.of_forall hcompact)

end Kernel

end Spectra.CompactOperator

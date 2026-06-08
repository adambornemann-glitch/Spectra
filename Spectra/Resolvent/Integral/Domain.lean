/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Resolvent/Integral/Domain.lean
-/
import Spectra.Resolvent.Integral.Limits.PLus
import Spectra.Resolvent.Integral.Limits.Minus
import Mathlib.Probability.Distributions.Gaussian.Real
/-!
# Generator Domain and Self-Adjointness

This file constructs the generator of a strongly continuous one-parameter unitary
group and proves it is self-adjoint.


## Implementation notes

Self-adjointness is proved using the criterion: `A` is self-adjoint iff `A` is
symmetric and `ran(A ± iI) = H`. This avoids dealing with the adjoint of an
unbounded operator directly.

Domain density uses averaged vectors: `h⁻¹ ∫₀ʰ U(t)φ dt → φ` as `h → 0`,
and these averaged vectors lie in the domain.

## Tags

generator, self-adjoint, domain, Stone's lemma
-/
open InnerProductSpace MeasureTheory Complex Filter Topology
open Spectra.QuantumMechanics OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))
namespace Spectra.Resolvent

lemma range_plus_i_eq_top :
    ∀ φ : H, ∃ ψ : (generator U_grp).domain,
      generator U_grp ψ + I • (ψ : H) = φ := by
  intro φ
  -- the difference quotient of `resolventIntegralPlus φ` converges to `φ - I • (·)`
  have hlim := generator_limit_resolventIntegralPlus U_grp φ
  -- so that vector lies in the domain ...
  have hmem : resolventIntegralPlus U_grp φ ∈ (generator U_grp).domain := ⟨_, hlim⟩
  -- ... and the generator's value there is that same limit, by uniqueness of limits
  have hval : generator U_grp ⟨resolventIntegralPlus U_grp φ, hmem⟩
            = φ - I • resolventIntegralPlus U_grp φ :=
    tendsto_nhds_unique (generator_tendsto U_grp ⟨resolventIntegralPlus U_grp φ, hmem⟩) hlim
  refine ⟨⟨resolventIntegralPlus U_grp φ, hmem⟩, ?_⟩
  show generator U_grp ⟨resolventIntegralPlus U_grp φ, hmem⟩
        + I • resolventIntegralPlus U_grp φ = φ
  rw [hval]; abel

lemma range_minus_i_eq_top :
    ∀ φ : H, ∃ ψ : (generator U_grp).domain,
      generator U_grp ψ - I • (ψ : H) = φ := by
  intro φ
  have hlim := generator_limit_resolventIntegralMinus U_grp φ
  have hmem : resolventIntegralMinus U_grp φ ∈ (generator U_grp).domain := ⟨_, hlim⟩
  have hval : generator U_grp ⟨resolventIntegralMinus U_grp φ, hmem⟩
            = φ + I • resolventIntegralMinus U_grp φ :=
    tendsto_nhds_unique (generator_tendsto U_grp ⟨resolventIntegralMinus U_grp φ, hmem⟩) hlim
  refine ⟨⟨resolventIntegralMinus U_grp φ, hmem⟩, ?_⟩
  show generator U_grp ⟨resolventIntegralMinus U_grp φ, hmem⟩
        - I • resolventIntegralMinus U_grp φ = φ
  rw [hval]; abel

/-- Time-averaged vector: `h⁻¹ ∫₀ʰ U(t)φ dt`. These lie in the generator domain
    and converge to `φ` as `h → 0`, proving domain density. -/
noncomputable def averagedVector (h : ℝ) (_ : h ≠ 0) (φ : H) : H :=
  (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, U_grp.U t φ

lemma averagedVector_tendsto (φ : H) :
    Tendsto (fun h : ℝ => if hh : h ≠ 0 then averagedVector U_grp h hh φ else φ)
            (𝓝[>] 0) (𝓝 φ) := by
  unfold averagedVector
  have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_f0 : U_grp.U 0 φ = φ := by rw [U_grp.identity]; rfl
  have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, U_grp.U t φ) (U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, U_grp.U t φ = 0 := intervalIntegral.integral_same
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, U_grp.U t φ)
                                (𝓝[≠] 0) (𝓝 φ) := by
    have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
    rw [hasDerivWithinAt_iff_tendsto_slope] at this
    simp only [Set.diff_diff, Set.union_self] at this
    convert this using 1
    · ext h
      unfold slope
      simp only [sub_zero, h_F0, vsub_eq_sub]
    · congr 1
      exact Set.compl_eq_univ_diff {(0 : ℝ)}
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [dif_pos (ne_of_gt hh)]
  rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  rw [(Complex.coe_smul h⁻¹ _).symm, ofReal_inv]

lemma averagedVector_orbit_shift_integral (s h : ℝ) (φ : H) :
    U_grp.U s (∫ t in Set.Ioc 0 h, U_grp.U t φ) = ∫ t in Set.Ioc s (s + h), U_grp.U t φ := by
  have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_shift_int : U_grp.U s (∫ t in Set.Ioc 0 h, U_grp.U t φ) =
                         ∫ t in Set.Ioc s (s + h), U_grp.U t φ := by
    rw [← (U_grp.U s).integral_comp_comm h_cont.integrableOn_Ioc]
    have h_subst : ∫ t in Set.Ioc 0 h, U_grp.U s (U_grp.U t φ) =
                    ∫ t in Set.Ioc 0 h, U_grp.U (s + t) φ := by
      congr 1; ext t
      rw [@OneParameterUnitaryGroup.group_law]
      rfl
    rw [h_subst]
    have h_preimage : (fun t => t - s) ⁻¹' (Set.Ioc 0 h) = Set.Ioc s (s + h) := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ioc]; constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
    have h_meas : Measure.map (fun t => t - s) volume = volume :=
      (measurePreserving_sub_right volume s).map_eq
    rw [← h_meas, MeasureTheory.setIntegral_map measurableSet_Ioc]
    simp only [h_preimage]; congr 1
    · exact
        Measure.ext_iff'.mpr
          (congrFun
            (congrArg DFunLike.coe
              (congrFun (congrArg Measure.restrict (id (Eq.symm h_meas))) (Set.Ioc s (s + h)))))
    simp only [add_sub_cancel]
    · exact h_cont.aestronglyMeasurable.comp_measurable (measurable_const_add s)
    · exact (measurable_sub_const s).aemeasurable
  exact h_shift_int

lemma integral_orbit_shift_arith (s h : ℝ) (φ : H) :
    (∫ t in s..(s + h), U_grp.U t φ) - ∫ t in (0:ℝ)..h, U_grp.U t φ
      = (∫ t in (h:ℝ)..(h + s), U_grp.U t φ) - ∫ t in (0:ℝ)..s, U_grp.U t φ := by
  have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_arith : (∫ t in s..(s + h), U_grp.U t φ) - ∫ t in (0 : ℝ)..h, U_grp.U t φ =
            (∫ t in (h : ℝ)..(h + s), U_grp.U t φ) - ∫ t in (0 : ℝ)..s, U_grp.U t φ := by
    have hint : ∀ a b : ℝ, IntervalIntegrable (fun t => U_grp.U t φ) volume a b :=
      fun a b => h_cont.intervalIntegrable a b
    have h3 : s + h = h + s := add_comm s h
    have key : (∫ t in s..(s + h), U_grp.U t φ) + ∫ t in (0 : ℝ)..s, U_grp.U t φ =
              (∫ t in h..(h + s), U_grp.U t φ) + ∫ t in (0 : ℝ)..h, U_grp.U t φ := by
      have eq1 := intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + h))
      have eq2 := intervalIntegral.integral_add_adjacent_intervals (hint 0 h) (hint h (h + s))
      calc (∫ t in s..(s + h), U_grp.U t φ) + ∫ t in (0 : ℝ)..s, U_grp.U t φ
          = (∫ t in (0 : ℝ)..s, U_grp.U t φ) + ∫ t in s..(s + h), U_grp.U t φ := by abel
        _ = ∫ t in (0 : ℝ)..(s + h), U_grp.U t φ := eq1
        _ = ∫ t in (0 : ℝ)..(h + s), U_grp.U t φ := by rw [h3]
        _ = (∫ t in (0 : ℝ)..h, U_grp.U t φ) + ∫ t in h..(h + s), U_grp.U t φ := eq2.symm
        _ = (∫ t in h..(h + s), U_grp.U t φ) + ∫ t in (0 : ℝ)..h, U_grp.U t φ := by abel
    have h_sub : ∀ a b c d : H, a + b = c + d → a - d = c - b := by
      intros a b c d heq
      have h1 : a = c + d - b := by rw [← heq]; abel
      rw [h1]; abel
    exact h_sub _ _ _ _ key
  exact h_arith

lemma averagedVector_quotient_tendsto_zero (φ : H) :
    Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (0:ℝ)..s, U_grp.U t φ) (𝓝[≠] 0) (𝓝 φ) := by
  have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_FTC1 : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (0 : ℝ)..s, U_grp.U t φ) (𝓝[≠] 0) (𝓝 φ) := by
    have h_deriv : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, U_grp.U t φ) φ 0 := by
      have := intervalIntegral.integral_hasDerivAt_right (h_cont.intervalIntegrable 0 0)
                (h_cont.stronglyMeasurableAtFilter volume (𝓝 0)) h_cont.continuousAt
      simp only [U_grp.identity, ContinuousLinearMap.id_apply] at this
      exact this
    have h_F0 : ∫ t in (0 : ℝ)..0, U_grp.U t φ = 0 := intervalIntegral.integral_same
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    apply h_deriv.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    unfold slope
    simp only [vsub_eq_sub, sub_zero, h_F0, sub_zero]
    rw [(Complex.coe_smul s⁻¹ _).symm, ofReal_inv]
  exact h_FTC1

lemma averagedVector_quotient_tendsto_at (h : ℝ) (φ : H) :
    Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (h:ℝ)..(h + s), U_grp.U t φ)
      (𝓝[≠] 0) (𝓝 (U_grp.U h φ)) := by
  have h_cont : Continuous (fun t => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_FTC2 : Tendsto (fun s : ℝ => (s⁻¹ : ℂ) • ∫ t in (h : ℝ)..(h + s), U_grp.U t φ) (𝓝[≠] 0) (𝓝 (U_grp.U h φ)) := by
    have h_deriv : HasDerivAt (fun x => ∫ t in (h : ℝ)..x, U_grp.U t φ) (U_grp.U h φ) h := by
      exact intervalIntegral.integral_hasDerivAt_right (h_cont.intervalIntegrable h h)
              (h_cont.stronglyMeasurableAtFilter volume (𝓝 h)) h_cont.continuousAt
    have h_Fh : ∫ t in (h : ℝ)..h, U_grp.U t φ = 0 := intervalIntegral.integral_same
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    have h_shift : Tendsto (fun s : ℝ => h + s) (𝓝[≠] 0) (𝓝[≠] h) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun s : ℝ => h + s) (𝓝 0) (𝓝 h) := by
          have h1 : Tendsto (fun _ : ℝ => h) (𝓝 0) (𝓝 h) := tendsto_const_nhds
          have h2 : Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0) := tendsto_id
          convert h1.add h2 using 1
          simp only [add_zero]
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left]
        exact hs
    have := h_deriv.comp h_shift
    apply this.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    unfold slope
    simp only [vsub_eq_sub, h_Fh, sub_zero, Function.comp_apply, add_sub_cancel_left]
    rw [(Complex.coe_smul s⁻¹ _).symm, ofReal_inv]
  exact h_FTC2

lemma averagedVector_difference_quotient
    (h : ℝ) (hh : h ≠ 0) (hpos : 0 < h) (φ : H) (s : ℝ) (_hs : s ≠ 0) :
    ((I * s)⁻¹ : ℂ) • (U_grp.U s (averagedVector U_grp h hh φ) - averagedVector U_grp h hh φ)
      = ((I * h)⁻¹ : ℂ) • (((s⁻¹ : ℂ) • ∫ t in (h:ℝ)..(h + s), U_grp.U t φ)
                          - ((s⁻¹ : ℂ) • ∫ t in (0:ℝ)..s, U_grp.U t φ)) := by
  unfold averagedVector
  rw [ContinuousLinearMap.map_smul]
  rw [averagedVector_orbit_shift_integral U_grp s h φ]
  rw [← smul_sub, smul_smul]
  have h_Ioc_eq_interval : ∀ a b : ℝ, a ≤ b →
      ∫ t in Set.Ioc a b, U_grp.U t φ = ∫ t in a..b, U_grp.U t φ :=
    fun a b a_1 => Eq.symm (intervalIntegral.integral_of_le a_1)
  rw [h_Ioc_eq_interval s (s + h) (by linarith), h_Ioc_eq_interval 0 h (le_of_lt hpos)]
  rw [integral_orbit_shift_arith U_grp s h φ]
  have h_scalar : ((I * s)⁻¹ : ℂ) * (h⁻¹ : ℂ) = ((I * h)⁻¹ : ℂ) * (s⁻¹ : ℂ) := by field_simp
  rw [h_scalar, ← smul_smul, smul_sub]


lemma averagedVector_in_domain (h : ℝ) (hh : h ≠ 0) (φ : H) :
    averagedVector U_grp h hh φ ∈ generatorDomain U_grp := by
  by_cases hpos : 0 < h
  · refine ⟨((I * h)⁻¹ : ℂ) • (U_grp.U h φ - φ), ?_⟩
    apply Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (averagedVector_difference_quotient U_grp h hh hpos φ s hs).symm
    · exact Tendsto.smul tendsto_const_nhds
        ((averagedVector_quotient_tendsto_at U_grp h φ).sub
         (averagedVector_quotient_tendsto_zero U_grp φ))
  · push Not at hpos
    have hneg : h < 0 := lt_of_le_of_ne hpos hh
    have h_empty : Set.Ioc 0 h = ∅ := Set.Ioc_eq_empty (not_lt.mpr hneg.le)
    unfold averagedVector
    rw [h_empty, setIntegral_empty, smul_zero]
    exact (generatorDomain U_grp).zero_mem


lemma generatorDomain_dense_via_average :
    Dense (generatorDomain U_grp : Set H) := by
  rw [Metric.dense_iff]
  intro φ ε hε
  have h_tendsto := averagedVector_tendsto U_grp φ
  rw [Metric.tendsto_nhds] at h_tendsto
  specialize h_tendsto ε hε
  rw [Filter.eventually_iff_exists_mem] at h_tendsto
  obtain ⟨S, hS_mem, hS_ball⟩ := h_tendsto
  rw [mem_nhdsWithin] at hS_mem
  obtain ⟨U, hU_open, hU_zero, hU_sub⟩ := hS_mem
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := hU_open 0 hU_zero
  have hh : δ / 2 ≠ 0 := by linarith
  have hh_pos : δ / 2 > 0 := by linarith
  refine ⟨averagedVector U_grp (δ / 2) hh φ, ?_, ?_⟩
  · have h_in_ball : δ / 2 ∈ Metric.ball 0 δ := by
      rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_pos hh_pos]
      linarith
    have h_in_U : δ / 2 ∈ U := hδ_ball h_in_ball
    have h_in_S : δ / 2 ∈ S := hU_sub ⟨h_in_U, hh_pos⟩
    have := hS_ball (δ / 2) h_in_S
    rw [dif_pos hh] at this
    exact this
  · exact averagedVector_in_domain U_grp (δ / 2) hh φ

lemma generatorDomain_maximal (ψ : H)
    (h : ∃ η : H, Tendsto (fun t : ℝ => ((I : ℂ) * t)⁻¹ • (U_grp.U t ψ - ψ)) (𝓝[≠] 0) (𝓝 η)) :
    ψ ∈ generatorDomain U_grp := h

lemma generator_isSelfAdjoint : IsSelfAdjoint (generator U_grp) :=
  isSelfAdjoint_of_surjective_addSub (generator U_grp)
    (generator_isFormalAdjoint U_grp)
    (generatorDomain_dense_via_average U_grp)
    (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)

end Spectra.Resolvent

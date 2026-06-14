/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Bochner/Limits/Plus.lean
-/
import Spectra.Resolvent.Integral.Limits.Helpers

/-!
# Generator Limit for R₊

This file proves that the resolvent integral `R₊(φ) = (-i) ∫₀^∞ e^{-t} U(t)φ dt`
lies in the generator domain and satisfies `A(R₊φ) = φ - iR₊φ`.

## Tags

generator, resolvent, limit
-/
open MeasureTheory Measure Filter Topology Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

section GeneratorLimitPlus

variable (U_grp : OneParameterUnitaryGroup (H := H))

lemma integrableOn_exp_neg_orbit_Ici_plus (φ : H) (b : ℝ) :
    IntegrableOn (fun t => Real.exp (-t) • U_grp.U t φ) (Set.Ici b) :=
  integrableOn_Ici_of_Ici_zero (exp_neg_orbit_continuous_plus U_grp φ)
    (integrable_exp_neg_unitary U_grp φ) b

lemma integral_Ici_orbit_split_plus (φ : H) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ici a, Real.exp (-t) • U_grp.U t φ =
    (∫ t in Set.Ioc a b, Real.exp (-t) • U_grp.U t φ) +
    ∫ t in Set.Ici b, Real.exp (-t) • U_grp.U t φ :=
  integral_Ici_split_of (exp_neg_orbit_continuous_plus U_grp φ)
    (integrable_exp_neg_unitary U_grp φ) hab

lemma unitary_apply_Ici_orbit_integral_plus (φ : H) (h : ℝ) :
    U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
    Real.exp h • ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ := by
  have h_int := integrable_exp_neg_unitary U_grp φ
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U t φ) =
                      Real.exp (-t) • U_grp.U (t + h) φ := by
    intro t
    have hlaw := U_grp.group_law h t
    rw [add_comm] at hlaw
    rw [hlaw, ContinuousLinearMap.comp_apply]
    exact map_smul (U_grp.U h) _ _
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (t + h) φ =
                    Real.exp h • (Real.exp (-(t + h)) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [h_exp]
  rw [integral_smul]
  have h_subst : ∫ t in Set.Ici 0, Real.exp (-(t + h)) • U_grp.U (t + h) φ =
                 ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ := by
    have h_preimage : (· + h) ⁻¹' (Set.Ici h) = Set.Ici 0 := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ici]
      constructor
      · intro ht; linarith
      · intro ht; linarith
    have h_map : Measure.map (· + h) volume = (volume : Measure ℝ) :=
      (measurePreserving_add_right volume h).map_eq
    have h_meas_set : MeasurableSet (Set.Ici h) := measurableSet_Ici
    have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U s φ)
                      (Measure.map (· + h) volume) := by
      rw [h_map]
      exact ((Real.continuous_exp.comp continuous_neg).smul
        (U_grp.strong_continuous φ)).aestronglyMeasurable
    have h_g_meas : AEMeasurable (· + h) volume := (measurable_add_const h).aemeasurable
    rw [← h_map, MeasureTheory.setIntegral_map h_meas_set h_f_meas h_g_meas, h_preimage]
    congr 1
    ext t
    exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t
  rw [h_subst]


lemma unitary_shift_resolventIntegralPlus (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ =
    (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) -
    (-I) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
  unfold resolventIntegralPlus
  rw [ContinuousLinearMap.map_smul, unitary_apply_Ici_orbit_integral_plus U_grp φ h,
      integral_Ici_orbit_split_plus U_grp φ (le_of_lt hh)]
  set X := ∫ s in Set.Ici h, Real.exp (-s) • U_grp.U s φ with hX_def
  set Y := ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ with hY_def
  rw [smul_add]
  calc -I • Real.exp h • X - (-I • Y + -I • X)
      = -I • Real.exp h • X - -I • X - -I • Y := by abel
    _ = -I • (Real.exp h • X - X) - -I • Y := by rw [← smul_sub]
    _ = -I • ((Real.exp h - 1) • X) - -I • Y := by rw [sub_smul, one_smul]


lemma unitary_shift_resolventIntegralPlus_neg (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralPlus U_grp φ) - resolventIntegralPlus U_grp φ =
    (-I) • (Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) +
    (-I) • ((Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) := by
  unfold resolventIntegralPlus
  rw [ContinuousLinearMap.map_smul, unitary_apply_Ici_orbit_integral_plus U_grp φ h,
      integral_Ici_orbit_split_plus U_grp φ (le_of_lt hh)]
  set X := ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ
  set Y := ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ
  rw [smul_add]
  calc -I • (Real.exp h • X + Real.exp h • Y) - -I • Y
      = -I • Real.exp h • X + -I • Real.exp h • Y - -I • Y := by rw [smul_add]
    _ = -I • Real.exp h • X + (-I • Real.exp h • Y - -I • Y) := by abel
    _ = -I • Real.exp h • X + -I • (Real.exp h • Y - Y) := by rw [← smul_sub]
    _ = -I • Real.exp h • X + -I • ((Real.exp h - 1) • Y) := by rw [sub_smul, one_smul]

lemma genPlus_target_eq (φ : H) :
    φ - I • resolventIntegralPlus U_grp φ =
      φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ := by
  unfold resolventIntegralPlus
  rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]

lemma genPlus_scalar (h : ℝ) : ((I * (h : ℂ))⁻¹ * (-I) : ℂ) = -(h : ℂ)⁻¹ := by
  rw [mul_inv_rev, mul_assoc, mul_neg, inv_mul_cancel₀ I_ne_zero, mul_neg_one]

lemma genPlus_diffQuotient_pos (φ : H) (h : ℝ) (hh : h > 0) :
    ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
        resolventIntegralPlus U_grp φ) =
      -((h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ) +
      ((h : ℂ)⁻¹ • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) := by
  rw [unitary_shift_resolventIntegralPlus U_grp φ h hh,
      smul_sub, smul_smul, smul_smul, genPlus_scalar h,
      neg_smul, neg_smul, sub_neg_eq_add]

lemma genPlus_diffQuotient_neg (φ : H) (h : ℝ) (hh : h < 0) :
    ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
        resolventIntegralPlus U_grp φ) =
      (-(h : ℂ)⁻¹ • Real.exp h • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) +
      (-(h : ℂ)⁻¹ • (Real.exp h - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) := by
  rw [unitary_shift_resolventIntegralPlus_neg U_grp φ h hh,
      smul_add, smul_smul, smul_smul, genPlus_scalar h]

lemma genPlus_bulk_pos (φ : H) :
    Tendsto (fun h : ℝ => -((h : ℂ)⁻¹ • (Real.exp h - 1) •
        ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ))
      (𝓝[>] 0) (𝓝 (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ))) := by
  apply Tendsto.neg
  have he : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[>] 0) (𝓝 1) :=
    tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  have hi : Tendsto (fun h : ℝ => ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
      (𝓝[>] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
    (tendsto_integral_Ici_exp_unitary U_grp φ).mono_left nhdsWithin_le_nhds
  have he_cplx : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    convert Tendsto.comp (continuous_ofReal.tendsto 1) he using 1
    ext h
    simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
  have h_prod : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ) •
      ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
      (𝓝[>] 0) (𝓝 ((1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
    Tendsto.smul he_cplx hi
  simp only [one_smul] at h_prod
  apply Tendsto.congr' _ h_prod
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [div_eq_inv_mul]
  conv_lhs =>
    rw [show (↑(Real.exp h) : ℂ) - 1 = ↑(Real.exp h - 1) from by rw [ofReal_sub, ofReal_one]]
    rw [← smul_smul]
  rfl

lemma genPlus_boundary_neg (φ : H) :
    Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • Real.exp h •
        ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ) (𝓝[<] 0) (𝓝 φ) := by
  have h_avg := tendsto_average_integral_unitary_neg U_grp φ
  have he' : Tendsto (fun h : ℝ => Real.exp h) (𝓝[<] 0) (𝓝 (1 : ℝ)) := by
    rw [← Real.exp_zero]
    exact Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_comb : Tendsto (fun h : ℝ => Real.exp h • (((-h)⁻¹ : ℂ) •
      ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ)) (𝓝[<] 0) (𝓝 ((1 : ℝ) • φ)) :=
    Tendsto.smul he' h_avg
  simp only [one_smul] at h_comb
  apply Tendsto.congr' _ h_comb
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [smul_comm, @inv_neg]

lemma genPlus_bulk_neg (φ : H) :
    Tendsto (fun h : ℝ => -(h : ℂ)⁻¹ • (Real.exp h - 1) •
        ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
      (𝓝[<] 0) (𝓝 (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ))) := by
  have he : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[<] 0) (𝓝 1) :=
    tendsto_exp_sub_one_div.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
  have he_cplx : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ)) (𝓝[<] 0) (𝓝 1) := by
    convert Tendsto.comp (continuous_ofReal.tendsto 1) he using 1
    ext h
    simp only [Function.comp_apply, ofReal_div, ofReal_sub, ofReal_one]
  have h_prod : Tendsto (fun h : ℝ => ((Real.exp h - 1) / h : ℂ) •
      ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
      (𝓝[<] 0) (𝓝 ((1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) :=
    Tendsto.smul he_cplx tendsto_const_nhds
  simp only [one_smul] at h_prod
  have h_inner : Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (Real.exp h - 1) •
      ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)
      (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) := by
    apply Tendsto.congr' _ h_prod
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [div_eq_inv_mul]
    conv_lhs =>
      rw [show (↑(Real.exp h) : ℂ) - 1 = ↑(Real.exp h - 1) from by rw [ofReal_sub, ofReal_one]]
      rw [← smul_smul]
    rw [@Complex.coe_smul]
  apply Tendsto.congr' _ h_inner.neg
  filter_upwards with h
  rw [neg_smul]

lemma generator_limit_resolventIntegralPlus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralPlus U_grp φ) -
        resolventIntegralPlus U_grp φ))
      (𝓝[≠] 0) (𝓝 (φ - I • resolventIntegralPlus U_grp φ)) := by
  have h_compl : ({0} : Set ℝ)ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · intro hx; rcases lt_or_gt_of_ne hx with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact ne_of_gt h
      · exact ne_of_lt h
  rw [genPlus_target_eq U_grp φ,
      show (𝓝[≠] (0 : ℝ)) = 𝓝[Set.Ioi 0 ∪ Set.Iio 0] 0 by rw [← h_compl], nhdsWithin_union]
  refine Tendsto.sup ?_ ?_
  · rw [show φ - (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
          -(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) + φ by abel]
    refine Tendsto.congr' ?_
      ((genPlus_bulk_pos U_grp φ).add (tendsto_average_integral_unitary U_grp φ))
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (genPlus_diffQuotient_pos U_grp φ h hh).symm
  · rw [show φ - (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ) =
          φ + (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) by abel]
    refine Tendsto.congr' ?_
      ((genPlus_boundary_neg U_grp φ).add (genPlus_bulk_neg U_grp φ))
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (genPlus_diffQuotient_neg U_grp φ h hh).symm

end GeneratorLimitPlus

end Spectra.Resolvent

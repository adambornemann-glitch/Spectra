/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: Bochner/Limits/Minus.lean
-/
import Spectra.UnitaryEvolution.BochnerIntegration.Limits.Helpers
import Mathlib.MeasureTheory.Function.LpSpace.Complete
/-!
# Generator Limit for R₋

This file proves that the resolvent integral `R₋(φ) = i ∫₀^∞ e^{-t} U(-t)φ dt`
lies in the generator domain and satisfies `A(R₋φ) = φ + iR₋φ`.


## Tags

generator, resolvent, limit
-/

namespace QuantumMechanics.Bochner

open MeasureTheory Measure Filter Topology Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section GeneratorLimitMinus

variable (U_grp : OneParameterUnitaryGroup (H := H))


lemma unitary_shift_resolventIntegralMinus (φ : H) (h : ℝ) (hh : h > 0) :
    U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ =
    I • (Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
    I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
  unfold resolventIntegralMinus
  rw [ContinuousLinearMap.map_smul, unitary_apply_Ici_orbit_integral U_grp φ h,
      integral_Ici_orbit_split U_grp φ (show (-h : ℝ) ≤ 0 by linarith)]
  set X := ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ
  set Y := ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ
  rw [smul_add]
  calc I • (Real.exp (-h) • X + Real.exp (-h) • Y) - I • Y
      = I • Real.exp (-h) • X + I • Real.exp (-h) • Y - I • Y := by rw [smul_add]
    _ = I • Real.exp (-h) • X + (I • Real.exp (-h) • Y - I • Y) := by abel
    _ = I • Real.exp (-h) • X + I • (Real.exp (-h) • Y - Y) := by rw [← smul_sub]
    _ = I • Real.exp (-h) • X + I • ((Real.exp (-h) - 1) • Y) := by rw [sub_smul, one_smul]


lemma unitary_shift_resolventIntegralMinus_neg (φ : H) (h : ℝ) (hh : h < 0) :
    U_grp.U h (resolventIntegralMinus U_grp φ) - resolventIntegralMinus U_grp φ =
    I • ((Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) -
    I • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ := by
  unfold resolventIntegralMinus
  rw [ContinuousLinearMap.map_smul, unitary_apply_Ici_orbit_integral U_grp φ h,
      integral_Ici_orbit_split U_grp φ (show (0:ℝ) ≤ -h by linarith)]
  set X := ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ
  set Y := ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ
  rw [smul_add]
  calc I • Real.exp (-h) • Y - (I • X + I • Y)
      = I • Real.exp (-h) • Y - I • Y - I • X := by abel
    _ = I • (Real.exp (-h) • Y - Y) - I • X := by rw [← smul_sub]
    _ = I • ((Real.exp (-h) - 1) • Y) - I • X := by rw [sub_smul, one_smul]


private lemma genMinus_target_eq (φ : H) :
    φ + I • resolventIntegralMinus U_grp φ =
      φ - ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ := by
  unfold resolventIntegralMinus
  rw [smul_smul, I_mul_I, neg_one_smul, sub_eq_add_neg]

private lemma genMinus_scalar (h : ℝ) : ((I * (h : ℂ))⁻¹ * I : ℂ) = (h : ℂ)⁻¹ := by
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ I_ne_zero, mul_one]

private lemma genMinus_diffQuotient_pos (φ : H) (h : ℝ) (hh : h > 0) :
    ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
        resolventIntegralMinus U_grp φ) =
      ((h : ℂ)⁻¹ • Real.exp (-h) • ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) +
      ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) := by
  rw [unitary_shift_resolventIntegralMinus U_grp φ h hh, smul_add, smul_smul, smul_smul,
      genMinus_scalar h]

private lemma genMinus_diffQuotient_neg (φ : H) (h : ℝ) (hh : h < 0) :
    ((I * (h : ℂ))⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
        resolventIntegralMinus U_grp φ) =
      ((h : ℂ)⁻¹ • (Real.exp (-h) - 1) • ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ) +
      ((-(h : ℂ)⁻¹) • ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) := by
  rw [unitary_shift_resolventIntegralMinus_neg U_grp φ h hh,
      smul_sub, smul_smul, smul_smul, genMinus_scalar h,
      sub_eq_add_neg, neg_smul]

private lemma genMinus_bulk_pos (φ : H) :
    Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (Real.exp (-h) - 1) •
        ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)
      (𝓝[>] 0) (𝓝 (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ))) := by
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_neg_nhdsWithin_Ioi.mono_right (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
  have h_prod :
      Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ) •
          ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)
        (𝓝[>] 0) (𝓝 ((-1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) :=
    (exp_neg_sub_one_div_ofReal_tendsto_neg_one hneg).smul tendsto_const_nhds
  simp only [neg_one_smul] at h_prod
  apply Tendsto.congr' _ h_prod
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [div_eq_inv_mul]
  conv_lhs =>
    rw [show (↑(Real.exp (-h)) : ℂ) - 1 = ↑(Real.exp (-h) - 1) from by rw [ofReal_sub, ofReal_one]]
    rw [← smul_smul]
  rw [@Complex.coe_smul]

private lemma genMinus_boundary_pos (φ : H) :
    Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • Real.exp (-h) •
        ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) (𝓝[>] 0) (𝓝 φ) := by
  have he : Tendsto (fun h : ℝ => Real.exp (-h)) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun h : ℝ => -h) (𝓝 (0 : ℝ)) (𝓝 0) := by
      convert (continuous_neg (G := ℝ)).tendsto 0 using 1; simp
    have h2 : Tendsto Real.exp (𝓝 0) (𝓝 1) := by
      rw [← Real.exp_zero]; exact Real.continuous_exp.tendsto 0
    exact (h2.comp h1).mono_left nhdsWithin_le_nhds
  have h_avg : Tendsto (fun h : ℝ => (h⁻¹ : ℂ) •
      ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ) (𝓝[>] 0) (𝓝 φ) := by
    have h_eq_int : ∀ h > 0, ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ =
                             ∫ t in (-h)..0, Real.exp (-t) • U_grp.U (-t) φ := by
      intro h hh; rw [intervalIntegral.integral_of_le (by linarith : -h ≤ 0)]
    have h_tendsto_real := avg_exp_neg_orbit_tendsto U_grp φ
    have h_neg_tendsto := h_tendsto_real.mono_left
      (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx)) |>.comp tendsto_neg_nhdsWithin_Ioi
    apply Tendsto.congr' _ h_neg_tendsto
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [h_eq_int h hh]
    simp only [Function.comp_apply]
    rw [intervalIntegral.integral_symm (-h) 0, smul_neg, neg_eq_iff_eq_neg, ← neg_smul,
        (Complex.coe_smul (-h)⁻¹ _).symm]
    congr 1
    simp only [ofReal_inv, ofReal_neg, neg_inv]
  have h_comb : Tendsto (fun h : ℝ => Real.exp (-h) • ((h⁻¹ : ℂ) •
      ∫ t in Set.Ioc (-h) 0, Real.exp (-t) • U_grp.U (-t) φ)) (𝓝[>] 0) (𝓝 ((1 : ℝ) • φ)) :=
    Tendsto.smul he h_avg
  simp only [one_smul] at h_comb
  apply Tendsto.congr' _ h_comb
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [smul_comm]

private lemma genMinus_tail_continuous_neg (φ : H) :
    Tendsto (fun h : ℝ => ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ)
      (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) := by
  have h_cont := exp_neg_orbit_continuous U_grp φ
  have h_prim_cont : Continuous (fun a => ∫ t in (0 : ℝ)..a, Real.exp (-t) • U_grp.U (-t) φ) :=
    intervalIntegral.continuous_primitive (fun a b => h_cont.intervalIntegrable a b) 0
  have h_prim_zero : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U (-t) φ = 0 :=
    intervalIntegral.integral_same
  have h_prim_tendsto : Tendsto (fun a => ∫ t in (0 : ℝ)..a, Real.exp (-t) • U_grp.U (-t) φ)
      (𝓝 0) (𝓝 0) := by rw [← h_prim_zero]; exact h_prim_cont.tendsto 0
  have h_split : ∀ h < 0, ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ =
      (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) -
      ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ := by
    intro h hh
    have h_neg_pos : (0 : ℝ) ≤ -h := by linarith
    rw [intervalIntegral.integral_of_le h_neg_pos, integral_Ici_orbit_split U_grp φ h_neg_pos]
    abel
  have h_int_tendsto : Tendsto (fun h : ℝ => ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ)
      (𝓝[<] 0) (𝓝 0) := by
    have h_neg_tendsto : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝 0) := by
      have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
        convert (continuous_neg (G := ℝ)).tendsto 0 using 1; simp
      exact this.mono_left nhdsWithin_le_nhds
    have := h_prim_tendsto.comp h_neg_tendsto
    convert this using 1
  have h_combined : Tendsto (fun h : ℝ => (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) -
      ∫ t in (0 : ℝ)..(-h), Real.exp (-t) • U_grp.U (-t) φ)
      (𝓝[<] 0) (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) := by
    convert tendsto_const_nhds.sub h_int_tendsto using 1
    simp only [sub_zero]
  apply Tendsto.congr' _ h_combined
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (h_split h hh).symm

private lemma genMinus_bulk_neg (φ : H) :
    Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (Real.exp (-h) - 1) •
        ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ)
      (𝓝[<] 0) (𝓝 (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ))) := by
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[≠] 0) :=
    tendsto_neg_nhdsWithin_Iio.mono_right (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  have h_prod : Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ) •
      ∫ t in Set.Ici (-h), Real.exp (-t) • U_grp.U (-t) φ)
      (𝓝[<] 0) (𝓝 ((-1 : ℂ) • ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) :=
    (exp_neg_sub_one_div_ofReal_tendsto_neg_one hneg).smul (genMinus_tail_continuous_neg U_grp φ)
  simp only [neg_one_smul] at h_prod
  apply Tendsto.congr' _ h_prod
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [div_eq_inv_mul]
  conv_lhs =>
    rw [show (↑(Real.exp (-h)) : ℂ) - 1 = ↑(Real.exp (-h) - 1) from by rw [ofReal_sub, ofReal_one]]
    rw [← smul_smul]
  rw [@Complex.coe_smul]

private lemma genMinus_boundary_neg (φ : H) :
    Tendsto (fun h : ℝ => (-(h : ℂ)⁻¹) •
        ∫ t in Set.Ioc 0 (-h), Real.exp (-t) • U_grp.U (-t) φ) (𝓝[<] 0) (𝓝 φ) := by
  have h_avg : Tendsto (fun h : ℝ => (h⁻¹ : ℂ) •
      ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U (-t) φ) (𝓝[>] 0) (𝓝 φ) := by
    have h_eq_int : ∀ h > 0, ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U (-t) φ =
                             ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ := by
      intro h hh; rw [intervalIntegral.integral_of_le (le_of_lt hh)]
    have h_tendsto_real := avg_exp_neg_orbit_tendsto U_grp φ
    have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
    apply Tendsto.congr' _ h_restrict
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [h_eq_int h hh, (Complex.coe_smul h⁻¹ _).symm, ofReal_inv]
  have h_comp := h_avg.comp tendsto_neg_nhdsWithin_Iio
  apply Tendsto.congr' _ h_comp
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [Function.comp_apply]
  rw [show -(h : ℂ)⁻¹ = ((-h) : ℂ)⁻¹ from by rw [@neg_inv]]
  simp only [ofReal_neg, inv_neg, neg_smul]


lemma generator_limit_resolventIntegralMinus (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) • (U_grp.U h (resolventIntegralMinus U_grp φ) -
        resolventIntegralMinus U_grp φ))
      (𝓝[≠] 0) (𝓝 (φ + I • resolventIntegralMinus U_grp φ)) := by
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
  rw [genMinus_target_eq U_grp φ,
      show (𝓝[≠] (0 : ℝ)) = 𝓝[Set.Ioi 0 ∪ Set.Iio 0] 0 by rw [← h_compl], nhdsWithin_union]
  refine Tendsto.sup ?_ ?_
  · rw [show φ - (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
          φ + (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) by abel]
    refine Tendsto.congr' ?_ ((genMinus_boundary_pos U_grp φ).add (genMinus_bulk_pos U_grp φ))
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (genMinus_diffQuotient_pos U_grp φ h hh).symm
  · rw [show φ - (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
          (-(∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ)) + φ by abel]
    refine Tendsto.congr' ?_ ((genMinus_bulk_neg U_grp φ).add (genMinus_boundary_neg U_grp φ))
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (genMinus_diffQuotient_neg U_grp φ h hh).symm


end GeneratorLimitMinus

end QuantumMechanics.Bochner

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Resolvent/IntegralZ.lean
-/
import Spectra.Resolvent.Diagonal.IntegralZ.Defs
open Complex MeasureTheory Filter Topology

open Spectra.QuantumMechanics
open OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))
namespace Spectra.Resolvent

/-- Bulk derivative: `(e^{izh} - 1)/h → iz` as `h → 0`. The `z`-generalization of
`tendsto_exp_sub_one_div` (the `z = -i` case gives `iz = 1`). -/
lemma tendsto_cexp_mul_sub_one_div {z : ℂ} :
    Tendsto (fun h : ℝ => (cexp (I * z * (h : ℂ)) - 1) / (h : ℂ)) (𝓝[≠] 0) (𝓝 (I * z)) := by
  -- d/dw exp((iz)·w) = iz at w = 0
  have hw : HasDerivAt (fun w : ℂ => cexp (I * z * w)) (I * z) ((0 : ℝ) : ℂ) := by
    have h0 : HasDerivAt (fun w : ℂ => I * z * w) (I * z) ((0 : ℝ) : ℂ) := by
      simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul (I * z)
    simpa using h0.cexp
  -- restrict to ℝ along ofReal
  have hr : HasDerivAt (fun h : ℝ => cexp (I * z * (h : ℂ))) (I * z) 0 := hw.comp_ofReal
  rw [hasDerivAt_iff_tendsto_slope] at hr
  refine Tendsto.congr' ?_ hr
  filter_upwards [self_mem_nhdsWithin] with h _hh
  simp only [slope_def_module, sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [← Complex.coe_smul, smul_eq_mul, ofReal_inv, div_eq_inv_mul]

lemma tendsto_integral_Ici_expZ_unitary {z : ℂ} (hz : z.im < 0) (φ : H) :
    Tendsto (fun h : ℝ => ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
            (𝓝 0)
            (𝓝 (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) := by
  have h_cont : Continuous (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.const_mul (I * z)).neg)).smul
      (U_grp.strong_continuous φ)
  have h_int := integrable_expZ_unitary U_grp hz φ
  have h_prim_cont : Continuous
      (fun h => ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) :=
    intervalIntegral.continuous_primitive (fun a b => h_cont.intervalIntegrable a b) 0
  have h_prim_zero : ∫ t in (0 : ℝ)..0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_prim_tendsto :
      Tendsto (fun h => ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
              (𝓝 0) (𝓝 0) := by
    rw [← h_prim_zero]
    exact h_prim_cont.tendsto 0
  convert tendsto_const_nhds.sub h_prim_tendsto using 1
  · ext h
    by_cases hh : h ≥ 0
    · have h_ae_eq : ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                     ∫ t in Set.Ioi (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ :=
        setIntegral_congr_set Ioi_ae_eq_Ici.symm
      have h_union : Set.Ioi (0 : ℝ) = Set.Ioc 0 h ∪ Set.Ioi h := by
        ext x
        simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
        constructor
        · intro hx
          by_cases hxh : x ≤ h
          · left; exact ⟨hx, hxh⟩
          · right; exact lt_of_not_ge hxh
        · intro hx
          cases hx with
          | inl hx => exact hx.1
          | inr hx => linarith [hh, hx]
      have h_disj : Disjoint (Set.Ioc 0 h) (Set.Ioi h) := Set.Ioc_disjoint_Ioi le_rfl
      have h_ae_eq2 : ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                      ∫ t in Set.Ioi h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ :=
        setIntegral_congr_set Ioi_ae_eq_Ici.symm
      have h_eq1 : ∫ t in Set.Ioi (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                   (∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
                   ∫ t in Set.Ioi h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
        rw [h_union, setIntegral_union h_disj measurableSet_Ioi
            (h_int.mono_set (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Ici_self))
            (h_int.mono_set (Set.Ioi_subset_Ici hh))]
      have h_eq2 : ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                   ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
        rw [intervalIntegral.integral_of_le hh]
      have h_eq3 : ∫ t in Set.Ioi h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                   (∫ t in Set.Ioi (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) -
                   ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
        exact Eq.symm (sub_eq_of_eq_add' h_eq1)
      rw [h_ae_eq2, h_eq3, h_ae_eq.symm, h_eq2]
    · push Not at hh
      have h_union : Set.Ici h = Set.Ico h 0 ∪ Set.Ici (0 : ℝ) := by
        ext x
        simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ico]
        constructor
        · intro hx
          by_cases hx0 : x < 0
          · left; exact ⟨hx, hx0⟩
          · right; linarith
        · intro hx
          cases hx with
          | inl hx => exact hx.1
          | inr hx => linarith [hh, hx]
      have h_disj : Disjoint (Set.Ico h 0) (Set.Ici (0 : ℝ)) := by
        grind only [= Set.disjoint_left, = Set.mem_Ico, = Set.mem_Ici]
      have h_eq1 : ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                   (∫ t in Set.Ico h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) +
                   ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
        rw [h_union, setIntegral_union h_disj measurableSet_Ici
            (h_cont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
            h_int]
      have h_eq2 : ∫ t in Set.Ico h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                   -(∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) := by
        rw [← intervalIntegral.integral_symm]
        rw [intervalIntegral.integral_of_le (le_of_lt hh)]
        rw [@restrict_Ico_eq_restrict_Ioc]
      rw [h_eq1, h_eq2]; abel
  · simp only [sub_zero]

lemma tendsto_average_integral_expZ_unitary {z : ℂ} (φ : H) :
    Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
            (𝓝[>] 0)
            (𝓝 φ) := by
  have h_cont : Continuous (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.const_mul (I * z)).neg)).smul
      (U_grp.strong_continuous φ)
  have h_f0 : cexp (-(I * z * ((0 : ℝ) : ℂ))) • U_grp.U 0 φ = φ := by
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]
  have h_eq : ∀ h > (0 : ℝ), ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                       ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
                            (cexp (-(I * z * ((0 : ℝ) : ℂ))) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_tendsto_real :
      Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
              (𝓝[≠] 0) (𝓝 φ) := by
    have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
    rw [hasDerivWithinAt_iff_tendsto_slope] at this
    simp only [Set.diff_diff, Set.union_self] at this
    convert this using 1
    ext h
    unfold slope
    simp only [sub_zero, h_F0, vsub_eq_sub]
    · congr 1
      exact Set.compl_eq_univ_diff {(0 : ℝ)}
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, ← ofReal_inv, @Complex.coe_smul]

lemma tendsto_average_integral_expZ_unitary_neg {z : ℂ} (φ : H) :
    Tendsto (fun h : ℝ => ((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
            (𝓝[<] 0)
            (𝓝 φ) := by
  have h_cont : Continuous (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.const_mul (I * z)).neg)).smul
      (U_grp.strong_continuous φ)
  have h_f0 : cexp (-(I * z * ((0 : ℝ) : ℂ))) • U_grp.U 0 φ = φ := by
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]
  have h_eq : ∀ h < (0 : ℝ), ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                       ∫ t in h..0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_eq' : ∀ h < (0 : ℝ), ∫ t in h..0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                        -∫ t in 0..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
    intro h _
    rw [intervalIntegral.integral_symm]
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
                            (cexp (-(I * z * ((0 : ℝ) : ℂ))) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_tendsto_real :
      Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
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
  have h_restrict := h_tendsto_real.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, h_eq' h hh]
  rw [smul_neg]
  rw [← neg_smul]
  rw [(Complex.coe_smul h⁻¹ _).symm, ofReal_inv]
  congr 1
  rw [@neg_inv]
  simp_all only [intervalIntegral.integral_same, neg_neg]

end Spectra.Resolvent

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Integral.GroupIntegration
/-!
# Helper Lemmas for Generator Limits

This file contains shared analytical lemmas used in proving that the resolvent
integrals `R±(φ)` lie in the generator domain.

## Main statements

* `tendsto_exp_sub_one_div`: `(e^h - 1)/h → 1` as `h → 0`
* `tendsto_integral_Ici_exp_unitary`: continuity of `∫_{[h,∞)} e^{-t} U(t)φ dt` at `h = 0`
* `tendsto_average_integral_unitary`: `h⁻¹ ∫_{(0,h]} e^{-t} U(t)φ dt → φ` as `h → 0⁺`
* `tendsto_average_integral_unitary_neg`: analogous limit as `h → 0⁻`

## Tags

generator, limit, exponential, average
-/
open MeasureTheory Measure Filter Topology Complex
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

section Helpers

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The difference quotient `(e^h - 1)/h → 1` as `h → 0` along `𝓝[≠] 0`. -/
lemma tendsto_exp_sub_one_div :
    Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[≠] 0) (𝓝 1) := by
  have h : HasDerivAt Real.exp 1 0 := by
    convert Real.hasDerivAt_exp 0 using 1
    exact Real.exp_zero.symm
  rw [hasDerivAt_iff_tendsto_slope] at h
  convert h using 1
  ext y
  simp only [slope, Real.exp_zero, sub_zero, vsub_eq_sub, smul_eq_mul]
  exact div_eq_inv_mul (Real.exp y - 1) y

/-- The half-line integral `∫_{[h,∞)} e^{-t} U(t)φ dt` is continuous at `h = 0`. -/
lemma tendsto_integral_Ici_exp_unitary (φ : H) :
    Tendsto (fun h : ℝ => ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ)
            (𝓝 0)
            (𝓝 (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ)) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
  have h_int := integrable_exp_neg_unitary U_grp φ
  have h_prim_cont : Continuous (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ) :=
    intervalIntegral.continuous_primitive (fun a b => h_cont.intervalIntegrable a b) 0
  have h_prim_zero : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_prim_tendsto : Tendsto (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                                (𝓝 0) (𝓝 0) := by
    rw [← h_prim_zero]
    exact h_prim_cont.tendsto 0
  convert tendsto_const_nhds.sub h_prim_tendsto using 1
  · ext h
    by_cases hh : h ≥ 0
    · have h_ae_eq : ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ =
                     ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ :=
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
      have h_ae_eq2 : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ =
                      ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ :=
        setIntegral_congr_set Ioi_ae_eq_Ici.symm
      have h_eq1 : ∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ) +
                   ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ := by
        rw [h_union, setIntegral_union h_disj measurableSet_Ioi
            (h_int.mono_set (Set.Ioc_subset_Icc_self.trans Set.Icc_subset_Ici_self))
            (h_int.mono_set (Set.Ioi_subset_Ici hh))]
      have h_eq2 : ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ =
                   ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ := by
        rw [intervalIntegral.integral_of_le hh]
      have h_eq3 : ∫ t in Set.Ioi h, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ioi 0, Real.exp (-t) • U_grp.U t φ) -
                   ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ := by
        exact Eq.symm (sub_eq_of_eq_add' h_eq1)
      rw [h_ae_eq2, h_eq3, h_ae_eq.symm, h_eq2]
    · push Not at hh
      have h_union : Set.Ici h = Set.Ico h 0 ∪ Set.Ici 0 := by
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
      have h_disj : Disjoint (Set.Ico h 0) (Set.Ici 0) := by
        grind only [= Set.disjoint_left, = Set.mem_Ico, = Set.mem_Ici]
      have h_eq1 : ∫ t in Set.Ici h, Real.exp (-t) • U_grp.U t φ =
                   (∫ t in Set.Ico h 0, Real.exp (-t) • U_grp.U t φ) +
                   ∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U t φ := by
        rw [h_union, setIntegral_union h_disj measurableSet_Ici
            (h_cont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
            h_int]
      have h_eq2 : ∫ t in Set.Ico h 0, Real.exp (-t) • U_grp.U t φ =
                   -(∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ) := by
        rw [← intervalIntegral.integral_symm]
        rw [intervalIntegral.integral_of_le (le_of_lt hh)]
        rw [@restrict_Ico_eq_restrict_Ioc]
      rw [h_eq1, h_eq2]
      ring_nf
      exact
        neg_add_eq_sub (∫ (t : ℝ) in 0..h, Real.exp (-t) • (U_grp.U t) φ)
          (∫ (t : ℝ) in Set.Ici 0, Real.exp (-t) • (U_grp.U t) φ)
  · simp only [sub_zero]

/-- The right average `h⁻¹ ∫_{(0,h]} e^{-t} U(t)φ dt → φ` as `h → 0⁺`. -/
lemma tendsto_average_integral_unitary (φ : H) :
    Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ)
            (𝓝[>] 0)
            (𝓝 φ) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
  have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
    simp only [neg_zero, Real.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]
  have h_eq : ∀ h > 0, ∫ t in Set.Ioc 0 h, Real.exp (-t) • U_grp.U t φ =
                       ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                            (Real.exp (-(0 : ℝ)) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
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

/-- The left average `(-h)⁻¹ ∫_{(h,0]} e^{-t} U(t)φ dt → φ` as `h → 0⁻`. -/
lemma tendsto_average_integral_unitary_neg (φ : H) :
    Tendsto (fun h : ℝ => ((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ)
            (𝓝[<] 0)
            (𝓝 φ) := by
  have h_cont : Continuous (fun t => Real.exp (-t) • U_grp.U t φ) :=
    (Real.continuous_exp.comp continuous_neg).smul (U_grp.strong_continuous φ)
  have h_f0 : Real.exp (-(0 : ℝ)) • U_grp.U 0 φ = φ := by
    simp only [neg_zero, Real.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]
  have h_eq : ∀ h < 0, ∫ t in Set.Ioc h 0, Real.exp (-t) • U_grp.U t φ =
                       ∫ t in h..0, Real.exp (-t) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_eq' : ∀ h < 0, ∫ t in h..0, Real.exp (-t) • U_grp.U t φ =
                        -∫ t in 0..h, Real.exp (-t) • U_grp.U t φ := by
    intro h _
    rw [intervalIntegral.integral_symm]
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
                            (Real.exp (-(0 : ℝ)) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, Real.exp (-t) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have h_tendsto_real : Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, Real.exp (-t) • U_grp.U t φ)
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
  simp_all only [neg_zero, Real.exp_zero, one_smul, intervalIntegral.integral_same, neg_neg]

/-- The reverse orbit integrand `t ↦ e^{-t} • U(-t)φ` is continuous. -/
lemma exp_neg_orbit_continuous (φ : H) :
    Continuous (fun t : ℝ => Real.exp (-t) • U_grp.U (-t) φ) :=
  (Real.continuous_exp.comp continuous_neg).smul
    ((U_grp.strong_continuous φ).comp continuous_neg)

/-- The reverse orbit integrand at `t = 0` equals `φ`, i.e. `e^{0} • U(0)φ = φ`. -/
lemma exp_neg_orbit_at_zero (φ : H) :
    Real.exp (-(0 : ℝ)) • U_grp.U (-(0 : ℝ)) φ = φ := by
  simp only [neg_zero, Real.exp_zero, one_smul]
  rw [U_grp.identity]
  simp only [ContinuousLinearMap.id_apply]

/-- Negation maps `𝓝[>] 0` to `𝓝[<] 0`, i.e. `h ↦ -h` sends right neighborhoods to left ones. -/
lemma tendsto_neg_nhdsWithin_Ioi :
    Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
      convert (continuous_neg (G := ℝ)).tendsto 0 using 1
      simp
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [Set.mem_Iio, Left.neg_neg_iff]
    exact hh

/-- Negation maps `𝓝[<] 0` to `𝓝[>] 0`, i.e. `h ↦ -h` sends left neighborhoods to right ones. -/
lemma tendsto_neg_nhdsWithin_Iio :
    Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
      convert (continuous_neg (G := ℝ)).tendsto 0 using 1
      simp
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [Set.mem_Ioi]
    exact Left.neg_pos_iff.mpr hh


/-- The difference quotient `(e^{-h} - 1)/h → -1` along any filter `l` with `-h → 0` in `𝓝[≠] 0`. -/
lemma exp_neg_sub_one_div_tendsto_neg_one {l : Filter ℝ}
    (hl : Tendsto (fun h : ℝ => -h) l (𝓝[≠] 0)) :
    Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / h) l (𝓝 (-1)) := by
  have h1 : Tendsto (fun h : ℝ => (Real.exp (-h) - 1) / (-h) * (-1)) l (𝓝 (1 * (-1))) := by
    apply Tendsto.mul
    · have := tendsto_exp_sub_one_div.comp hl
      convert this using 1
    · exact tendsto_const_nhds
  simp only [mul_neg_one] at h1
  convert h1 using 1
  ext h
  by_cases hh : h = 0
  · simp [hh]
  · field_simp

/-- Complex-valued form: `((e^{-h} - 1)/h : ℂ) → -1` along `l` with `-h → 0` in `𝓝[≠] 0`. -/
lemma exp_neg_sub_one_div_ofReal_tendsto_neg_one {l : Filter ℝ}
    (hl : Tendsto (fun h : ℝ => -h) l (𝓝[≠] 0)) :
    Tendsto (fun h : ℝ => ((Real.exp (-h) - 1) / h : ℂ)) l (𝓝 (-1)) := by
  have : Tendsto (fun h : ℝ => (((Real.exp (-h) - 1) / h : ℝ) : ℂ)) l (𝓝 ((-1 : ℝ) : ℂ)) :=
    (continuous_ofReal.tendsto _).comp (exp_neg_sub_one_div_tendsto_neg_one hl)
  simpa using this

/-- The reverse orbit average `h⁻¹ ∫₀^h e^{-t} U(-t)φ dt → φ` as `h → 0` along `𝓝[≠] 0`. -/
lemma avg_exp_neg_orbit_tendsto (φ : H) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0:ℝ)..h, Real.exp (-t) • U_grp.U (-t) φ)
      (𝓝[≠] 0) (𝓝 φ) := by
  have h_cont : Continuous (fun t : ℝ => Real.exp (-t) • U_grp.U (-t) φ) :=
    exp_neg_orbit_continuous U_grp φ
  have h_deriv : HasDerivAt (fun x => ∫ t in (0:ℝ)..x, Real.exp (-t) • U_grp.U (-t) φ)
      (Real.exp (-(0:ℝ)) • U_grp.U (-(0:ℝ)) φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [exp_neg_orbit_at_zero U_grp φ] at h_deriv
  have h_F0 : ∫ t in (0:ℝ)..0, Real.exp (-t) • U_grp.U (-t) φ = 0 :=
    intervalIntegral.integral_same
  have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
  rw [hasDerivWithinAt_iff_tendsto_slope] at this
  simp only [Set.diff_diff, Set.union_self] at this
  convert this using 1
  · ext h
    unfold slope
    simp only [sub_zero, h_F0, vsub_eq_sub]
  · congr 1
    exact Set.compl_eq_univ_diff {(0:ℝ)}

/-- Translating the orbit integrand by `h` shifts the half-line lower limit from `0` to `-h`. -/
lemma integral_Ici_sub_shift (φ : H) (h : ℝ) :
    ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ =
    ∫ s in Set.Ici (-h), Real.exp (-s) • U_grp.U (-s) φ := by
  have h_preimage : (· - h) ⁻¹' (Set.Ici (-h)) = Set.Ici 0 := by
    ext t; simp only [Set.mem_preimage, Set.mem_Ici]; constructor <;> intro ht <;> linarith
  have h_map : Measure.map (· - h) volume = (volume : Measure ℝ) :=
    (measurePreserving_sub_right volume h).map_eq
  have h_f_meas : AEStronglyMeasurable (fun s => Real.exp (-s) • U_grp.U (-s) φ)
                    (Measure.map (· - h) volume) := by
    rw [h_map]
    exact (exp_neg_orbit_continuous U_grp φ).aestronglyMeasurable
  rw [← h_map, MeasureTheory.setIntegral_map measurableSet_Ici h_f_meas
        (measurable_sub_const h).aemeasurable, h_preimage]
  congr 1; ext t
  exact congrFun (congrArg DFunLike.coe (congrFun (congrArg restrict h_map) (Set.Ici 0))) t

/-- Applying `U h` to the half-line orbit integral shifts the lower limit by `-h`
and factors out `e^{-h}`. Sign-free: holds for all `h`. -/
lemma unitary_apply_Ici_orbit_integral (φ : H) (h : ℝ) :
    U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
    Real.exp (-h) • ∫ s in Set.Ici (-h), Real.exp (-s) • U_grp.U (-s) φ := by
  have h_int := integrable_exp_neg_unitary_neg U_grp φ
  have h_comm : U_grp.U h (∫ t in Set.Ici 0, Real.exp (-t) • U_grp.U (-t) φ) =
                ∫ t in Set.Ici 0, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  rw [h_comm]
  have h_shift : ∀ t, U_grp.U h (Real.exp (-t) • U_grp.U (-t) φ) =
                      Real.exp (-t) • U_grp.U (h - t) φ := by
    intro t
    have hlaw : U_grp.U h ∘L U_grp.U (-t) = U_grp.U (h - t) := by
      rw [show h - t = h + (-t) from sub_eq_add_neg h t]
      exact (U_grp.group_law h (-t)).symm
    rw [← hlaw, ContinuousLinearMap.comp_apply]
    exact map_smul (U_grp.U h) _ _
  simp_rw [h_shift]
  have h_exp : ∀ t, Real.exp (-t) • U_grp.U (h - t) φ =
                    Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) := by
    intro t
    rw [← smul_assoc, smul_eq_mul, ← Real.exp_add]
    congr 1
    · ring_nf
    · congr 1; abel_nf
  simp_rw [h_exp]
  have h_smul_comm :
      ∫ t in Set.Ici 0, Real.exp (-h) • (Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ) =
        Real.exp (-h) • ∫ t in Set.Ici 0, Real.exp (-(t - h)) • U_grp.U (-(t - h)) φ :=
    integral_smul (Real.exp (-h)) fun a => Real.exp (-(a - h)) • (U_grp.U (-(a - h))) φ
  rw [h_smul_comm, integral_Ici_sub_shift U_grp φ h]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- A continuous `f` integrable on `[0,∞)` is integrable on every half-line `[b,∞)`. -/
lemma integrableOn_Ici_of_Ici_zero {f : ℝ → H} (hcont : Continuous f)
    (h0 : IntegrableOn f (Set.Ici 0)) (b : ℝ) :
    IntegrableOn f (Set.Ici b) := by
  rcases le_or_gt 0 b with hb | hb
  · exact h0.mono_set (Set.Ici_subset_Ici.mpr hb)
  · have h_union : Set.Ici b = Set.Ico b 0 ∪ Set.Ici 0 := by
      ext x; simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ico]
      constructor
      · intro hx; rcases lt_or_ge x 0 with hlt | hge
        · exact Or.inl ⟨hx, hlt⟩
        · exact Or.inr hge
      · rintro (⟨hx, _⟩ | hx)
        · exact hx
        · linarith
    rw [h_union]
    exact (hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self).union h0

omit [CompleteSpace H] in
/-- For `a ≤ b`, the half-line integral of `f` splits as `∫_{(a,b]} f + ∫_{[b,∞)} f`. -/
lemma integral_Ici_split_of {f : ℝ → H} (hcont : Continuous f)
    (h0 : IntegrableOn f (Set.Ici 0)) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ici a, f t = (∫ t in Set.Ioc a b, f t) + ∫ t in Set.Ici b, f t := by
  have h_ae_eqa : ∫ t in Set.Ici a, f t = ∫ t in Set.Ioi a, f t :=
    setIntegral_congr_set Ioi_ae_eq_Ici.symm
  have h_ae_eqb : ∫ t in Set.Ici b, f t = ∫ t in Set.Ioi b, f t :=
    setIntegral_congr_set Ioi_ae_eq_Ici.symm
  have h_union : Set.Ioi a = Set.Ioc a b ∪ Set.Ioi b := by
    ext x; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hx; rcases le_or_gt x b with hxb | hxb
      · exact Or.inl ⟨hx, hxb⟩
      · exact Or.inr hxb
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  rw [h_ae_eqa, h_union,
      setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        ((integrableOn_Ici_of_Ici_zero hcont h0 b).mono_set Set.Ioi_subset_Ici_self),
      h_ae_eqb.symm]

/-- Split the half-line orbit integral at an interior point. -/
lemma integral_Ici_orbit_split (φ : H) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ici a, Real.exp (-t) • U_grp.U (-t) φ =
    (∫ t in Set.Ioc a b, Real.exp (-t) • U_grp.U (-t) φ) +
    ∫ t in Set.Ici b, Real.exp (-t) • U_grp.U (-t) φ :=
  integral_Ici_split_of (exp_neg_orbit_continuous U_grp φ)
    (integrable_exp_neg_unitary_neg U_grp φ) hab

end Helpers

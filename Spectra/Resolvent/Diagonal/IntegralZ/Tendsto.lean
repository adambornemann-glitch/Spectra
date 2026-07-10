/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.Diagonal.IntegralZ.Defs
import Spectra.Resolvent.Integral.Limits

/-!
# Continuity and limit lemmas for the general-`z` resolvent integral

This file collects the continuity/limit facts feeding the generator-recovery argument for the
Laplace-transform resolvent `resolventIntegralZ`: continuity of the resolvent integral in its
lower endpoint, and the one-sided average-to-initial-vector limits that identify the derivative
of the resolvent integral at `h = 0` with `φ` itself. Together with `Shift.lean`'s shift lemmas,
these feed `GeneratorLim.lean`'s generator-recovery theorem.

## Main statements

* `tendsto_cexp_mul_sub_one_div` — the scalar bulk derivative `(e^{izh} - 1)/h → iz`.
* `tendsto_integral_Ici_expZ_unitary` — continuity of `h ↦ ∫_{Ici h} e^{-izt}U(t)φ dt` at `h = 0`.
* `tendsto_average_integral_expZ_unitary` / `_neg` — the right/left average of the resolvent
  kernel over `Set.Ioc 0 h` / `Set.Ioc h 0` tends to `φ` as `h → 0`, from either side.
-/

open Complex MeasureTheory Filter Topology
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.Resolvent

variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The **bulk derivative**: `(e^{izh} - 1)/h → iz` as `h → 0`. The `z`-generalization of
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

/-- **Continuity in the lower endpoint**: `∫_{Ici h} e^{-izt}U(t)φ dt → ∫_{Ici 0} e^{-izt}U(t)φ dt`
as `h → 0`, for `Im z < 0`. Feeds `Shift.lean`'s `integral_Ici_orbit_split_Z` and, transitively,
the generator-recovery argument in `GeneratorLim.lean`. -/
lemma tendsto_integral_Ici_expZ_unitary {z : ℂ} (hz : z.im < 0) (φ : H) :
    Tendsto (fun h : ℝ => ∫ t in Set.Ici h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
            (𝓝 0)
            (𝓝 (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)) := by
  have h_cont := expZ_orbit_continuous U_grp (z := z) φ
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
    · have h_split := integral_Ici_split_of h_cont h_int hh
      have h_eq2 : ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                   ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ :=
        (intervalIntegral.integral_of_le hh).symm
      rw [h_eq2] at h_split
      exact (sub_eq_of_eq_add' h_split).symm
    · push Not at hh
      have h_split := integral_Ici_split_of h_cont h_int (le_of_lt hh)
      have h_eq2 : ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                   -(∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) := by
        rw [← intervalIntegral.integral_symm, intervalIntegral.integral_of_le (le_of_lt hh)]
      rw [h_eq2] at h_split
      rw [h_split]; abel
  · simp only [sub_zero]

/-- The **two-sided average limit** shared by both one-sided results below:
`h⁻¹ • ∫_{(0)..h} e^{-izt}U(t)φ dt → φ` as `h → 0` along the punctured neighborhood `𝓝[≠] 0`.
`tendsto_average_integral_expZ_unitary` and `_neg` restrict this to `𝓝[>] 0` / `𝓝[<] 0` and
rewrite the interval integral as a `Set.Ioc` integral on each side. -/
private lemma tendsto_average_integral_expZ_unitary_core {z : ℂ} (φ : H) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
            (𝓝[≠] 0) (𝓝 φ) := by
  have h_cont := expZ_orbit_continuous U_grp (z := z) φ
  have h_f0 : cexp (-(I * z * ((0 : ℝ) : ℂ))) • U_grp.U 0 φ = φ := by
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul]
    rw [U_grp.identity]
    simp only [ContinuousLinearMap.id_apply]
  have h_deriv : HasDerivAt (fun h => ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
                            (cexp (-(I * z * ((0 : ℝ) : ℂ))) • U_grp.U 0 φ) 0 := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact h_cont.intervalIntegrable 0 0
    · exact Continuous.stronglyMeasurableAtFilter h_cont volume (𝓝 0)
    · exact h_cont.continuousAt
  rw [h_f0] at h_deriv
  have h_F0 : ∫ t in (0 : ℝ)..0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ = 0 :=
    intervalIntegral.integral_same
  have := h_deriv.hasDerivWithinAt (s := Set.univ \ {0})
  rw [hasDerivWithinAt_iff_tendsto_slope] at this
  simp only [Set.diff_diff, Set.union_self] at this
  convert this using 1
  · ext h
    unfold slope
    simp only [sub_zero, h_F0, vsub_eq_sub]
  · congr 1
    exact Set.compl_eq_univ_diff {(0 : ℝ)}

/-- **Right-hand average** tends to the initial vector: `h⁻¹ ∫_{Ioc 0 h} e^{-izt}U(t)φ dt → φ`
as `h → 0⁺`. -/
lemma tendsto_average_integral_expZ_unitary {z : ℂ} (φ : H) :
    Tendsto (fun h : ℝ => (h⁻¹ : ℂ) • ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
            (𝓝[>] 0)
            (𝓝 φ) := by
  have h_eq : ∀ h > (0 : ℝ), ∫ t in Set.Ioc 0 h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                       ∫ t in (0 : ℝ)..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_restrict := (tendsto_average_integral_expZ_unitary_core U_grp (z := z) φ).mono_left
    (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, ← ofReal_inv, @Complex.coe_smul]

/-- **Left-hand average** tends to the initial vector: `(-h)⁻¹ ∫_{Ioc h 0} e^{-izt}U(t)φ dt → φ`
as `h → 0⁻`. -/
lemma tendsto_average_integral_expZ_unitary_neg {z : ℂ} (φ : H) :
    Tendsto (fun h : ℝ =>
        ((-h)⁻¹ : ℂ) • ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ)
            (𝓝[<] 0)
            (𝓝 φ) := by
  have h_eq : ∀ h < (0 : ℝ), ∫ t in Set.Ioc h 0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                       ∫ t in h..0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
    intro h hh
    rw [intervalIntegral.integral_of_le (le_of_lt hh)]
  have h_eq' : ∀ h < (0 : ℝ), ∫ t in h..0, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ =
                        -∫ t in 0..h, cexp (-(I * z * (t : ℂ))) • U_grp.U t φ := by
    intro h _
    rw [intervalIntegral.integral_symm]
  have h_restrict := (tendsto_average_integral_expZ_unitary_core U_grp (z := z) φ).mono_left
    (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
  apply Tendsto.congr' _ h_restrict
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [h_eq h hh, h_eq' h hh]
  rw [smul_neg]
  rw [← neg_smul]
  rw [(Complex.coe_smul h⁻¹ _).symm, ofReal_inv]
  congr 1
  rw [@neg_inv]
  simp_all only [neg_neg]

end Spectra.Resolvent

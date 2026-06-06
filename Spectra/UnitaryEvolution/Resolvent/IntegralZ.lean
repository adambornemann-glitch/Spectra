/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
Filename: UnitaryEvolution/Resolvent/IntegralZ.lean
-/
import Spectra.UnitaryEvolution.BochnerIntegration.Domain
import Spectra.UnitaryEvolution.Resolvent.Analytic

namespace QuantumMechanics.Bochner
open Complex MeasureTheory Filter Topology Resolvent
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- Resolvent integral at general `z` in the lower half-plane:
    `R(z)φ = (-i) ∫₀^∞ e^{-izt} U(t)φ dt`.  At `z = -i` this is `resolventIntegralPlus`. -/
noncomputable def resolventIntegralZ (z : ℂ) (φ : H) : H :=
  (-I) • ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ

/-- Integrability needs `Im z < 0`; bound `‖e^{-izt} • U(t)φ‖ = e^{(Im z)t} ‖φ‖ ≤ ‖φ‖`. -/
lemma integrable_expZ_unitary {z : ℂ} (hz : z.im < 0) (φ : H) :
    IntegrableOn (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (Set.Ici 0) := by
  -- ── two facts from the `OneParameterUnitaryGroup` API (supply the names) ──────
  have h_orbit_cont : Continuous (fun t : ℝ => U_grp.U t φ) := U_grp.strong_continuous φ
  have h_normU : ∀ t : ℝ, ‖U_grp.U t φ‖ ≤ ‖φ‖ := fun t => (norm_preserving U_grp t φ).le
  -- ── dominating function  ‖φ‖ · e^{(Im z)·t},  integrable since  Im z < 0 ──────
  have h_exp_int : IntegrableOn (fun t : ℝ => Real.exp (z.im * t)) (Set.Ici 0) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hz 0)
  have h_g_int : IntegrableOn (fun t : ℝ => ‖φ‖ * Real.exp (z.im * t)) (Set.Ici 0) volume :=
    h_exp_int.const_mul ‖φ‖
  -- ── measurability of the integrand ──────────────────────────────────────────
  have h_scalar_cont : Continuous (fun t : ℝ => cexp (-(I * z * (t : ℂ)))) := by
    apply Complex.continuous_exp.comp
    exact (Complex.continuous_ofReal.const_mul (I * z)).neg
  have h_meas : AEStronglyMeasurable
      (fun t : ℝ => cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) (volume.restrict (Set.Ici 0)) := by
    apply AEStronglyMeasurable.smul
    · exact h_scalar_cont.aestronglyMeasurable.restrict
    · exact h_orbit_cont.aestronglyMeasurable.restrict
  -- ── pointwise domination:  ‖integrand t‖ = e^{(Im z)·t} · ‖U(t)φ‖ ≤ g t ──────
  have h_bound : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Ici (0 : ℝ))),
      ‖cexp (-(I * z * (t : ℂ))) • U_grp.U t φ‖ ≤ ‖φ‖ * Real.exp (z.im * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t _ht
    rw [norm_smul, Complex.norm_exp]
    have h_re : (-(I * z * (t : ℂ))).re = z.im * t := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                 Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [h_re]
    calc Real.exp (z.im * t) * ‖U_grp.U t φ‖
        ≤ Real.exp (z.im * t) * ‖φ‖ :=
          mul_le_mul_of_nonneg_left (h_normU t) (Real.exp_pos _).le
      _ = ‖φ‖ * Real.exp (z.im * t) := mul_comm _ _
  exact Integrable.mono' h_g_int h_meas h_bound

/-- The shift lemma, generalizing `unitary_apply_Ici_orbit_integral_plus`:
    the prefactor `e^h` becomes `e^{izh}`. -/
lemma unitary_apply_expZ_integral {z : ℂ} (hz : z.im < 0) (φ : H) (h : ℝ) :
    U_grp.U h (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) =
      cexp (I * z * (h : ℂ)) • ∫ s in Set.Ici h, cexp (-(I * z * (s : ℂ))) • U_grp.U s φ := by
  have h_int := integrable_expZ_unitary U_grp hz φ
  -- (1) push U(h) through the Bochner integral
  have h_comm : U_grp.U h (∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) =
                ∫ t in Set.Ici (0 : ℝ), U_grp.U h (cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) :=
    ((U_grp.U h).integral_comp_comm h_int).symm
  -- (2) group law:  U(h)(e^{-izt} • U(t)φ) = e^{-izt} • U(t+h)φ
  have h_shift : ∀ t : ℝ, U_grp.U h (cexp (-(I * z * (t : ℂ))) • U_grp.U t φ) =
                      cexp (-(I * z * (t : ℂ))) • U_grp.U (t + h) φ := by
    intro t
    have hlaw := U_grp.group_law h t
    rw [add_comm] at hlaw
    rw [hlaw, ContinuousLinearMap.comp_apply]
    exact map_smul (U_grp.U h) _ _
  -- (3) split the prefactor:  e^{-izt} = e^{izh} · e^{-iz(t+h)}
  have h_exp : ∀ t : ℝ, cexp (-(I * z * (t : ℂ))) • U_grp.U (t + h) φ =
                    cexp (I * z * (h : ℂ)) •
                      (cexp (-(I * z * ((t + h : ℝ) : ℂ))) • U_grp.U (t + h) φ) := by
    intro t
    rw [← smul_assoc]
    congr 1
    rw [smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h_comm]
  simp_rw [h_shift]
  simp_rw [h_exp]
  rw [integral_smul]
  -- (4) translation  s = t + h :  ∫_{[0,∞)} f(t+h) dt = ∫_{[h,∞)} f(s) ds
  have h_subst :
      ∫ t in Set.Ici (0 : ℝ), cexp (-(I * z * ((t + h : ℝ) : ℂ))) • U_grp.U (t + h) φ =
      ∫ s in Set.Ici h, cexp (-(I * z * (s : ℂ))) • U_grp.U s φ := by
    have hmp : MeasurePreserving (· + h) (volume : Measure ℝ) volume :=
      measurePreserving_add_right volume h
    have hme : MeasurableEmbedding (· + h : ℝ → ℝ) :=
      (Homeomorph.addRight h).isClosedEmbedding.measurableEmbedding
    have hpre : (· + h) ⁻¹' (Set.Ici h) = Set.Ici (0 : ℝ) := by
      ext t; simp only [Set.mem_preimage, Set.mem_Ici]
      constructor <;> intro ht <;> linarith
    have key := hmp.setIntegral_preimage_emb hme
      (fun s => cexp (-(I * z * (s : ℂ))) • U_grp.U s φ) (Set.Ici h)
    rw [hpre] at key
    exact key
  rw [h_subst]

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


/-- The difference-quotient limit lands on `z • R(z)φ + φ`.
    Cross-check: at `z = -i` this is `-i • R₊ + φ = φ - I • resolventIntegralPlus`,
    exactly `generator_limit_resolventIntegralPlus`. -/
lemma generator_limit_resolventIntegralZ {z : ℂ} (hz : z.im < 0) (φ : H) :
    Tendsto (fun h : ℝ => ((I * h)⁻¹ : ℂ) •
        (U_grp.U h (resolventIntegralZ U_grp z φ) - resolventIntegralZ U_grp z φ))
      (𝓝[≠] 0) (𝓝 (z • resolventIntegralZ U_grp z φ + φ)) := by
  sorry  -- Ioi/Iio split + bulk/boundary tendsto, as in `Plus.lean`;
         -- (e^{izh}-1)/(I h) → z gives the `z • _` term; the boundary average gives `+ φ`

/-- Hence `(A - z)` sends the integral to `φ`, so it IS the resolvent. -/
theorem resolventIntegralZ_eq_resolvent {z : ℂ} (hz : z.im < 0) (φ : H) :
    resolventIntegralZ U_grp z φ
      = Resolvent.resolvent z (ne_of_lt hz)
          (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) φ := by
  -- membership + generator value from `generatorDomain_maximal` + `generator_tendsto`
  -- + `generator_limit_resolventIntegralZ`, giving  A J - z • J = φ;
  -- then `solution_unique` against `self_adjoint_range_all_z`.
  sorry

end QuantumMechanics.Bochner

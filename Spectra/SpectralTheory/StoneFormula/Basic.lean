/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Resolvent.SpectralRepresentation
import Spectra.Kernel.Arctan
import Spectra.Resolvent.Diagonal.Basic
import Spectra.QuantumMechanics.DiracEquation.Operators
/-!
# Stone's Formula

Recovery of the spectral projections from boundary values of the resolvent:

  `E((a,b)) + ½E({a}) + ½E({b}) = s-lim_{ε→0⁺} (1/2πi) ∫_a^b [R(t+iε) − R(t−iε)] dt`.

## Proof shape

1. **Symbol**: `stoneSymbol a b ε := (1/π)(arctan((b−·)/ε) − arctan((a−·)/ε))`, the
   `λ`-average of the Poisson kernel; uniformly bounded by `1`, pointwise convergent
   *everywhere* to the averaged indicator `1_{(a,b)} + ½1_{{a}} + ½1_{{b}}`
   (`arctan_kernel_pointwise_limit` — the endpoint halves are why the statement carries
   averaged atoms).
2. **Limit**: `tendsto_spectralCalculus_apply` along `𝓝[>] 0` (countably generated)
   gives `Φ(stoneSymbol ε)ξ → Φ(limit)ξ` in `H`; the calculus algebra rewrites
   `Φ(limit)` as the projection combination (`spectralCalculus_stoneLimit`).
3. **Identification**: `⟪ξ, Φ(stoneSymbol ε)ξ⟫ = (1/2πi) ∫_a^b ⟪ξ,(R₊−R₋)ξ⟫ dt` via
   `spectralForm_self`, the real Fubini, and `lorentzian_arctan_integral`.

## References

* [Reed, Simon, *Methods of Modern Mathematical Physics I*][reed1980], Theorem VII.13
* Stone, "Linear Transformations in Hilbert Space" (1932)
-/
open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Borel
open SpectralMeasure
open Spectra.Kernels
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.OneParameterUnitaryGroup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## The averaged indicator and the arctan kernel limit -/

/-- The pointwise limit of the arctan kernel: `1` strictly inside `(a, b)`, `½` at the
endpoints, `0` outside. -/
noncomputable def averagedIndicator (a b : ℝ) : ℝ → ℝ :=
  fun s => if s < a then 0
    else if s = a then 1 / 2
    else if s < b then 1
    else if s = b then 1 / 2
    else 0

/-- The arctan kernel converges pointwise *everywhere* to the averaged indicator —
the endpoint cases (`arctan 0 = 0` against `arctan(±∞) = ±π/2`) produce the halves. -/
lemma arctan_kernel_pointwise_limit (a b s : ℝ) (hab : a < b) :
    Tendsto (fun ε : ℝ => (1 / Real.pi) *
      (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)))
      (𝓝[>] 0) (𝓝 (averagedIndicator a b s)) := by
  unfold averagedIndicator
  have _hπ := Real.pi_pos
  have arc_pos : ∀ c : ℝ, 0 < c →
      Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (Real.pi / 2)) :=
    fun c hc => (Real.tendsto_arctan_atTop.comp
      (tendsto_pos_div_zero_atTop hc)).mono_right nhdsWithin_le_nhds
  have arc_neg : ∀ c : ℝ, c < 0 →
      Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (-(Real.pi / 2))) :=
    fun c hc => (Real.tendsto_arctan_atBot.comp
      (tendsto_neg_div_zero_atBot hc)).mono_right nhdsWithin_le_nhds
  split_ifs with h1 h2 h3 h4
  · -- s < a: both arctans → π/2, difference → 0
    have := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((arc_pos _ (by linarith : 0 < b - s)).sub (arc_pos _ (by linarith : 0 < a - s)))
    simp only [sub_self, mul_zero] at this; exact this
  · -- s = a: arctan(0) = 0 against arctan(+∞) = π/2
    simp only [h2, sub_self, zero_div, Real.arctan_zero, sub_zero]
    have := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      (arc_pos _ (by linarith : 0 < b - a))
    rwa [show (1 / Real.pi) * (Real.pi / 2) = 1 / 2 from by field_simp] at this
  · -- a < s < b: difference → π/2 − (−π/2) = π
    have hsa : a < s := by
      rcases (not_lt.mp h1).eq_or_lt with h | h
      · exact absurd h.symm h2
      · exact h
    have := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((arc_pos _ (by linarith : 0 < b - s)).sub (arc_neg _ (by linarith : a - s < 0)))
    simp only [sub_neg_eq_add, add_halves] at this
    rwa [show (1 / Real.pi) * Real.pi = 1 from by field_simp] at this
  · -- s = b: arctan(0) = 0 against arctan(−∞) = −π/2
    simp only [h4, sub_self, zero_div, Real.arctan_zero, zero_sub]
    have := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      (arc_neg _ (by linarith : a - b < 0)).neg
    simp only [neg_neg] at this
    rwa [show (1 / Real.pi) * (Real.pi / 2) = 1 / 2 from by field_simp] at this
  · -- s > b: both arctans → −π/2, difference → 0
    have hsb : b < s := by
      rcases (not_lt.mp h3).eq_or_lt with h | h
      · exact absurd h.symm h4
      · exact h
    have := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((arc_neg _ (by linarith : b - s < 0)).sub (arc_neg _ (by linarith : a - s < 0)))
    simp only [sub_self, mul_zero] at this; exact this

/-- The arctan kernel is bounded by `1` for ALL `ε` (no sign condition — needed because
the DCT engine quantifies the uniform bound over the whole index type). -/
lemma arctan_kernel_abs_le_one (a b s ε : ℝ) :
    |(1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε))| ≤ 1 := by
  have _hπ_pos := Real.pi_pos
  have h_diff : |Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)| ≤ Real.pi := by
    rw [abs_le]
    constructor <;>
      linarith [Real.neg_pi_div_two_lt_arctan ((b - s) / ε),
        Real.arctan_lt_pi_div_two ((b - s) / ε),
        Real.neg_pi_div_two_lt_arctan ((a - s) / ε),
        Real.arctan_lt_pi_div_two ((a - s) / ε)]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  calc (1 / Real.pi) * |Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)|
      ≤ (1 / Real.pi) * Real.pi := by
        exact mul_le_mul_of_nonneg_left h_diff (by positivity)
    _ = 1 := by field_simp

/-! ## The Stone symbol -/

/-- The Stone symbol: the `λ`-average of the Poisson kernel over `[a, b]`, as a bounded
measurable ℂ-valued symbol for the calculus. -/
noncomputable def stoneSymbol (a b ε : ℝ) : ℝ → ℂ := fun s =>
  (((1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) : ℝ) : ℂ)

lemma stoneSymbol_measurable (a b ε : ℝ) : Measurable (stoneSymbol a b ε) :=
  Complex.measurable_ofReal.comp
    ((continuous_const.mul
      ((Real.continuous_arctan.comp ((continuous_const.sub continuous_id).div_const ε)).sub
        (Real.continuous_arctan.comp
          ((continuous_const.sub continuous_id).div_const ε)))).measurable)

lemma stoneSymbol_norm_le_one (a b ε : ℝ) (s : ℝ) : ‖stoneSymbol a b ε s‖ ≤ 1 := by
  rw [show stoneSymbol a b ε s
      = (((1 / Real.pi) * (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) : ℝ) : ℂ)
    from rfl, Complex.norm_real, Real.norm_eq_abs]
  exact arctan_kernel_abs_le_one a b s ε

lemma stoneSymbol_bdd (a b ε : ℝ) : ∃ C, ∀ s, ‖stoneSymbol a b ε s‖ ≤ C :=
  ⟨1, stoneSymbol_norm_le_one a b ε⟩

/-! ## The limit symbol -/

/-- The limit symbol: the complexified averaged indicator. -/
noncomputable def stoneLimit (a b : ℝ) : ℝ → ℂ :=
  fun s => ((averagedIndicator a b s : ℝ) : ℂ)

/-- The limit symbol as an indicator combination — the form the calculus algebra
consumes.  Needs `a < b` (at `a = b` the two endpoint halves would collide). -/
lemma stoneLimit_eq_indicators (a b : ℝ) (hab : a < b) :
    stoneLimit a b = fun s : ℝ =>
      Set.indicator (Set.Ioo a b) (fun _ => (1 : ℂ)) s
        + ((1 / 2 : ℂ) * Set.indicator {a} (fun _ => (1 : ℂ)) s
            + (1 / 2 : ℂ) * Set.indicator {b} (fun _ => (1 : ℂ)) s) := by
  classical
  funext s
  unfold stoneLimit averagedIndicator
  simp only [Set.indicator_apply, Set.mem_Ioo, Set.mem_singleton_iff]
  rcases lt_trichotomy s a with hsa | rfl | hsa
  · norm_num [hsa, hsa.ne, not_lt.mpr hsa.le, (hsa.trans hab).ne]
  · norm_num [hab.ne]
  · rcases lt_trichotomy s b with hsb | rfl | hsb
    · norm_num [not_lt.mpr hsa.le, hsa.ne', hsb, hsb.ne, hsa]
    · norm_num [not_lt.mpr hab.le, hab.ne']
    · norm_num [not_lt.mpr (hab.trans hsb).le, (hab.trans hsb).ne',
        not_lt.mpr hsb.le, hsb.ne']

lemma stoneLimit_measurable (a b : ℝ) (hab : a < b) : Measurable (stoneLimit a b) := by
  rw [stoneLimit_eq_indicators a b hab]
  exact (measurable_const.indicator measurableSet_Ioo).add
    ((measurable_const.mul (measurable_const.indicator (measurableSet_singleton a))).add
      (measurable_const.mul (measurable_const.indicator (measurableSet_singleton b))))

lemma stoneLimit_bdd (a b : ℝ) : ∃ C, ∀ s, ‖stoneLimit a b s‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  change ‖((averagedIndicator a b s : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold averagedIndicator
  split_ifs <;> norm_num

/-- Pointwise convergence of the Stone symbol to the limit symbol — the complexified
`arctan_kernel_pointwise_limit`. -/
lemma stoneSymbol_tendsto (a b : ℝ) (hab : a < b) (s : ℝ) :
    Tendsto (fun ε : ℝ => stoneSymbol a b ε s) (𝓝[>] 0) (𝓝 (stoneLimit a b s)) := by
  have h := (Complex.continuous_ofReal.tendsto (averagedIndicator a b s)).comp
    (arctan_kernel_pointwise_limit a b s hab)
  exact h.congr fun ε => rfl

/-- **The calculus of the limit symbol is the projection combination**:
`Φ(stoneLimit) = E((a,b)) + ½E({a}) + ½E({b})`. -/
lemma spectralCalculus_stoneLimit (a b : ℝ) (hab : a < b) :
    spectralCalculus U_grp (stoneLimit a b)
        (stoneLimit_measurable a b hab) (stoneLimit_bdd a b)
      = spectralProjection U_grp (Set.Ioo a b) measurableSet_Ioo
        + ((1 / 2 : ℂ) • spectralProjection U_grp {a} (measurableSet_singleton a)
            + (1 / 2 : ℂ) • spectralProjection U_grp {b} (measurableSet_singleton b)) := by
  have hm_a : Measurable fun s : ℝ =>
      (1 / 2 : ℂ) * Set.indicator {a} (fun _ => (1 : ℂ)) s :=
    measurable_const.mul (measurable_const.indicator (measurableSet_singleton a))
  have hb_a : ∃ C, ∀ s : ℝ, ‖(1 / 2 : ℂ) * Set.indicator {a} (fun _ => (1 : ℂ)) s‖ ≤ C :=
    bounded_mul ⟨‖(1 / 2 : ℂ)‖, fun _ => le_rfl⟩ (indicator_one_bdd _)
  have hm_b : Measurable fun s : ℝ =>
      (1 / 2 : ℂ) * Set.indicator {b} (fun _ => (1 : ℂ)) s :=
    measurable_const.mul (measurable_const.indicator (measurableSet_singleton b))
  have hb_b : ∃ C, ∀ s : ℝ, ‖(1 / 2 : ℂ) * Set.indicator {b} (fun _ => (1 : ℂ)) s‖ ≤ C :=
    bounded_mul ⟨‖(1 / 2 : ℂ)‖, fun _ => le_rfl⟩ (indicator_one_bdd _)
  have hm_ab : Measurable fun s : ℝ =>
      (1 / 2 : ℂ) * Set.indicator {a} (fun _ => (1 : ℂ)) s
        + (1 / 2 : ℂ) * Set.indicator {b} (fun _ => (1 : ℂ)) s := hm_a.add hm_b
  have hb_ab : ∃ C, ∀ s : ℝ,
      ‖(1 / 2 : ℂ) * Set.indicator {a} (fun _ => (1 : ℂ)) s
        + (1 / 2 : ℂ) * Set.indicator {b} (fun _ => (1 : ℂ)) s‖ ≤ C :=
    bounded_add hb_a hb_b
  have hm_sum : Measurable fun s : ℝ =>
      Set.indicator (Set.Ioo a b) (fun _ => (1 : ℂ)) s
        + ((1 / 2 : ℂ) * Set.indicator {a} (fun _ => (1 : ℂ)) s
            + (1 / 2 : ℂ) * Set.indicator {b} (fun _ => (1 : ℂ)) s) :=
    (measurable_const.indicator measurableSet_Ioo).add hm_ab
  have hb_sum : ∃ C, ∀ s : ℝ,
      ‖Set.indicator (Set.Ioo a b) (fun _ => (1 : ℂ)) s
        + ((1 / 2 : ℂ) * Set.indicator {a} (fun _ => (1 : ℂ)) s
            + (1 / 2 : ℂ) * Set.indicator {b} (fun _ => (1 : ℂ)) s)‖ ≤ C :=
    bounded_add (indicator_one_bdd _) hb_ab
  rw [spectralCalculus_congr U_grp (stoneLimit_eq_indicators a b hab)
      (stoneLimit_measurable a b hab) (stoneLimit_bdd a b) hm_sum hb_sum,
    spectralCalculus_add U_grp _ _ (measurable_const.indicator measurableSet_Ioo)
      (indicator_one_bdd _) hm_ab hb_ab hm_sum hb_sum,
    spectralCalculus_add U_grp _ _ hm_a hb_a hm_b hb_b hm_ab hb_ab,
    spectralCalculus_smul U_grp (1 / 2 : ℂ) _
      (measurable_const.indicator (measurableSet_singleton a)) (indicator_one_bdd _)
      hm_a hb_a,
    spectralCalculus_smul U_grp (1 / 2 : ℂ) _
      (measurable_const.indicator (measurableSet_singleton b)) (indicator_one_bdd _)
      hm_b hb_b]
  rfl

/-! ## Stone's formula, strong form -/

/-- **Stone's Formula, strong form.**  The Stone symbols converge through the calculus,
in the norm of `H`, to the averaged spectral projection:

  `Φ(S_ε)ξ → (E((a,b)) + ½E({a}) + ½E({b}))ξ`  as `ε → 0⁺`.

One application of the dominated-convergence engine `tendsto_spectralCalculus_apply`
along `𝓝[>] 0`, with uniform bound `1`. -/
theorem stonesFormula (a b : ℝ) (hab : a < b) (ξ : H) :
    Tendsto (fun ε : ℝ =>
        spectralCalculus U_grp (stoneSymbol a b ε)
          (stoneSymbol_measurable a b ε) (stoneSymbol_bdd a b ε) ξ)
      (𝓝[>] 0)
      (𝓝 ((spectralProjection U_grp (Set.Ioo a b) measurableSet_Ioo
            + ((1 / 2 : ℂ) • spectralProjection U_grp {a} (measurableSet_singleton a)
                + (1 / 2 : ℂ) • spectralProjection U_grp {b}
                    (measurableSet_singleton b))) ξ)) := by
  have hconv := tendsto_spectralCalculus_apply U_grp
    (G := fun ε : ℝ => stoneSymbol a b ε) (g := stoneLimit a b)
    (fun ε => stoneSymbol_measurable a b ε) (fun ε => stoneSymbol_bdd a b ε)
    (stoneLimit_measurable a b hab) (stoneLimit_bdd a b)
    (fun ε s => stoneSymbol_norm_le_one a b ε s)
    (fun s => stoneSymbol_tendsto a b hab s) ξ
  rwa [spectralCalculus_stoneLimit U_grp a b hab] at hconv

/-- Stone's formula with no spectral mass at the endpoints: the limit is exactly
`E((a,b))ξ`. -/
theorem stonesFormula_of_measure_atom_zero (a b : ℝ) (hab : a < b) (ξ : H)
    (ha : borelMeasure U_grp ξ {a} = 0) (hb : borelMeasure U_grp ξ {b} = 0) :
    Tendsto (fun ε : ℝ =>
        spectralCalculus U_grp (stoneSymbol a b ε)
          (stoneSymbol_measurable a b ε) (stoneSymbol_bdd a b ε) ξ)
      (𝓝[>] 0)
      (𝓝 (spectralProjection U_grp (Set.Ioo a b) measurableSet_Ioo ξ)) := by
  have hEa : spectralProjection U_grp {a} (measurableSet_singleton a) ξ = 0 :=
    (spectralProjection_eq_zero_iff_measure_zero U_grp {a}
      (measurableSet_singleton a) ξ).mpr ha
  have hEb : spectralProjection U_grp {b} (measurableSet_singleton b) ξ = 0 :=
    (spectralProjection_eq_zero_iff_measure_zero U_grp {b}
      (measurableSet_singleton b) ξ).mpr hb
  have h := stonesFormula U_grp a b hab ξ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    hEa, hEb, smul_zero, smul_zero, add_zero, add_zero] at h
  exact h

/-! ## Identification with the resolvent integral -/

/-- The diagonal of the resolvent difference, via conjugation symmetry — no kernel
identity:  `⟪ξ, (R(t+iε) − R(t−iε))ξ⟫ = 2i · ∫ ε/((s−t)² + ε²) dμ_ξ(s)`. -/
lemma inner_resolvent_diff_diag (t : ℝ) {ε : ℝ} (hε : 0 < ε) (ξ : H) :
    ⟪ξ, (resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)
        - resolvent (⟨t, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne')
            (generator_isFormalAdjoint U_grp)
            (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)) ξ⟫_ℂ
      = 2 * I * ((∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂(borelMeasure U_grp ξ) : ℝ) : ℂ) := by
  rw [ContinuousLinearMap.sub_apply, inner_sub_right]
  have h_minus : ⟪ξ, resolvent (⟨t, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne')
        (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ
      = starRingEnd ℂ ⟪ξ, resolvent (⟨t, ε⟩ : ℂ) hε.ne'
          (generator_isFormalAdjoint U_grp)
          (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ := by
    rw [inner_resolvent_diag_eq_integral U_grp (⟨t, -ε⟩ : ℂ)
        (neg_ne_zero.mpr hε.ne') ξ,
      inner_resolvent_diag_eq_integral U_grp (⟨t, ε⟩ : ℂ) hε.ne' ξ,
      ← integral_conj]
    refine integral_congr_ae (.of_forall fun s => ?_)
    simp only [map_inv₀, map_sub, Complex.conj_ofReal]
    congr 2
  rw [h_minus, Complex.sub_conj, im_inner_resolvent_diag U_grp t hε ξ]
  push_cast
  ring

/-- Real Fubini for the Lorentzian kernel against a finite measure. -/
lemma lorentzian_fubini {μ : Measure ℝ} [IsFiniteMeasure μ] (a b : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ t in Set.Icc a b, ∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂μ
      = ∫ s, (∫ t in Set.Icc a b, ε / ((s - t) ^ 2 + ε ^ 2)) ∂μ := by
  set ν := volume.restrict (Set.Icc a b) with hν
  haveI : IsFiniteMeasure ν := ⟨by
    simp only [hν, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact isCompact_Icc.measure_lt_top⟩
  have h_cont : Continuous (fun p : ℝ × ℝ => ε / ((p.2 - p.1) ^ 2 + ε ^ 2)) := by
    apply continuous_const.div
    · exact ((continuous_snd.sub continuous_fst).pow 2).add continuous_const
    · intro p; positivity
  have h_bound : ∀ p : ℝ × ℝ, ‖ε / ((p.2 - p.1) ^ 2 + ε ^ 2)‖ ≤ 1 / ε := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h_denom : ε ^ 2 ≤ (p.2 - p.1) ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg (p.2 - p.1)]
    calc ε / ((p.2 - p.1) ^ 2 + ε ^ 2)
        ≤ ε / ε ^ 2 := div_le_div_of_nonneg_left hε.le (by positivity) h_denom
      _ = 1 / ε := by rw [pow_two, ← div_div, div_self hε.ne']
  have h_int : Integrable (fun p : ℝ × ℝ => ε / ((p.2 - p.1) ^ 2 + ε ^ 2)) (ν.prod μ) :=
    (memLp_top_of_bound h_cont.aestronglyMeasurable (1 / ε)
      (Filter.Eventually.of_forall h_bound)).integrable le_top
  exact integral_integral_swap h_int

/-- The Lorentzian's `λ`-integral over `Icc` is the arctan difference — the `Icc`
set-integral form of `lorentzian_arctan_integral`. -/
lemma setIntegral_Icc_lorentzian (s a b ε : ℝ) (hab : a ≤ b) (hε : 0 < ε) :
    ∫ t in Set.Icc a b, ε / ((s - t) ^ 2 + ε ^ 2)
      = Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε) := by
  rw [show (∫ t in Set.Icc a b, ε / ((s - t) ^ 2 + ε ^ 2))
        = ∫ t in a..b, ε / ((s - t) ^ 2 + ε ^ 2) from by
      rw [intervalIntegral.integral_of_le hab]
      exact integral_Icc_eq_integral_Ioc]
  exact lorentzian_arctan_integral s a b ε hε

/-- **The identification**: the diagonal of the Stone symbol through the calculus is the
classical resolvent-difference integral,

  `⟪ξ, Φ(S_ε)ξ⟫ = (1/2πi) ∫_{[a,b]} ⟪ξ, (R(t+iε) − R(t−iε))ξ⟫ dt`. -/
lemma inner_stoneSymbol_eq_resolvent_integral (a b : ℝ) (hab : a ≤ b) {ε : ℝ}
    (hε : 0 < ε) (ξ : H) :
    ⟪ξ, spectralCalculus U_grp (stoneSymbol a b ε)
        (stoneSymbol_measurable a b ε) (stoneSymbol_bdd a b ε) ξ⟫_ℂ
      = (1 / (2 * Real.pi * I)) * ∫ t in Set.Icc a b,
          ⟪ξ, (resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp)
                (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)
              - resolvent (⟨t, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne')
                  (generator_isFormalAdjoint U_grp)
                  (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)) ξ⟫_ℂ := by
  set μ := borelMeasure U_grp ξ with _hμ_def
  haveI : IsFiniteMeasure μ := borelMeasure_isFiniteMeasure U_grp ξ
  -- LHS: the calculus diagonal is the spectral integral of the symbol.
  rw [inner_spectralCalculus, spectralForm_self U_grp ξ
    (stoneSymbol_measurable a b ε) (stoneSymbol_bdd a b ε)]
  unfold stoneSymbol
  rw [integral_complex_ofReal]
  -- RHS: collapse to the same real double integral.
  symm
  calc (1 / (2 * Real.pi * I)) * ∫ t in Set.Icc a b,
        ⟪ξ, (resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp)
              (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)
            - resolvent (⟨t, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne')
                (generator_isFormalAdjoint U_grp)
                (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)) ξ⟫_ℂ
      = (1 / (2 * Real.pi * I)) * ∫ t in Set.Icc a b,
          2 * I * ((∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂μ : ℝ) : ℂ) := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Icc fun t _ =>
          inner_resolvent_diff_diag U_grp t hε ξ
    _ = (1 / (2 * Real.pi * I)) * (2 * I *
          ∫ t in Set.Icc a b, ((∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂μ : ℝ) : ℂ)) := by
        rw [integral_const_mul]
    _ = (1 / (2 * Real.pi * I)) * (2 * I *
          ((∫ t in Set.Icc a b, ∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂μ : ℝ) : ℂ)) := by
        rw [integral_complex_ofReal]
    _ = (((1 / Real.pi) *
          ∫ t in Set.Icc a b, ∫ s, ε / ((s - t) ^ 2 + ε ^ 2) ∂μ : ℝ) : ℂ) := by
        push_cast
        have hI : (I : ℂ) ≠ 0 := I_ne_zero
        have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
        field_simp
    _ = (((1 / Real.pi) *
          ∫ s, (∫ t in Set.Icc a b, ε / ((s - t) ^ 2 + ε ^ 2)) ∂μ : ℝ) : ℂ) := by
        rw [lorentzian_fubini a b hε]
    _ = (((1 / Real.pi) *
          ∫ s, (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ : ℝ) : ℂ) := by
        rw [show (∫ s, (∫ t in Set.Icc a b, ε / ((s - t) ^ 2 + ε ^ 2)) ∂μ)
              = ∫ s, (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ from
            integral_congr_ae (.of_forall fun s =>
              setIntegral_Icc_lorentzian s a b ε hab hε)]
    _ = ((∫ s, (1 / Real.pi) *
          (Real.arctan ((b - s) / ε) - Real.arctan ((a - s) / ε)) ∂μ : ℝ) : ℂ) :=
        congrArg Complex.ofReal (integral_const_mul _ _).symm

/-! ## Stone's formula, classical bilinear form -/

/-- **Stone's Formula, classical form.**  For every `ξ`,

  `(1/2πi) ∫_a^b ⟪ξ, (R(t+iε) − R(t−iε))ξ⟫ dt
      → ⟪ξ, (E((a,b)) + ½E({a}) + ½E({b}))ξ⟫`  as `ε → 0⁺`.

Continuity of the inner product applied to the strong form, plus the identification. -/
theorem stonesFormula_inner (a b : ℝ) (hab : a < b) (ξ : H) :
    Tendsto (fun ε : ℝ => if hε : 0 < ε then
        (1 / (2 * Real.pi * I)) * ∫ t in Set.Icc a b,
          ⟪ξ, (resolvent (⟨t, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp)
                (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)
              - resolvent (⟨t, -ε⟩ : ℂ) (neg_ne_zero.mpr hε.ne')
                  (generator_isFormalAdjoint U_grp)
                  (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp)) ξ⟫_ℂ
      else 0)
      (𝓝[>] 0)
      (𝓝 ⟪ξ, (spectralProjection U_grp (Set.Ioo a b) measurableSet_Ioo
            + ((1 / 2 : ℂ) • spectralProjection U_grp {a} (measurableSet_singleton a)
                + (1 / 2 : ℂ) • spectralProjection U_grp {b}
                    (measurableSet_singleton b))) ξ⟫_ℂ) := by
  have h := (tendsto_const_nhds (x := ξ)).inner (𝕜 := ℂ)
    (stonesFormula U_grp a b hab ξ)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [dif_pos hε]
  exact inner_stoneSymbol_eq_resolvent_integral U_grp a b hab.le hε ξ

end Spectra.Resolvent

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Convolution
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Young's convolution inequality `L¹ ⋆ L² → L²`

Mathlib provides the scalar Young inequality and the `L¹ ⋆ L¹ → L¹` convolution result, but not
the mixed `L¹ ⋆ L² → L²` estimate. This file supplies it on `ℝ³` (brick **M4** of the Coulomb
relative-compactness program): if `f ∈ L¹` and `g ∈ L²` then `f ⋆ g ∈ L²` with
`‖f ⋆ g‖₂ ≤ ‖f‖₁ · ‖g‖₂`.

The proof is the direct weighted-Cauchy–Schwarz argument carried out entirely in `ℝ≥0∞`
(`enorm`/`lintegral`), avoiding the general Minkowski integral inequality (absent from Mathlib):

* the pointwise bound `‖(f ⋆ g) x‖ₑ ≤ H x := ∫⁻ t, ‖f t‖ₑ · ‖g (x − t)‖ₑ`
  (`enorm_integral_le_lintegral_enorm`);
* weighted Cauchy–Schwarz (`ENNReal.lintegral_mul_le_Lp_mul_Lq`, `p = q = 2`):
  `(H x)² ≤ ‖f‖₁ · ∫⁻ t, ‖f t‖ₑ · ‖g (x − t)‖ₑ²`;
* Tonelli (`lintegral_lintegral_swap`) + translation invariance
  (`lintegral_sub_right_eq_self`) ⟹ `∫⁻ x, (H x)² ≤ ‖f‖₁² · ‖g‖₂²`.

This is the controlling estimate for the singular convolution theorem (brick M6): it bounds
`‖(G_z − G_z^{(ε)}) ⋆ h‖₂ ≤ ‖G_z − G_z^{(ε)}‖₁ · ‖h‖₂` in the kernel-mollification limit.
-/

open MeasureTheory ENNReal ContinuousLinearMap
open scoped ENNReal NNReal Convolution

noncomputable section

namespace Spectra.CompactOperator

/-- **Young's convolution inequality, `L¹ ⋆ L² → L²` case** (on `ℝ³`).
If `f ∈ L¹` and `g ∈ L²` then their convolution `f ⋆ g` lies in `L²` and
`‖f ⋆ g‖₂ ≤ ‖f‖₁ · ‖g‖₂`. -/
theorem young_L1_conv_L2 {f g : (EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hf : MemLp f 1 volume) (hg : MemLp g 2 volume) :
    MemLp (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) 2 volume ∧
      eLpNorm (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) 2 volume
        ≤ eLpNorm f 1 volume * eLpNorm g 2 volume := by
  set μ : Measure (EuclideanSpace ℝ (Fin 3)) := volume with hμ
  -- abbreviations
  set H : (EuclideanSpace ℝ (Fin 3)) → ℝ≥0∞ :=
    fun x => ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ with hH
  set F1 : ℝ≥0∞ := ∫⁻ t, ‖f t‖ₑ ∂μ with hF1
  set G2 : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ ^ (2 : ℝ) ∂μ with hG2
  have hf_aem : AEMeasurable (fun t => ‖f t‖ₑ) μ := hf.aestronglyMeasurable.enorm
  -- AEStronglyMeasurable of the convolution (measurability half of `MemLp`)
  have haem : AEStronglyMeasurable (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) μ :=
    (hf.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
      hg.aestronglyMeasurable).integral_prod_right'
  -- `‖f‖₁` and `‖g‖₂` as lintegrals
  have hF1eq : eLpNorm f 1 μ = F1 := by rw [eLpNorm_one_eq_lintegral_enorm]
  have hG2eq : eLpNorm g 2 μ = G2 ^ (1 / (2:ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, hG2, one_div]
  -- finiteness
  have hF1_lt : F1 < ∞ := by rw [← hF1eq]; exact hf.eLpNorm_lt_top
  have hG2_lt : G2 < ∞ := by
    have hlt := hg.eLpNorm_lt_top
    rw [hG2eq] at hlt
    by_contra h
    rw [top_le_iff.mp (not_lt.mp h)] at hlt
    simp [ENNReal.top_rpow_of_pos] at hlt
  -- STEP 1: pointwise enorm bound `‖(f⋆g) x‖ₑ ≤ H x`
  have hstep1 : ∀ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x‖ₑ ≤ H x := by
    intro x
    rw [convolution_mul]
    calc ‖∫ t, f t * g (x - t) ∂μ‖ₑ
        ≤ ∫⁻ t, ‖f t * g (x - t)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂μ := by simp_rw [enorm_mul]
  -- Hölder conjugate `(2,2)`
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  -- STEP 3: pointwise weighted Cauchy–Schwarz `(H x)² ≤ F1 · ∫ ‖f t‖ · ‖g(x-t)‖²`
  have hstep3 : ∀ x, (H x) ^ (2 : ℝ)
      ≤ F1 * ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ (2 : ℝ) ∂μ := by
    intro x
    set u : (EuclideanSpace ℝ (Fin 3)) → ℝ≥0∞ := fun t => ‖f t‖ₑ ^ ((1:ℝ)/2) with hu
    set v : (EuclideanSpace ℝ (Fin 3)) → ℝ≥0∞ :=
      fun t => ‖f t‖ₑ ^ ((1:ℝ)/2) * ‖g (x - t)‖ₑ with hv
    have hfactor : ∀ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ = u t * v t := by
      intro t
      simp only [hu, hv]
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have hHx : H x = ∫⁻ t, u t * v t ∂μ := by
      simp only [hH]; exact lintegral_congr (fun t => hfactor t)
    have hu_aem : AEMeasurable u μ := (hf_aem.pow_const _)
    have hg_shift : AEStronglyMeasurable (fun t => g (x - t)) μ :=
      hg.aestronglyMeasurable.comp_measurePreserving (Measure.measurePreserving_sub_left μ x)
    have hv_aem : AEMeasurable v μ := (hf_aem.pow_const _).mul hg_shift.enorm
    have hcs : (∫⁻ t, u t * v t ∂μ)
        ≤ (∫⁻ t, u t ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) * (∫⁻ t, v t ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ)) := by
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hu_aem hv_aem
      simpa [Pi.mul_apply] using this
    have hu2 : (∫⁻ t, u t ^ (2:ℝ) ∂μ) = F1 := by
      simp only [hu, hF1]
      apply lintegral_congr; intro t
      rw [← ENNReal.rpow_mul]; norm_num
    have hv2 : (∫⁻ t, v t ^ (2:ℝ) ∂μ) = ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ (2 : ℝ) ∂μ := by
      apply lintegral_congr; intro t
      simp only [hv]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
      norm_num
    rw [hu2, hv2] at hcs
    rw [hHx]
    calc (∫⁻ t, u t * v t ∂μ) ^ (2:ℝ)
        ≤ (F1 ^ (1/(2:ℝ)) * (∫⁻ t, ‖f t‖ₑ * ‖g (x-t)‖ₑ^(2:ℝ) ∂μ) ^ (1/(2:ℝ))) ^ (2:ℝ) := by
          gcongr
      _ = F1 * (∫⁻ t, ‖f t‖ₑ * ‖g (x-t)‖ₑ^(2:ℝ) ∂μ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
              ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          norm_num
  -- STEP 4 + 5: integrate `(H x)²` in `x`, Tonelli swap, translation invariance
  have hstep45 : (∫⁻ x, (H x) ^ (2:ℝ) ∂μ) ≤ F1 * (F1 * G2) := by
    calc (∫⁻ x, (H x) ^ (2:ℝ) ∂μ)
        ≤ ∫⁻ x, F1 * (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ (2:ℝ) ∂μ) ∂μ := by
          apply lintegral_mono; exact hstep3
      _ = F1 * ∫⁻ x, (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ (2:ℝ) ∂μ) ∂μ := by
          rw [lintegral_const_mul' F1 _ (ne_of_lt hF1_lt)]
      _ = F1 * (F1 * G2) := by
          congr 1
          -- joint measurability of the swapped integrand
          have hmp : MeasurePreserving (fun p : (EuclideanSpace ℝ (Fin 3)) × _ =>
              (p.1 - p.2, p.2)) (μ.prod μ) (μ.prod μ) := measurePreserving_sub_prod μ μ
          have hgsub : AEStronglyMeasurable
              (fun p : (EuclideanSpace ℝ (Fin 3)) × _ => g (p.1 - p.2)) (μ.prod μ) :=
            (hg.aestronglyMeasurable.comp_fst).comp_measurePreserving hmp
          have hjoint : AEMeasurable
              (fun p : (EuclideanSpace ℝ (Fin 3)) × _ =>
                ‖f p.2‖ₑ * ‖g (p.1 - p.2)‖ₑ ^ (2:ℝ)) (μ.prod μ) :=
            (hf_aem.comp_snd).mul (hgsub.enorm.pow_const _)
          rw [lintegral_lintegral_swap hjoint]
          have hinner : ∀ t, (∫⁻ x, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ (2:ℝ) ∂μ)
              = ‖f t‖ₑ * G2 := by
            intro t
            rw [lintegral_const_mul' (‖f t‖ₑ) _ enorm_ne_top,
                lintegral_sub_right_eq_self (fun y => ‖g y‖ₑ ^ (2:ℝ)) t]
          simp_rw [hinner]
          rw [lintegral_mul_const'' _ hf_aem, hF1]
  -- STEP 2 + 6: reduce eLpNorm to the majorant lintegral, then assemble
  have hbound : eLpNorm (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) 2 μ
      ≤ (∫⁻ x, (H x) ^ (2:ℝ) ∂μ) ^ (1/(2:ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    gcongr with x
    exact hstep1 x
  -- final bound `eLpNorm (f⋆g) 2 ≤ ‖f‖₁ ‖g‖₂`
  have hfinal : eLpNorm (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) 2 μ
      ≤ eLpNorm f 1 μ * eLpNorm g 2 μ := by
    refine hbound.trans ?_
    calc (∫⁻ x, (H x) ^ (2:ℝ) ∂μ) ^ (1/(2:ℝ))
        ≤ (F1 * (F1 * G2)) ^ (1/(2:ℝ)) := by gcongr
      _ = F1 * G2 ^ (1/(2:ℝ)) := by
          rw [← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
              ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
          norm_num
      _ = eLpNorm f 1 μ * eLpNorm g 2 μ := by rw [hF1eq, hG2eq]
  exact ⟨⟨haem, lt_of_le_of_lt hfinal (by
    rw [hμ] at *
    exact ENNReal.mul_lt_top (hf.eLpNorm_lt_top) (hg.eLpNorm_lt_top))⟩, hfinal⟩

end Spectra.CompactOperator

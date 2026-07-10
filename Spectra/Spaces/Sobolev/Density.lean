/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.WeakDerivative
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Lp.SmoothApprox
/-!
# Density of Test Functions in L²(ℝᵈ)

This file proves that smooth compactly supported functions `C_c^∞(ℝᵈ)` are dense in `L²(ℝᵈ)`,
for every dimension `d`, together with the intermediate density of continuous compactly supported
functions.  All results are stated generically over `{d : ℕ}` (with `R3 := Rn 3` a defeq abbrev).

## Main statements

* `dense_continuous_compactSupport_L2`: continuous compactly supported functions are dense in `L²`.
* `eLpNorm_le_of_compactSupport_bound`: an elementary `L²`-norm bound for a compactly supported
  bounded function (sup-norm × a power of the support measure).
* `dense_test_functions_L2`: `C_c^∞(ℝᵈ)` is dense in `L²(ℝᵈ)` — the capstone density result,
  supplied directly by Mathlib's `Lp.dense_hasCompactSupport_contDiff`.

## Implementation notes

`dense_continuous_compactSupport_L2` is the `L² ←ε— C_c` step (via Mathlib's
`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`); the `C_c ←ε— C_c^∞` mollification step is now
supplied wholesale by Mathlib (`Lp.dense_hasCompactSupport_contDiff`), so the capstone
`dense_test_functions_L2` is a thin `Dense.mono` over it.  The helper
`eLpNorm_le_of_compactSupport_bound` is retained: it feeds the mollification error estimate in
`Mollification.lean`.

## References

* [Adams, Fournier, *Sobolev Spaces*][adams2003]
* [Lieb, Loss, *Analysis*][lieb2001], Chapter 2.
-/
open MeasureTheory Complex
open scoped ENNReal Pointwise ContDiff

namespace Spectra.Sobolev

variable {d : ℕ}

/-- Continuous compactly supported functions are dense in L²(ℝ³). -/
lemma dense_continuous_compactSupport_L2 :
    Dense {g : (l2Rn d) | ∃ (φ : Rn d → ℂ),
      Continuous φ ∧ HasCompactSupport φ ∧
      (g : Rn d → ℂ) =ᵐ[volume] φ} := by
  rw [Metric.dense_iff]
  intro g ε hε
  have hg := Lp.memLp g
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hε' : (ENNReal.ofReal (ε / 2)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Nat.ofNat_pos, div_pos_iff_of_pos_right]
    exact RCLike.ofReal_pos.mp hε
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Rn d)) := by
    infer_instance
  haveI : (volume : Measure (Rn d)).Regular := by
    infer_instance
  haveI : WeaklyLocallyCompactSpace (Rn d) := by infer_instance
  haveI : R1Space (Rn d) := by infer_instance
  obtain ⟨φ, hsupp, hclose, hcont, hmem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hp hε'
  use hmem.toLp φ
  constructor
  · simp only [Metric.mem_ball]
    rw [Lp.dist_def]
    have h1 : eLpNorm ((hmem.toLp φ : Rn d → ℂ) - (g : Rn d → ℂ)) 2 volume ≤
              ENNReal.ofReal (ε / 2) := by
      have hae : (hmem.toLp φ : Rn d → ℂ) - (g : Rn d → ℂ) =ᵐ[volume] φ - (g : Rn d → ℂ) :=
        hmem.coeFn_toLp.sub (ae_eq_refl _)
      rw [eLpNorm_congr_ae (p := 2) hae, eLpNorm_sub_comm]
      exact hclose
    calc (eLpNorm ((hmem.toLp φ : Rn d → ℂ) - (g : Rn d → ℂ)) 2 volume).toReal
        ≤ (ENNReal.ofReal (ε / 2)).toReal :=
          ENNReal.toReal_le_toReal
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1)
            ENNReal.ofReal_ne_top |>.mpr h1
      _ < ε := by rw [ENNReal.toReal_ofReal (by linarith)]; linarith
  · exact ⟨φ, hcont, hsupp, hmem.coeFn_toLp⟩

/-- The eLpNorm of a compactly supported bounded function is controlled by
    the sup-norm times a power of the support measure -/
lemma eLpNorm_le_of_compactSupport_bound
    (f : Rn d → ℂ) (hf_supp : HasCompactSupport f)
    (C : ℝ) (hfC : ∀ x, ‖f x‖ ≤ C) :
    eLpNorm f 2 (volume : Measure (Rn d)) ≤
      ENNReal.ofReal C *
        ((volume : Measure (Rn d)) (tsupport f)) ^ ((1 : ℝ) / 2) := by
  set K := tsupport f
  have hK : IsCompact K := hf_supp.isCompact
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have h_eq : f = K.indicator f := by
    ext x; by_cases hx : x ∈ K
    · exact (Set.indicator_of_mem hx f).symm
    · rw [Set.indicator_of_notMem hx f]
      exact image_eq_zero_of_notMem_tsupport hx
  conv_lhs => rw [h_eq, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Rn d)) := by
    infer_instance
  haveI : IsFiniteMeasure ((volume : Measure (Rn d)).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have h_ae_bound : ∀ᵐ x ∂(volume : Measure (Rn d)).restrict K, ‖f x‖ ≤ C :=
    ae_of_all _ hfC
  calc eLpNorm f 2 ((volume : Measure (Rn d)).restrict K)
      ≤ ((volume : Measure (Rn d)).restrict K Set.univ) ^ (ENNReal.toReal 2)⁻¹ *
          ENNReal.ofReal C := eLpNorm_le_of_ae_bound h_ae_bound
    _ = ENNReal.ofReal C *
          ((volume : Measure (Rn d)) K) ^ ((1 : ℝ) / 2) := by
        rw [mul_comm, Measure.restrict_apply_univ]
        congr 1
        simp [ENNReal.toReal_ofNat]

/-- **Density**: C_c^∞(ℝ³) is dense in L²(ℝ³).
    Chain: L² ←ε/2— C_c ←ε/2— C_c^∞. -/
lemma dense_test_functions_L2 {d : ℕ} :
    Dense {g : l2Rn d | ∃ (φ : Rn d → ℂ),
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (g : Rn d → ℂ) =ᵐ[volume] φ} := by
  -- Re-pointed at mathlib's general-dimension density theorem; the two sets differ only in the
  -- order of the ∃-body conjuncts, so `Dense.mono` closes it.
  refine Dense.mono ?_ (MeasureTheory.Lp.dense_hasCompactSupport_contDiff (F := ℂ)
    (μ := (volume : Measure (Rn d))) (p := 2) (by norm_num))
  rintro f ⟨g, h1, h2, h3⟩
  exact ⟨g, h3, h2, h1⟩

end Spectra.Sobolev

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Calculus.PMapSquareRoot
/-!
# The mixed bounded/unbounded product law for the PVM functional calculus (J-free)

Generic spectral-calculus infrastructure, independent of the Tomita/modular (`J`) machinery.
Relocated here from `Spectra/Modular/Cocycle/ModularSqrtSelfAdjoint.lean` so that downstream
*pure-spectral* files (e.g. `SpectralTheory/Calculus/SquarePushforward.lean`) can use them without
importing any modular/`J` file — a correctness (non-circularity) requirement for the Field-3
polar-uniqueness build.

* `borelMeasure_spectralCalculus_eq_withDensity` — `μ_{Φ(g)ξ} = μ_ξ.withDensity ‖g‖²`.
* `mem_pmapDomain_spectralCalculus` — `Φ(g)ξ ∈ D(∫f dP)` when `f·g` is bounded.
* `pmapOfPVM_spectralCalculus_of_mul_bounded` — **the mixed product law**:
  `(∫f dP)(Φ(g)ξ) = Φ(f·g)ξ` when `g`, `f·g` are bounded.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

/-! ## Generic spectral-calculus infrastructure -/

namespace Spectra.QuantumMechanics.SpectralTheory

open Spectra Spectra.Borel Spectra.OneParameterUnitaryGroup SpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- **The diagonal measure of a bounded-calculus vector is a weighted measure**:
`μ_{Φ(g)ξ} = μ_ξ.withDensity ‖g‖²`.  On any measurable `B`, both sides have mass
`∫_B ‖g‖² dμ_ξ`, using `E(B)Φ(g) = Φ(1_B·g)` (`spectralCalculus_mul`) and
`‖Φ(1_B·g)ξ‖² = ∫‖1_B·g‖² dμ_ξ` (`norm_sq_spectralCalculus_apply`). -/
theorem borelMeasure_spectralCalculus_eq_withDensity
    (g : ℝ → ℂ) (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (ξ : H) :
    borelMeasure U_grp (spectralCalculus U_grp g hg_meas hg_bdd ξ)
      = (borelMeasure U_grp ξ).withDensity (fun s => (‖g s‖₊ : ℝ≥0∞) ^ 2) := by
  classical
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  haveI : IsFiniteMeasure (borelMeasure U_grp (spectralCalculus U_grp g hg_meas hg_bdd ξ)) :=
    borelMeasure_isFiniteMeasure U_grp _
  refine Measure.ext fun B hB => ?_
  rw [withDensity_apply _ hB]
  have hRHS_ne : (∫⁻ s in B, (‖g s‖₊ : ℝ≥0∞) ^ 2 ∂(borelMeasure U_grp ξ)) ≠ ⊤ := by
    obtain ⟨C, hC⟩ := hg_bdd
    have hbound : ∀ s, (‖g s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖C‖₊ : ℝ≥0∞) ^ 2 := by
      intro s
      have hle : ‖g s‖₊ ≤ ‖C‖₊ := by
        rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
        exact (hC s).trans (le_abs_self C |>.trans_eq (Real.norm_eq_abs C).symm)
      exact pow_le_pow_left' (by exact_mod_cast hle) 2
    apply ne_of_lt
    calc (∫⁻ s in B, (‖g s‖₊ : ℝ≥0∞) ^ 2 ∂(borelMeasure U_grp ξ))
        ≤ ∫⁻ _ in B, (‖C‖₊ : ℝ≥0∞) ^ 2 ∂(borelMeasure U_grp ξ) := lintegral_mono fun s => hbound s
      _ = (‖C‖₊ : ℝ≥0∞) ^ 2 * (borelMeasure U_grp ξ) B := by rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hRHS_ne).mp ?_
  rw [← norm_sq_spectralProjection U_grp B hB (spectralCalculus U_grp g hg_meas hg_bdd ξ)]
  have hEB : spectralProjection U_grp B hB (spectralCalculus U_grp g hg_meas hg_bdd ξ)
      = spectralCalculus U_grp (fun s => Set.indicator B (fun _ => (1 : ℂ)) s * g s)
          ((measurable_const.indicator hB).mul hg_meas)
          (bounded_mul (indicator_one_bdd B) hg_bdd) ξ := by
    rw [← ContinuousLinearMap.mul_apply]
    simp only [spectralProjection]
    rw [spectralCalculus_mul U_grp g (Set.indicator B fun _ => (1 : ℂ)) hg_meas hg_bdd
        (measurable_const.indicator hB) (indicator_one_bdd B)
        ((measurable_const.indicator hB).mul hg_meas) (bounded_mul (indicator_one_bdd B) hg_bdd)]
  rw [hEB, norm_sq_spectralCalculus_apply,
    ← integral_toReal ((hg_meas.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable.restrict
      (ae_of_all _ fun s => ENNReal.pow_lt_top (by exact_mod_cast ENNReal.coe_lt_top)),
    ← integral_indicator hB]
  refine integral_congr_ae (.of_forall fun s => ?_)
  simp only [Set.indicator_apply]
  by_cases hs : s ∈ B
  · simp only [hs, if_true]
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
    simp
  · simp only [hs, if_false]
    simp

/-- **Domain membership**: `Φ(g)ξ ∈ D(∫f dP)` whenever `g` and the product `f·g` are bounded. Via
the weighted measure `μ_{Φ(g)ξ} = ‖g‖²·μ_ξ`, the condition `∫‖f‖² dμ_{Φ(g)ξ} < ∞` becomes
`∫‖f·g‖² dμ_ξ < ∞`, which holds since `f·g` is bounded and `μ_ξ` finite. -/
theorem mem_pmapDomain_spectralCalculus
    (f g : ℝ → ℂ) (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hfg_bdd : ∃ C, ∀ s, ‖f s * g s‖ ≤ C) (ξ : H) :
    spectralCalculus U_grp g hg_meas hg_bdd ξ ∈ ProjValMeasure.pmapDomain U_grp.toPVM f := by
  rw [ProjValMeasure.mem_pmapDomain]
  have hmeas_eq : U_grp.toPVM.diag (spectralCalculus U_grp g hg_meas hg_bdd ξ)
      = borelMeasure U_grp (spectralCalculus U_grp g hg_meas hg_bdd ξ) := rfl
  rw [hmeas_eq, borelMeasure_spectralCalculus_eq_withDensity U_grp g hg_meas hg_bdd ξ]
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  rw [integrable_withDensity_iff (hg_meas.nnnorm.coe_nnreal_ennreal.pow_const 2)
      (ae_of_all _ fun s => ENNReal.pow_lt_top (by exact_mod_cast ENNReal.coe_lt_top))]
  obtain ⟨C, hC⟩ := hfg_bdd
  refine Integrable.mono' (integrable_const (C ^ 2)) ?_ (ae_of_all _ fun s => ?_)
  · exact ((hf_meas.norm.pow_const 2).mul
      (((hg_meas.nnnorm.coe_nnreal_ennreal.pow_const 2)).ennreal_toReal)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ENNReal.toReal_pow, ENNReal.coe_toReal,
      coe_nnnorm]
    have hmul : ‖f s‖ ^ 2 * ‖g s‖ ^ 2 = ‖f s * g s‖ ^ 2 := by rw [norm_mul]; ring
    rw [hmul]
    nlinarith [hC s, norm_nonneg (f s * g s)]

/-- Bound: `‖truncSym f n s · g s‖ ≤ C` when `‖f s · g s‖ ≤ C` (the truncation is `f s` or `0`). -/
private lemma norm_truncMul_le (f g : ℝ → ℂ) {C : ℝ} (hC : ∀ s, ‖f s * g s‖ ≤ C) (n : ℕ) (s : ℝ) :
    ‖truncSym f n s * g s‖ ≤ C := by
  rw [truncSym_apply]
  split_ifs with h
  · exact hC s
  · simp only [zero_mul, norm_zero]; exact (norm_nonneg (f s * g s)).trans (hC s)

/-- `Φ(truncSym f n · g)ξ → Φ(f·g)ξ`: the truncated products converge in the `L²` norm identity,
`‖Φ(truncₙ·g)ξ − Φ(f·g)ξ‖² = ∫‖(truncₙ − f)·g‖² dμ_ξ → 0` by dominated convergence (dominated by
`(2C)²`, `μ_ξ` finite). -/
theorem tendsto_spectralCalculus_truncMul
    (f g : ℝ → ℂ) (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hfg_meas : Measurable fun s => f s * g s)
    (hfg_bdd : ∃ C, ∀ s, ‖f s * g s‖ ≤ C) (ξ : H) :
    Tendsto (fun n => spectralCalculus U_grp (fun s => truncSym f n s * g s)
        ((measurable_truncSym hf_meas n).mul hg_meas)
        (bounded_mul (truncSym_bdd f n) hg_bdd) ξ) atTop
      (𝓝 (spectralCalculus U_grp (fun s => f s * g s) hfg_meas hfg_bdd ξ)) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖spectralCalculus U_grp (fun s => truncSym f n s * g s)
        ((measurable_truncSym hf_meas n).mul hg_meas)
        (bounded_mul (truncSym_bdd f n) hg_bdd) ξ
        - spectralCalculus U_grp (fun s => f s * g s) hfg_meas hfg_bdd ξ‖
      = Real.sqrt (∫ s, ‖truncSym f n s * g s - f s * g s‖ ^ 2 ∂(borelMeasure U_grp ξ)) := by
    intro n
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    rw [← ContinuousLinearMap.sub_apply,
      ← spectralCalculus_sub U_grp (fun s => truncSym f n s * g s) (fun s => f s * g s)
        ((measurable_truncSym hf_meas n).mul hg_meas) (bounded_mul (truncSym_bdd f n) hg_bdd)
        hfg_meas hfg_bdd
        (((measurable_truncSym hf_meas n).mul hg_meas).sub hfg_meas)
        (bounded_sub (bounded_mul (truncSym_bdd f n) hg_bdd) hfg_bdd),
      norm_sq_spectralCalculus_apply]
  simp_rw [hnorm]
  obtain ⟨C, hC⟩ := hfg_bdd
  have hint_tendsto : Tendsto
      (fun n => ∫ s, ‖truncSym f n s * g s - f s * g s‖ ^ 2 ∂(borelMeasure U_grp ξ))
      atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := borelMeasure U_grp ξ)
      (F := fun n s => ‖truncSym f n s * g s - f s * g s‖ ^ 2) (f := fun _ => (0 : ℝ))
      (bound := fun _ : ℝ => (2 * C) ^ 2)
      (fun n => (((measurable_truncSym hf_meas n).mul hg_meas).sub hfg_meas).norm.pow_const 2
        |>.aestronglyMeasurable)
      (integrable_const _) (fun n => ae_of_all _ fun s => ?_) (ae_of_all _ fun s => ?_)
    · simpa using h
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hd : ‖truncSym f n s * g s - f s * g s‖ ≤ 2 * C := by
        calc ‖truncSym f n s * g s - f s * g s‖
            ≤ ‖truncSym f n s * g s‖ + ‖f s * g s‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add (norm_truncMul_le f g hC n s) (hC s)
          _ = 2 * C := by ring
      nlinarith [norm_nonneg (truncSym f n s * g s - f s * g s), hd, hC s, norm_nonneg (f s * g s)]
    · have hmul : Tendsto (fun n => truncSym f n s * g s) atTop (𝓝 (f s * g s)) :=
        (tendsto_truncSym f s).mul_const (g s)
      have h0 : Tendsto (fun n => truncSym f n s * g s - f s * g s) atTop (𝓝 0) := by
        have := hmul.sub (tendsto_const_nhds (x := f s * g s))
        simpa using this
      simpa using h0.norm.pow 2
  have := hint_tendsto.sqrt
  rwa [Real.sqrt_zero] at this

/-- **The mixed bounded/unbounded product law.**  For measurable `f`, bounded measurable `g` with
`f·g` bounded, applying the unbounded `∫f dP = pmapOfPVM f` after the bounded `Φ(g)` collapses to
the bounded `Φ(f·g)`:  `(∫f dP)(Φ(g)ξ) = Φ(f·g)ξ`.  Both are the strong limit of the same sequence
`Φ(truncₙ f)(Φ(g)ξ) = Φ(truncₙ f · g)ξ` — the outer one by `pmapOfPVM_apply_tendsto`, the value by
`tendsto_spectralCalculus_truncMul` — so uniqueness of limits closes it. -/
theorem pmapOfPVM_spectralCalculus_of_mul_bounded
    (f g : ℝ → ℂ) (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C) (hfg_meas : Measurable fun s => f s * g s)
    (hfg_bdd : ∃ C, ∀ s, ‖f s * g s‖ ≤ C) (ξ : H)
    (hmem : spectralCalculus U_grp g hg_meas hg_bdd ξ ∈ ProjValMeasure.pmapDomain U_grp.toPVM f) :
    pmapOfPVM U_grp f hf_meas ⟨spectralCalculus U_grp g hg_meas hg_bdd ξ, hmem⟩
      = spectralCalculus U_grp (fun s => f s * g s) hfg_meas hfg_bdd ξ := by
  have htend1 := pmapOfPVM_apply_tendsto U_grp f hf_meas
    ((ProjValMeasure.mem_pmapDomain U_grp.toPVM).mp hmem)
  have hstep : ∀ n, pmapTrunc U_grp f hf_meas n (spectralCalculus U_grp g hg_meas hg_bdd ξ)
      = spectralCalculus U_grp (fun s => truncSym f n s * g s)
          ((measurable_truncSym hf_meas n).mul hg_meas)
          (bounded_mul (truncSym_bdd f n) hg_bdd) ξ := by
    intro n
    rw [pmapTrunc_apply, ← ContinuousLinearMap.mul_apply,
      spectralCalculus_mul U_grp g (truncSym f n) hg_meas hg_bdd
        (measurable_truncSym hf_meas n) (truncSym_bdd f n)
        ((measurable_truncSym hf_meas n).mul hg_meas) (bounded_mul (truncSym_bdd f n) hg_bdd)]
  have htend2 : Tendsto (fun n => pmapTrunc U_grp f hf_meas n
      (spectralCalculus U_grp g hg_meas hg_bdd ξ)) atTop
      (𝓝 (spectralCalculus U_grp (fun s => f s * g s) hfg_meas hfg_bdd ξ)) := by
    refine (tendsto_spectralCalculus_truncMul
      U_grp f g hf_meas hg_meas hg_bdd hfg_meas hfg_bdd ξ).congr
      fun n => (hstep n).symm
  exact tendsto_nhds_unique htend1 htend2

end Spectra.QuantumMechanics.SpectralTheory

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Author: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularInvolution
/-!
# The modular square root `Δ^{½}` is self-adjoint (HC1)

For a cyclic–separating vector `Ω` of a von Neumann algebra `M`, the modular square root
`Δ^{½} = modularSqrt` (the unbounded `√` calculus of `Δ = modularOp M Ω ≥ 0`) is **self-adjoint**.

The route is von Neumann's deficiency criterion (`isSelfAdjoint_of_surjective_addSub`): a densely
defined symmetric operator whose `A + i` and `A − i` are both surjective is self-adjoint.

* **Symmetry** is `pmapOfPVM_isFormalAdjoint_self` (the `√` symbol is real).
* **Density** of `D(Δ^{½})` follows from `D(Δ) ⊆ D(Δ^{½})` and `D(Δ)` dense.
* **Surjectivity** of `Δ^{½} ± i` uses the *bounded* resolvent `R_± := Φ(1/(√·±i))`: the symbol
  `1/(√s±i)` is bounded (`‖√s±i‖ ≥ 1`), so `R_± h` is a genuine bounded-calculus vector, and the
  **mixed bounded/unbounded product law** below shows `R_± h ∈ D(Δ^{½})` and
  `Δ^{½}(R_± h) = Φ(√/(√±i)) h`, whence `(Δ^{½} ± i)(R_± h) = Φ((√±i)/(√±i)) h = Φ(1) h = h`.

## Key new infrastructure (namespace `Spectra.QuantumMechanics.SpectralTheory`)

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
    refine (tendsto_spectralCalculus_truncMul U_grp f g hf_meas hg_meas hg_bdd hfg_meas hfg_bdd ξ).congr
      fun n => (hstep n).symm
  exact tendsto_nhds_unique htend1 htend2

end Spectra.QuantumMechanics.SpectralTheory

/-! ## The modular square root is self-adjoint -/

open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ### Boundedness / measurability of the resolvent symbols `1/(√s ± i)`, `√s/(√s ± i)` -/

/-- `‖√s + i‖ ≥ 1` (the imaginary part is `1`). -/
lemma one_le_norm_sqrtC_add_I (s : ℝ) : (1 : ℝ) ≤ ‖(Real.sqrt s : ℂ) + I‖ := by
  have him : ((Real.sqrt s : ℂ) + I).im = 1 := by simp
  calc (1 : ℝ) = |((Real.sqrt s : ℂ) + I).im| := by rw [him]; norm_num
    _ ≤ ‖(Real.sqrt s : ℂ) + I‖ := Complex.abs_im_le_norm _

/-- `‖√s − i‖ ≥ 1` (the imaginary part is `−1`). -/
lemma one_le_norm_sqrtC_sub_I (s : ℝ) : (1 : ℝ) ≤ ‖(Real.sqrt s : ℂ) - I‖ := by
  have him : ((Real.sqrt s : ℂ) - I).im = -1 := by simp
  calc (1 : ℝ) = |((Real.sqrt s : ℂ) - I).im| := by rw [him]; norm_num
    _ ≤ ‖(Real.sqrt s : ℂ) - I‖ := Complex.abs_im_le_norm _

lemma sqrtC_add_I_ne_zero (s : ℝ) : (Real.sqrt s : ℂ) + I ≠ 0 := by
  intro h; have := one_le_norm_sqrtC_add_I s; rw [h, norm_zero] at this; linarith

lemma sqrtC_sub_I_ne_zero (s : ℝ) : (Real.sqrt s : ℂ) - I ≠ 0 := by
  intro h; have := one_le_norm_sqrtC_sub_I s; rw [h, norm_zero] at this; linarith

/-- `‖√s‖ ≤ ‖√s + i‖`, via `‖·‖² = normSq` and `normSq(√s+i) = (√s)² + 1`. -/
lemma norm_sqrtC_le_norm_sqrtC_add_I (s : ℝ) :
    ‖(Real.sqrt s : ℂ)‖ ≤ ‖(Real.sqrt s : ℂ) + I‖ := by
  have h1 : ‖(Real.sqrt s : ℂ)‖ ^ 2 ≤ ‖(Real.sqrt s : ℂ) + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.sqrt_nonneg s]
  nlinarith [norm_nonneg ((Real.sqrt s : ℂ)), norm_nonneg ((Real.sqrt s : ℂ) + I), h1]

lemma norm_sqrtC_le_norm_sqrtC_sub_I (s : ℝ) :
    ‖(Real.sqrt s : ℂ)‖ ≤ ‖(Real.sqrt s : ℂ) - I‖ := by
  have h1 : ‖(Real.sqrt s : ℂ)‖ ^ 2 ≤ ‖(Real.sqrt s : ℂ) - I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.sqrt_nonneg s]
  nlinarith [norm_nonneg ((Real.sqrt s : ℂ)), norm_nonneg ((Real.sqrt s : ℂ) - I), h1]

lemma resPlus_bdd : ∃ C, ∀ s, ‖(1 : ℂ) / ((Real.sqrt s : ℂ) + I)‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [norm_div, NormOneClass.norm_one, div_le_one (by have := one_le_norm_sqrtC_add_I s; linarith)]
  exact one_le_norm_sqrtC_add_I s

lemma resMinus_bdd : ∃ C, ∀ s, ‖(1 : ℂ) / ((Real.sqrt s : ℂ) - I)‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [norm_div, NormOneClass.norm_one, div_le_one (by have := one_le_norm_sqrtC_sub_I s; linarith)]
  exact one_le_norm_sqrtC_sub_I s

lemma sqrtMulResPlus_bdd :
    ∃ C, ∀ s, ‖(Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [mul_one_div, norm_div, div_le_one (by have := one_le_norm_sqrtC_add_I s; linarith)]
  exact norm_sqrtC_le_norm_sqrtC_add_I s

lemma sqrtMulResMinus_bdd :
    ∃ C, ∀ s, ‖(Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))‖ ≤ C := by
  refine ⟨1, fun s => ?_⟩
  rw [mul_one_div, norm_div, div_le_one (by have := one_le_norm_sqrtC_sub_I s; linarith)]
  exact norm_sqrtC_le_norm_sqrtC_sub_I s

lemma IResPlus_bdd : ∃ C, ∀ s, ‖I * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))‖ ≤ C := by
  obtain ⟨C, hC⟩ := resPlus_bdd
  exact ⟨‖I‖ * C, fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)⟩

lemma IResMinus_bdd : ∃ C, ∀ s, ‖I * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))‖ ≤ C := by
  obtain ⟨C, hC⟩ := resMinus_bdd
  exact ⟨‖I‖ * C, fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)⟩

lemma measurable_resPlus : Measurable (fun s : ℝ => (1 : ℂ) / ((Real.sqrt s : ℂ) + I)) :=
  measurable_const.div (measurable_sqrtC.add measurable_const)

lemma measurable_resMinus : Measurable (fun s : ℝ => (1 : ℂ) / ((Real.sqrt s : ℂ) - I)) :=
  measurable_const.div (measurable_sqrtC.sub measurable_const)

lemma measurable_sqrtMulResPlus :
    Measurable (fun s : ℝ => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))) :=
  measurable_sqrtC.mul measurable_resPlus

lemma measurable_sqrtMulResMinus :
    Measurable (fun s : ℝ => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))) :=
  measurable_sqrtC.mul measurable_resMinus

/-! ### Surjectivity of `Δ^{½} ± i` -/

/-- **Surjectivity of `Δ^{½} + i`.**  For every `h`, the bounded resolvent vector
`R h = Φ(1/(√+i)) h` lies in `D(Δ^{½})` (mixed-law domain membership) and
`(Δ^{½} + i)(R h) = Φ(√/(√+i)) h + Φ(i/(√+i)) h = Φ((√+i)/(√+i)) h = Φ(1) h = h`. -/
theorem modularSqrt_add_I_surjective (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    ∀ h : H, ∃ ψ : (modularSqrt hcyc hsep).domain,
      modularSqrt hcyc hsep ψ + I • (ψ : H) = h := by
  set U := genToGroup (modularOp_isSelfAdjoint hcyc hsep) with hU
  intro h
  have hmem : spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I))
        measurable_resPlus resPlus_bdd h
      ∈ ProjValMeasure.pmapDomain U.toPVM (fun s => (Real.sqrt s : ℂ)) :=
    mem_pmapDomain_spectralCalculus U (fun s => (Real.sqrt s : ℂ))
      (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I)) measurable_sqrtC measurable_resPlus resPlus_bdd
      sqrtMulResPlus_bdd h
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hsqrt : modularSqrt hcyc hsep ⟨_, hmem⟩
      = spectralCalculus U (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I)))
          measurable_sqrtMulResPlus sqrtMulResPlus_bdd h :=
    pmapOfPVM_spectralCalculus_of_mul_bounded U (fun s => (Real.sqrt s : ℂ))
      (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I)) measurable_sqrtC measurable_resPlus resPlus_bdd
      measurable_sqrtMulResPlus sqrtMulResPlus_bdd h hmem
  rw [hsqrt]
  have hIR : I • spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I))
        measurable_resPlus resPlus_bdd h
      = spectralCalculus U (fun s => I * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I)))
          (measurable_const.mul measurable_resPlus) IResPlus_bdd h := by
    rw [spectralCalculus_smul U I (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I)) measurable_resPlus
      resPlus_bdd (measurable_const.mul measurable_resPlus) IResPlus_bdd]
    rfl
  show _ + I • spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) + I))
    measurable_resPlus resPlus_bdd h = h
  rw [hIR, ← ContinuousLinearMap.add_apply,
    ← spectralCalculus_add U (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I)))
      (fun s => I * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I)))
      measurable_sqrtMulResPlus sqrtMulResPlus_bdd
      (measurable_const.mul measurable_resPlus) IResPlus_bdd
      (measurable_sqrtMulResPlus.add (measurable_const.mul measurable_resPlus))
      (by obtain ⟨C1, h1⟩ := sqrtMulResPlus_bdd; obtain ⟨C2, h2⟩ := IResPlus_bdd
          exact ⟨C1 + C2, fun s => (norm_add_le _ _).trans (add_le_add (h1 s) (h2 s))⟩)]
  have hcongr : (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))
      + I * ((1 : ℂ) / ((Real.sqrt s : ℂ) + I))) = (fun _ : ℝ => (1 : ℂ)) := by
    funext s
    have hne : (Real.sqrt s : ℂ) + I ≠ 0 := sqrtC_add_I_ne_zero s
    field_simp
  rw [spectralCalculus_congr U hcongr _ _ measurable_const ⟨1, fun _ => norm_one.le⟩,
    spectralCalculus_one, ContinuousLinearMap.id_apply]

/-- **Surjectivity of `Δ^{½} − i`.**  Mirror of the `+i` case with the symbol `1/(√−i)` and the
identity `√/(√−i) − i/(√−i) = (√−i)/(√−i) = 1`. -/
theorem modularSqrt_sub_I_surjective (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    ∀ h : H, ∃ ψ : (modularSqrt hcyc hsep).domain,
      modularSqrt hcyc hsep ψ - I • (ψ : H) = h := by
  set U := genToGroup (modularOp_isSelfAdjoint hcyc hsep) with hU
  intro h
  have hmem : spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I))
        measurable_resMinus resMinus_bdd h
      ∈ ProjValMeasure.pmapDomain U.toPVM (fun s => (Real.sqrt s : ℂ)) :=
    mem_pmapDomain_spectralCalculus U (fun s => (Real.sqrt s : ℂ))
      (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I)) measurable_sqrtC measurable_resMinus resMinus_bdd
      sqrtMulResMinus_bdd h
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hsqrt : modularSqrt hcyc hsep ⟨_, hmem⟩
      = spectralCalculus U (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I)))
          measurable_sqrtMulResMinus sqrtMulResMinus_bdd h :=
    pmapOfPVM_spectralCalculus_of_mul_bounded U (fun s => (Real.sqrt s : ℂ))
      (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I)) measurable_sqrtC measurable_resMinus resMinus_bdd
      measurable_sqrtMulResMinus sqrtMulResMinus_bdd h hmem
  rw [hsqrt]
  have hIR : I • spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I))
        measurable_resMinus resMinus_bdd h
      = spectralCalculus U (fun s => I * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I)))
          (measurable_const.mul measurable_resMinus) IResMinus_bdd h := by
    rw [spectralCalculus_smul U I (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I)) measurable_resMinus
      resMinus_bdd (measurable_const.mul measurable_resMinus) IResMinus_bdd]
    rfl
  show _ - I • spectralCalculus U (fun s => (1 : ℂ) / ((Real.sqrt s : ℂ) - I))
    measurable_resMinus resMinus_bdd h = h
  rw [hIR, ← ContinuousLinearMap.sub_apply,
    ← spectralCalculus_sub U (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I)))
      (fun s => I * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I)))
      measurable_sqrtMulResMinus sqrtMulResMinus_bdd
      (measurable_const.mul measurable_resMinus) IResMinus_bdd
      (measurable_sqrtMulResMinus.sub (measurable_const.mul measurable_resMinus))
      (by obtain ⟨C1, h1⟩ := sqrtMulResMinus_bdd; obtain ⟨C2, h2⟩ := IResMinus_bdd
          exact ⟨C1 + C2, fun s => (norm_sub_le _ _).trans (add_le_add (h1 s) (h2 s))⟩)]
  have hcongr : (fun s => (Real.sqrt s : ℂ) * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))
      - I * ((1 : ℂ) / ((Real.sqrt s : ℂ) - I))) = (fun _ : ℝ => (1 : ℂ)) := by
    funext s
    have hne : (Real.sqrt s : ℂ) - I ≠ 0 := sqrtC_sub_I_ne_zero s
    field_simp
  rw [spectralCalculus_congr U hcongr _ _ measurable_const ⟨1, fun _ => norm_one.le⟩,
    spectralCalculus_one, ContinuousLinearMap.id_apply]

/-! ### Density of `D(Δ^{½})` -/

/-- `D(Δ^{½})` is dense: `D(Δ) ⊆ D(Δ^{½})` (`modularOp_domain_le_modularSqrt_domain`) and `D(Δ)` is
dense (from `modularOp_isSelfAdjoint`'s proof, re-derived via the `1+Δ` surjective argument). -/
theorem modularSqrt_domain_dense (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    Dense ((modularSqrt hcyc hsep).domain : Set H) := by
  have hle : (modularOp M Ω).domain ≤ (modularSqrt hcyc hsep).domain :=
    modularOp_domain_le_modularSqrt_domain hcyc hsep
  have hΔdense : Dense ((modularOp M Ω).domain : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro h hh
    obtain ⟨g, hg⟩ := one_add_modularOp_surjective hcyc hsep h
    have hortho : ⟪(g : H), h⟫_ℂ = 0 := (Submodule.mem_orthogonal _ h).1 hh (g : H) g.2
    rw [← hg, inner_add_right] at hortho
    have h1 : 0 ≤ RCLike.re ⟪(g : H), modularOp M Ω g⟫_ℂ := by
      rw [inner_re_symm]; exact modularOp_nonneg hcyc g
    have hre : RCLike.re ⟪(g : H), modularOp M Ω g⟫_ℂ + ‖(g : H)‖ ^ 2 = 0 := by
      have hr := congrArg RCLike.re hortho
      rwa [map_add, map_zero, inner_self_eq_norm_sq] at hr
    have hgz : (g : H) = 0 := by
      have h2 : ‖(g : H)‖ ^ 2 = 0 := by linarith [sq_nonneg ‖(g : H)‖]
      exact norm_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h2)
    have hg0 : g = 0 := Subtype.ext hgz
    rw [← hg, hg0]; simp
  exact hΔdense.mono (fun x hx => hle hx)

/-! ### The main theorem -/

/-- **The modular square root `Δ^{½}` is self-adjoint** (HC1).  Von Neumann's deficiency criterion
`isSelfAdjoint_of_surjective_addSub`: `Δ^{½}` is densely defined, symmetric (real symbol `√`), and
both `Δ^{½} + i` and `Δ^{½} − i` are surjective (bounded resolvent + mixed product law). -/
theorem modularSqrt_isSelfAdjoint (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω) :
    IsSelfAdjoint (modularSqrt hcyc hsep) := by
  have hsym : (modularSqrt hcyc hsep).IsFormalAdjoint (modularSqrt hcyc hsep) :=
    pmapOfPVM_isFormalAdjoint_self _ (fun s => (Real.sqrt s : ℂ)) measurable_sqrtC
      (fun s => by rw [Complex.conj_ofReal])
  exact isSelfAdjoint_of_surjective_addSub (modularSqrt hcyc hsep) hsym
    (modularSqrt_domain_dense hcyc hsep)
    (modularSqrt_add_I_surjective hcyc hsep) (modularSqrt_sub_I_surjective hcyc hsep)

end Spectra.TomitaTakesaki

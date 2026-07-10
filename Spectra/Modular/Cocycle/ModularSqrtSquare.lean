/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Modular.Cocycle.ModularSqrtSelfAdjoint
/-!
# The modular square root squares to the modular operator: `(Δ^{½})² = Δ` (HC2)

Deliverables (sorry-free):
* `modularSqrt_mem_domain_of_mem_modularOp` — `Δ^{½}x ∈ D(Δ^{½})` for `x ∈ D(Δ)`.
* `modularSqrt_sq_apply` — `Δ^{½}(Δ^{½}x) = Δx` pointwise on `D(Δ)`.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal
open Spectra.QuantumMechanics.SpectralTheory
open Spectra.YosidaHille
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel
open SpectralMeasure

namespace Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-! ## The output measure of an unbounded-calculus vector (density) -/

/-- **Output measure of the unbounded calculus, on a set.**  For `ξ ∈ D(∫f dP)` and measurable
`B`, `μ_{(∫f dP)ξ}(B) = ∫_B ‖f‖² dμ_ξ`.  Both sides are the limit of the bounded truncation:
`‖E(B)((∫f dP)ξ)‖² = limₙ ‖Φ(1_B·truncₙ)ξ‖² = limₙ ∫‖1_B·truncₙ‖²dμ_ξ = ∫_B‖f‖²dμ_ξ` (DCT). -/
theorem borelMeasure_pmapOfPVM_apply_eq_setLIntegral
    (f : ℝ → ℂ) (hf : Measurable f) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (borelMeasure U_grp (pmapOfPVM U_grp f hf
        ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩) B).toReal
      = ∫ s in B, ‖f s‖ ^ 2 ∂(borelMeasure U_grp ξ) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  set v := pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩ with hv
  -- LHS = ‖E(B) v‖²
  rw [← norm_sq_spectralProjection U_grp B hB v]
  -- E(B) v = limₙ Φ(1_B · truncₙ f) ξ
  have hEv : Tendsto (fun n => spectralCalculus U_grp
      (fun s => Set.indicator B (fun _ => (1 : ℂ)) s * truncSym f n s)
        ((measurable_const.indicator hB).mul (measurable_truncSym hf n))
        (bounded_mul (indicator_one_bdd B) (truncSym_bdd f n)) ξ) atTop
      (𝓝 (spectralProjection U_grp B hB v)) := by
    have htrunc := pmapOfPVM_apply_tendsto U_grp f hf hξ
    rw [← hv] at htrunc
    have hcont := (spectralProjection U_grp B hB).continuous.tendsto v
    have := (hcont.comp htrunc)
    refine this.congr fun n => ?_
    rw [Function.comp_apply, pmapTrunc_apply]
    simp only [spectralProjection]
    rw [← ContinuousLinearMap.mul_apply,
      spectralCalculus_mul U_grp (truncSym f n) (Set.indicator B fun _ => (1 : ℂ))
        (measurable_truncSym hf n) (truncSym_bdd f n)
        (measurable_const.indicator hB) (indicator_one_bdd B)
        ((measurable_const.indicator hB).mul (measurable_truncSym hf n))
        (bounded_mul (indicator_one_bdd B) (truncSym_bdd f n))]
  -- norms squared converge to ‖E(B)v‖²
  have hL : Tendsto (fun n => ‖spectralCalculus U_grp
      (fun s => Set.indicator B (fun _ => (1 : ℂ)) s * truncSym f n s)
        ((measurable_const.indicator hB).mul (measurable_truncSym hf n))
        (bounded_mul (indicator_one_bdd B) (truncSym_bdd f n)) ξ‖ ^ 2) atTop
      (𝓝 (‖spectralProjection U_grp B hB v‖ ^ 2)) := hEv.norm.pow 2
  -- and the norm² equals ∫ ‖1_B·truncₙ‖² dμ_ξ, tending to ∫_B ‖f‖² dμ_ξ (DCT)
  have hR : Tendsto (fun n => ‖spectralCalculus U_grp
      (fun s => Set.indicator B (fun _ => (1 : ℂ)) s * truncSym f n s)
        ((measurable_const.indicator hB).mul (measurable_truncSym hf n))
        (bounded_mul (indicator_one_bdd B) (truncSym_bdd f n)) ξ‖ ^ 2) atTop
      (𝓝 (∫ s in B, ‖f s‖ ^ 2 ∂(borelMeasure U_grp ξ))) := by
    have heq : ∀ n, ‖spectralCalculus U_grp
        (fun s => Set.indicator B (fun _ => (1 : ℂ)) s * truncSym f n s)
          ((measurable_const.indicator hB).mul (measurable_truncSym hf n))
          (bounded_mul (indicator_one_bdd B) (truncSym_bdd f n)) ξ‖ ^ 2
        = ∫ s, ‖Set.indicator B (fun _ => (1 : ℂ)) s * truncSym f n s‖ ^ 2
            ∂(borelMeasure U_grp ξ) := fun n => by
      rw [norm_sq_spectralCalculus_apply]
    simp_rw [heq]
    rw [← integral_indicator hB]
    refine tendsto_integral_of_dominated_convergence (fun s => ‖f s‖ ^ 2)
      (fun n => (((measurable_const.indicator hB).mul
        (measurable_truncSym hf n)).norm.pow_const 2).aestronglyMeasurable)
      hξ (fun n => Eventually.of_forall fun s => ?_) (Eventually.of_forall fun s => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hbnd : ‖Set.indicator B (fun _ => (1 : ℂ)) s * truncSym f n s‖ ≤ ‖f s‖ := by
        rw [norm_mul]
        by_cases hs : s ∈ B
        · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, one_mul]
          exact norm_truncSym_le f n s
        · rw [Set.indicator_of_notMem hs, norm_zero, zero_mul]; exact norm_nonneg _
      exact pow_le_pow_left₀ (norm_nonneg _) hbnd 2
    · by_cases hs : s ∈ B
      · simp only [Set.indicator_of_mem hs]
        have hlim : Tendsto (fun n => (1 : ℂ) * truncSym f n s) atTop (𝓝 (f s)) := by
          rw [show f s = (1 : ℂ) * f s from (one_mul _).symm]
          exact (tendsto_const_nhds (x := (1 : ℂ))).mul (tendsto_truncSym f s)
        exact hlim.norm.pow 2
      · simp only [Set.indicator_of_notMem hs, zero_mul, norm_zero]
        refine tendsto_const_nhds.congr fun _n => ?_
        simp
  exact tendsto_nhds_unique hL hR

/-- **Output measure of the unbounded calculus** (full density):
`μ_{(∫f dP)ξ} = μ_ξ.withDensity ‖f‖²`. -/
theorem borelMeasure_pmapOfPVM_eq_withDensity
    (f : ℝ → ℂ) (hf : Measurable f) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ)) :
    borelMeasure U_grp (pmapOfPVM U_grp f hf
        ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩)
      = (borelMeasure U_grp ξ).withDensity (fun s => (‖f s‖₊ : ℝ≥0∞) ^ 2) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  set v := pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩ with _hv
  haveI : IsFiniteMeasure (borelMeasure U_grp v) := borelMeasure_isFiniteMeasure U_grp v
  refine Measure.ext fun B hB => ?_
  rw [withDensity_apply _ hB]
  -- RHS as a real integral (both finite)
  have hRHS_ne : (∫⁻ s in B, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂(borelMeasure U_grp ξ)) ≠ ⊤ := by
    apply ne_of_lt
    calc (∫⁻ s in B, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂(borelMeasure U_grp ξ))
        ≤ ∫⁻ s, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂(borelMeasure U_grp ξ) :=
          setLIntegral_le_lintegral _ _
      _ < ⊤ := by
          have := hξ.2
          rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => sq_nonneg _)] at this
          refine lt_of_le_of_lt (le_of_eq ?_) this
          refine lintegral_congr fun s => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.coe_pow]
          congr 2
          rw [← NNReal.coe_inj, coe_nnnorm, Real.coe_toNNReal _ (norm_nonneg _)]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hRHS_ne).mp ?_
  rw [borelMeasure_pmapOfPVM_apply_eq_setLIntegral U_grp f hf hξ B hB]
  rw [← integral_toReal ((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable.restrict
      (ae_of_all _ fun s => ENNReal.pow_lt_top (by exact_mod_cast ENNReal.coe_lt_top))]
  refine integral_congr_ae (.of_forall fun s => ?_)
  simp only
  rw [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]

/-! ## Dominated convergence of bounded approximants to the unbounded calculus -/

/-- **Bounded approximants converge to the unbounded calculus.**  If `x ∈ D(∫f dP)` and `g_m` is a
sequence of bounded symbols with `‖g_m ω‖ ≤ ‖f ω‖` and `g_m ω → f ω` pointwise, then
`Φ(g_m)x → (∫f dP)x`.  The key computation is `‖Φ(g_m)x − (∫f dP)x‖ = √(∫‖g_m − f‖² dμ_x)`
(taking `N → ∞` in `‖Φ(g_m)x − Φ(truncₙ f)x‖ = √(∫‖g_m − truncₙ f‖² dμ_x)` via continuity of the
norm and `pmapOfPVM_apply_tendsto`, the RHS by DCT); then `∫‖g_m − f‖² dμ_x → 0` by DCT. -/
theorem tendsto_spectralCalculus_pmapOfPVM_of_dominated
    (f : ℝ → ℂ) (hf : Measurable f) {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ))
    (g : ℕ → ℝ → ℂ) (hg_meas : ∀ m, Measurable (g m)) (hg_bdd : ∀ m, ∃ C, ∀ ω, ‖g m ω‖ ≤ C)
    (hdom : ∀ m ω, ‖g m ω‖ ≤ ‖f ω‖) (hlim : ∀ ω, Tendsto (fun m => g m ω) atTop (𝓝 (f ω))) :
    Tendsto (fun m => spectralCalculus U_grp (g m) (hg_meas m) (hg_bdd m) ξ) atTop
      (𝓝 (pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩)) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  set v := pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩ with hv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- Step 1: `‖Φ(g m)ξ − v‖ = √(∫ ‖g m − f‖² dμ_ξ)`.
  have hnorm : ∀ m, ‖spectralCalculus U_grp (g m) (hg_meas m) (hg_bdd m) ξ - v‖
      = Real.sqrt (∫ s, ‖g m s - f s‖ ^ 2 ∂(borelMeasure U_grp ξ)) := by
    intro m
    -- integrability of `‖g m − f‖²`
    have _hgf_int : Integrable (fun s => ‖g m s - f s‖ ^ 2) (borelMeasure U_grp ξ) := by
      refine Integrable.mono' (hξ.const_mul (4 : ℝ))
        (((hg_meas m).sub hf).norm.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hb : ‖g m s - f s‖ ≤ 2 * ‖f s‖ := by
        have := norm_sub_le (g m s) (f s)
        linarith [hdom m s]
      nlinarith [norm_nonneg (g m s - f s), hb, norm_nonneg (f s)]
    -- `‖Φ(g m)ξ − Φ(truncₙ f)ξ‖ → ‖Φ(g m)ξ − v‖`
    have htend_lhs : Tendsto (fun N => ‖spectralCalculus U_grp (g m) (hg_meas m) (hg_bdd m) ξ
        - pmapTrunc U_grp f hf N ξ‖) atTop
        (𝓝 ‖spectralCalculus U_grp (g m) (hg_meas m) (hg_bdd m) ξ - v‖) := by
      have hc : Continuous fun y : H =>
          ‖spectralCalculus U_grp (g m) (hg_meas m) (hg_bdd m) ξ - y‖ :=
        (continuous_const.sub continuous_id).norm
      exact (hc.tendsto v).comp (by rw [hv]; exact pmapOfPVM_apply_tendsto U_grp f hf hξ)
    -- each term equals `√(∫ ‖g m − truncₙ f‖²)`
    have heqN : ∀ N, ‖spectralCalculus U_grp (g m) (hg_meas m) (hg_bdd m) ξ
        - pmapTrunc U_grp f hf N ξ‖
        = Real.sqrt (∫ s, ‖g m s - truncSym f N s‖ ^ 2 ∂(borelMeasure U_grp ξ)) := by
      intro N
      rw [pmapTrunc_apply, ← Real.sqrt_sq (norm_nonneg _), ← ContinuousLinearMap.sub_apply,
        ← spectralCalculus_sub U_grp (g m) (truncSym f N) (hg_meas m) (hg_bdd m)
          (measurable_truncSym hf N) (truncSym_bdd f N)
          ((hg_meas m).sub (measurable_truncSym hf N))
          (bounded_sub (hg_bdd m) (truncSym_bdd f N)),
        norm_sq_spectralCalculus_apply]
    -- `√(∫ ‖g m − truncₙ f‖²) → √(∫ ‖g m − f‖²)` (DCT in N)
    have htend_rhs : Tendsto (fun N => Real.sqrt
        (∫ s, ‖g m s - truncSym f N s‖ ^ 2 ∂(borelMeasure U_grp ξ))) atTop
        (𝓝 (Real.sqrt (∫ s, ‖g m s - f s‖ ^ 2 ∂(borelMeasure U_grp ξ)))) := by
      refine (Filter.Tendsto.sqrt ?_)
      obtain ⟨Cg, hCg⟩ := hg_bdd m
      refine tendsto_integral_of_dominated_convergence
        (fun s => (‖g m s‖ + ‖f s‖) ^ 2)
        (fun N =>
          (((hg_meas m).sub (measurable_truncSym hf N)).norm.pow_const 2).aestronglyMeasurable)
        ?_ (fun N => Eventually.of_forall fun s => ?_) (Eventually.of_forall fun s => ?_)
      · -- majorant integrable: `(‖g m‖+‖f‖)² ≤ 2‖g m‖² + 2‖f‖² ≤ 2Cg² + 2‖f‖²`
        refine Integrable.mono' ((integrable_const (2 * Cg ^ 2)).add (hξ.const_mul 2))
          (((hg_meas m).norm.add hf.norm).pow_const 2).aestronglyMeasurable
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
        nlinarith [norm_nonneg (g m s), norm_nonneg (f s), hCg s, sq_nonneg (‖g m s‖ - ‖f s‖)]
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hb : ‖g m s - truncSym f N s‖ ≤ ‖g m s‖ + ‖f s‖ := by
          have := norm_sub_le (g m s) (truncSym f N s)
          linarith [norm_truncSym_le f N s]
        nlinarith [norm_nonneg (g m s - truncSym f N s), hb, norm_nonneg (g m s), norm_nonneg (f s)]
      · have h0 : Tendsto (fun N => g m s - truncSym f N s) atTop (𝓝 (g m s - f s)) :=
          tendsto_const_nhds.sub (tendsto_truncSym f s)
        exact h0.norm.pow 2
    -- combine the two limits by uniqueness
    exact tendsto_nhds_unique (htend_lhs.congr heqN) htend_rhs
  simp_rw [hnorm]
  -- Step 2: `∫ ‖g m − f‖² → 0` by DCT, then √.
  have hDCT : Tendsto (fun m => ∫ s, ‖g m s - f s‖ ^ 2 ∂(borelMeasure U_grp ξ)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := borelMeasure U_grp ξ)
      (F := fun m s => ‖g m s - f s‖ ^ 2) (f := fun _ => (0 : ℝ))
      (bound := fun s => (2 * ‖f s‖) ^ 2)
      (fun m => (((hg_meas m).sub hf).norm.pow_const 2).aestronglyMeasurable)
      (by
        refine Integrable.mono' (hξ.const_mul 4)
          (((hf.norm.const_mul 2)).pow_const 2).aestronglyMeasurable
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring_nf; rfl)
      (fun m => Eventually.of_forall fun s => ?_) (Eventually.of_forall fun s => ?_)
    · simpa using h
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hb : ‖g m s - f s‖ ≤ 2 * ‖f s‖ := by
        have := norm_sub_le (g m s) (f s)
        linarith [hdom m s]
      nlinarith [norm_nonneg (g m s - f s), hb, norm_nonneg (f s)]
    · have h0 : Tendsto (fun m => g m s - f s) atTop (𝓝 0) := by
        have := (hlim s).sub_const (f s); rwa [sub_self] at this
      have := h0.norm.pow 2; simpa using this
  have := hDCT.sqrt; rwa [Real.sqrt_zero] at this

/-! ## a.e.-equal symbols give equal calculus vectors -/

/-- If two bounded symbols agree `μ_ξ`-a.e. then the bounded calculus agrees at `ξ`:
`Φ(g)ξ = Φ(g')ξ`.  Because `‖Φ(g)ξ − Φ(g')ξ‖² = ∫‖g − g'‖² dμ_ξ = 0`. -/
theorem spectralCalculus_congr_ae (g g' : ℝ → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∃ C, ∀ ω, ‖g ω‖ ≤ C)
    (hg'_meas : Measurable g') (hg'_bdd : ∃ C, ∀ ω, ‖g' ω‖ ≤ C) (ξ : H)
    (hae : g =ᵐ[borelMeasure U_grp ξ] g') :
    spectralCalculus U_grp g hg_meas hg_bdd ξ = spectralCalculus U_grp g' hg'_meas hg'_bdd ξ := by
  have hzero : ‖spectralCalculus U_grp g hg_meas hg_bdd ξ
      - spectralCalculus U_grp g' hg'_meas hg'_bdd ξ‖ ^ 2 = 0 := by
    rw [← ContinuousLinearMap.sub_apply,
      ← spectralCalculus_sub U_grp g g' hg_meas hg_bdd hg'_meas hg'_bdd
        (hg_meas.sub hg'_meas) (bounded_sub hg_bdd hg'_bdd),
      norm_sq_spectralCalculus_apply]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with s hs
    rw [hs, sub_self, norm_zero]; simp
  have hsub : spectralCalculus U_grp g hg_meas hg_bdd ξ
      - spectralCalculus U_grp g' hg'_meas hg'_bdd ξ = 0 :=
    norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero)
  exact sub_eq_zero.mp hsub

/-- If two symbols agree `μ_ξ`-a.e. then the unbounded calculus agrees at `ξ`:
`(∫f dP)ξ = (∫f' dP)ξ`.  Both are strong limits of `Φ(truncₙ f)ξ`, `Φ(truncₙ f')ξ`, which agree
term-by-term by `spectralCalculus_congr_ae` (the truncations agree a.e.). -/
theorem pmapOfPVM_congr_ae (f f' : ℝ → ℂ) (hf : Measurable f) (hf' : Measurable f') {ξ : H}
    (hξ : Integrable (fun s => ‖f s‖ ^ 2) (borelMeasure U_grp ξ))
    (hξ' : Integrable (fun s => ‖f' s‖ ^ 2) (borelMeasure U_grp ξ))
    (hae : f =ᵐ[borelMeasure U_grp ξ] f') :
    pmapOfPVM U_grp f hf ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ⟩
      = pmapOfPVM U_grp f' hf' ⟨ξ, (ProjValMeasure.mem_pmapDomain U_grp.toPVM).mpr hξ'⟩ := by
  have htend1 := pmapOfPVM_apply_tendsto U_grp f hf hξ
  have htend2 := pmapOfPVM_apply_tendsto U_grp f' hf' hξ'
  refine tendsto_nhds_unique htend1 (htend2.congr fun N => ?_)
  rw [pmapTrunc_apply, pmapTrunc_apply]
  refine spectralCalculus_congr_ae U_grp (truncSym f' N) (truncSym f N) _ _ _ _ ξ ?_
  filter_upwards [hae] with s hs
  simp only [truncSym_apply, hs]

/-! ## The identity symbol computes the generator -/

/-- The identity symbol `s ↦ (s : ℂ)` under the unbounded calculus computes the generator:
`pmapOfPVM U (·:ℂ) x = generator U x` for `x ∈ D(generator U)`.  Two-sided cut-offs
`Φ(l·1_{[-m,m]})x = A(E([-m,m])x) = E([-m,m])(Ax)` converge to `pmapOfPVM U id x` (dominated
convergence, `f = (·:ℂ)`) on the one hand and to `Ax` (`tendsto_spectralProjection_Icc_univ`) on
the other. -/
theorem pmapOfPVM_id_eq_generator (x : (generator U_grp).domain)
    (hmem : (x : H) ∈ ProjValMeasure.pmapDomain U_grp.toPVM (fun s => (s : ℂ))) :
    pmapOfPVM U_grp (fun s => (s : ℂ)) Complex.measurable_ofReal ⟨(x : H), hmem⟩
      = generator U_grp x := by
  classical
  set μ := borelMeasure U_grp (x : H) with _hμ
  have hint : Integrable (fun s : ℝ => ‖(s : ℂ)‖ ^ 2) μ :=
    (ProjValMeasure.mem_pmapDomain _).mp hmem
  -- the two-sided cut-off symbols `l·1_{[-m,m]}`
  set G : ℕ → ℝ → ℂ := fun m s =>
    (s : ℂ) * Set.indicator (Set.Icc (-(m : ℝ)) (m : ℝ)) (fun _ => (1 : ℂ)) s with hG
  have hGmeas : ∀ m, Measurable (G m) := fun m =>
    Complex.measurable_ofReal.mul (measurable_const.indicator measurableSet_Icc)
  have hGbdd : ∀ m, ∃ C, ∀ ω, ‖G m ω‖ ≤ C := fun m => by
    refine ⟨(m : ℝ), fun s => ?_⟩
    rw [hG, norm_mul]
    by_cases hs : s ∈ Set.Icc (-(m : ℝ)) (m : ℝ)
    · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact abs_le_max_of_mem_Icc hs |>.trans (by simp)
    · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity
  have hGdom : ∀ m ω, ‖G m ω‖ ≤ ‖(ω : ℂ)‖ := fun m ω => by
    rw [hG, norm_mul]
    by_cases hs : ω ∈ Set.Icc (-(m : ℝ)) (m : ℝ)
    · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
    · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity
  have hGlim : ∀ ω, Tendsto (fun m => G m ω) atTop (𝓝 ((ω : ℂ))) := fun ω => by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈|ω|⌉₊] with m hm
    have hmem : ω ∈ Set.Icc (-(m : ℝ)) (m : ℝ) := by
      have hle : |ω| ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
      rw [Set.mem_Icc]
      exact ⟨by have := neg_abs_le ω; linarith, by have := le_abs_self ω; linarith⟩
    simp only [hG, Set.indicator_of_mem hmem, mul_one]
  -- limit 1: Φ(G m)x → pmapOfPVM id x
  have hlim1 := tendsto_spectralCalculus_pmapOfPVM_of_dominated U_grp (fun s => (s : ℂ))
    Complex.measurable_ofReal (ξ := (x : H)) hint G hGmeas hGbdd hGdom hGlim
  -- limit 2: Φ(G m)x = E([-m,m])(A x) → A x
  have hval : ∀ m, spectralCalculus U_grp (G m) (hGmeas m) (hGbdd m) (x : H)
      = spectralProjection U_grp (Set.Icc (-(m : ℝ)) (m : ℝ)) measurableSet_Icc
          (generator U_grp x) := by
    intro m
    have habs : ∀ y ∈ Set.Icc (-(m : ℝ)) (m : ℝ), |y| ≤ (m : ℝ) := fun y hy =>
      abs_le_max_of_mem_Icc hy |>.trans (by simp)
    rw [← generator_spectralProjection_comm U_grp measurableSet_Icc x,
      generator_spectralProjection U_grp measurableSet_Icc habs (x : H)]
  have hlim2 : Tendsto (fun m => spectralCalculus U_grp (G m) (hGmeas m) (hGbdd m) (x : H))
      atTop (𝓝 (generator U_grp x)) := by
    simp_rw [hval]
    exact tendsto_spectralProjection_Icc_univ U_grp (generator U_grp x)
  exact tendsto_nhds_unique hlim1 hlim2

end Spectra.QuantumMechanics.SpectralTheory

/-! ## HC2: `(Δ^{½})² = Δ` for the modular operator -/

open Spectra.QuantumMechanics.SpectralTheory
open Spectra.OneParameterUnitaryGroup
open Spectra.Borel

namespace Spectra.TomitaTakesaki

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-- The modular square-root cut-off symbol `√s · 1_{[0,m]}(s)`. -/
private noncomputable def sqrtCut (m : ℕ) : ℝ → ℂ :=
  fun s => (Real.sqrt s : ℂ) * Set.indicator (Set.Icc 0 (m : ℝ)) (fun _ => (1 : ℂ)) s

private lemma sqrtCut_meas (m : ℕ) : Measurable (sqrtCut m) :=
  measurable_sqrtC.mul (measurable_const.indicator measurableSet_Icc)

private lemma sqrtCut_bdd (m : ℕ) : ∃ C, ∀ s, ‖sqrtCut m s‖ ≤ C := by
  refine ⟨Real.sqrt (m : ℝ), fun s => ?_⟩
  rw [sqrtCut, norm_mul]
  by_cases hs : s ∈ Set.Icc 0 (m : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
    exact Real.sqrt_le_sqrt hs.2
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity

/-- `‖sqrtCut m s‖ ≤ ‖(√s : ℂ)‖` pointwise. -/
private lemma sqrtCut_dom (m : ℕ) (s : ℝ) : ‖sqrtCut m s‖ ≤ ‖(Real.sqrt s : ℂ)‖ := by
  rw [sqrtCut, norm_mul]
  by_cases hs : s ∈ Set.Icc 0 (m : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity

/-- `sqrtCut m s → (√s : ℂ)` pointwise. -/
private lemma sqrtCut_lim (s : ℝ) :
    Tendsto (fun m => sqrtCut m s) atTop (𝓝 ((Real.sqrt s : ℂ))) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop ⌈s⌉₊] with m hm
  by_cases hs : 0 ≤ s
  · have hmem : s ∈ Set.Icc 0 (m : ℝ) :=
      ⟨hs, (Nat.le_ceil s).trans (by exact_mod_cast hm)⟩
    simp only [sqrtCut, Set.indicator_of_mem hmem, mul_one]
  · -- s < 0: sqrtCut m s = √s · (indicator) and √s = 0
    have hsqrt : (Real.sqrt s : ℂ) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp hs)), Complex.ofReal_zero]
    simp only [sqrtCut, hsqrt, zero_mul]

/-- The positive-identity cut-off symbol `s · 1_{[0,m]}(s)` (` = (√·)² · 1_{[0,m]}`). -/
private noncomputable def posCut (m : ℕ) : ℝ → ℂ :=
  fun s => (s : ℂ) * Set.indicator (Set.Icc 0 (m : ℝ)) (fun _ => (1 : ℂ)) s

/-- The positive-identity symbol `s · 1_{[0,∞)}(s)`. -/
private noncomputable def posId : ℝ → ℂ :=
  fun s => (s : ℂ) * Set.indicator (Set.Ici (0 : ℝ)) (fun _ => (1 : ℂ)) s

private lemma posId_meas : Measurable posId :=
  Complex.measurable_ofReal.mul (measurable_const.indicator measurableSet_Ici)

private lemma posCut_meas (m : ℕ) : Measurable (posCut m) :=
  Complex.measurable_ofReal.mul (measurable_const.indicator measurableSet_Icc)

private lemma posCut_bdd (m : ℕ) : ∃ C, ∀ s, ‖posCut m s‖ ≤ C := by
  refine ⟨(m : ℝ), fun s => ?_⟩
  rw [posCut, norm_mul]
  by_cases hs : s ∈ Set.Icc 0 (m : ℝ)
  · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity

/-- `‖posCut m s‖ ≤ ‖posId s‖` pointwise. -/
private lemma posCut_dom (m : ℕ) (s : ℝ) : ‖posCut m s‖ ≤ ‖posId s‖ := by
  rw [posCut, posId, norm_mul, norm_mul]
  by_cases hs : 0 ≤ s
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hs)]
    by_cases hsm : s ∈ Set.Icc 0 (m : ℝ)
    · rw [Set.indicator_of_mem hsm]
    · rw [Set.indicator_of_notMem hsm, norm_zero, mul_zero]; positivity
  · have hnotIcc : s ∉ Set.Icc 0 (m : ℝ) := fun h => hs h.1
    have hnotIci : s ∉ Set.Ici (0 : ℝ) := fun h => hs h
    rw [Set.indicator_of_notMem hnotIcc, Set.indicator_of_notMem hnotIci, norm_zero, mul_zero]

/-- `posCut m s → posId s` pointwise. -/
private lemma posCut_lim (s : ℝ) : Tendsto (fun m => posCut m s) atTop (𝓝 (posId s)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop ⌈s⌉₊] with m hm
  by_cases hs : 0 ≤ s
  · have hmem : s ∈ Set.Icc 0 (m : ℝ) := ⟨hs, (Nat.le_ceil s).trans (by exact_mod_cast hm)⟩
    simp only [posCut, posId, Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Ici.mpr hs)]
  · have hnotIcc : s ∉ Set.Icc 0 (m : ℝ) := fun h => hs h.1
    have hnotIci : s ∉ Set.Ici (0 : ℝ) := fun h => hs h
    simp only [posCut, posId, Set.indicator_of_notMem hnotIcc, Set.indicator_of_notMem hnotIci]

/-- `(√s) · sqrtCut m s = posCut m s` as functions (both sides `(√s)²·1_{[0,m]} = s·1_{[0,m]}`
on `[0,∞)`, and `0` off it). -/
private lemma sqrtMul_sqrtCut_eq_posCut (m : ℕ) :
    (fun s => (Real.sqrt s : ℂ) * sqrtCut m s) = posCut m := by
  funext s
  rw [sqrtCut, posCut]
  by_cases hs : s ∈ Set.Icc 0 (m : ℝ)
  · rw [Set.indicator_of_mem hs, mul_one, mul_one, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hs.1]
  · rw [Set.indicator_of_notMem hs, mul_zero, mul_zero, mul_zero]

variable (hcyc : IsCyclic M Ω) (hsep : IsSeparating M Ω)

/-- Local abbreviation for the modular unitary group `U = genToGroup Δ` (so
`modularSqrt = pmapOfPVM U √`). -/
private noncomputable abbrev modU : OneParameterUnitaryGroup (H := H) :=
  genToGroup (modularOp_isSelfAdjoint hcyc hsep)

/-- The `√`-cut-off approximants converge to `Δ^{½}x`:  `Φ(sqrtCut m)x → Δ^{½}x` for `x ∈ D(Δ)`. -/
private theorem tendsto_sqrtCut_modularSqrt (x : (modularOp M Ω).domain) :
    Tendsto (fun m => spectralCalculus (modU hcyc hsep) (sqrtCut m) (sqrtCut_meas m) (sqrtCut_bdd m)
        (x : H)) atTop
      (𝓝 (modularSqrt hcyc hsep
        ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩)) := by
  set U := modU hcyc hsep with hU
  have hxg : (x : H) ∈ (generator U).domain := by rw [hU, generator_genToGroup]; exact x.2
  have hint : Integrable (fun s => ‖(Real.sqrt s : ℂ)‖ ^ 2) (borelMeasure U (x : H)) :=
    sqrt_integrable_of_mem_generator U ⟨(x : H), hxg⟩
  have h := tendsto_spectralCalculus_pmapOfPVM_of_dominated U (fun s => (Real.sqrt s : ℂ))
    measurable_sqrtC (ξ := (x : H)) hint sqrtCut sqrtCut_meas sqrtCut_bdd sqrtCut_dom sqrtCut_lim
  exact h

/-- `Φ(sqrtCut m)x ∈ D(Δ^{½})`. -/
private theorem sqrtCut_mem_modularSqrt_domain (x : (modularOp M Ω).domain) (m : ℕ) :
    spectralCalculus (modU hcyc hsep) (sqrtCut m) (sqrtCut_meas m) (sqrtCut_bdd m) (x : H)
      ∈ (modularSqrt hcyc hsep).domain := by
  set U := modU hcyc hsep with _hU
  have hfg_bdd : ∃ C, ∀ s, ‖(Real.sqrt s : ℂ) * sqrtCut m s‖ ≤ C := by
    have h := posCut_bdd m
    rw [← sqrtMul_sqrtCut_eq_posCut m] at h; exact h
  exact mem_pmapDomain_spectralCalculus U (fun s => (Real.sqrt s : ℂ)) (sqrtCut m)
    measurable_sqrtC (sqrtCut_meas m) (sqrtCut_bdd m) hfg_bdd (x : H)

/-- The outer square-root application: `Δ^{½}(Φ(sqrtCut m)x) = Φ(posCut m)x`. -/
private theorem modularSqrt_sqrtCut_apply (x : (modularOp M Ω).domain) (m : ℕ) :
    modularSqrt hcyc hsep
        ⟨spectralCalculus (modU hcyc hsep) (sqrtCut m) (sqrtCut_meas m) (sqrtCut_bdd m) (x : H),
          sqrtCut_mem_modularSqrt_domain hcyc hsep x m⟩
      = spectralCalculus (modU hcyc hsep) (posCut m) (posCut_meas m) (posCut_bdd m) (x : H) := by
  set U := modU hcyc hsep with _hU
  have hfg_meas : Measurable fun s => (Real.sqrt s : ℂ) * sqrtCut m s := by
    have h := posCut_meas m; rw [← sqrtMul_sqrtCut_eq_posCut m] at h; exact h
  have hfg_bdd : ∃ C, ∀ s, ‖(Real.sqrt s : ℂ) * sqrtCut m s‖ ≤ C := by
    have h := posCut_bdd m; rw [← sqrtMul_sqrtCut_eq_posCut m] at h; exact h
  have hmix := pmapOfPVM_spectralCalculus_of_mul_bounded U (fun s => (Real.sqrt s : ℂ))
    (sqrtCut m) measurable_sqrtC (sqrtCut_meas m) (sqrtCut_bdd m) hfg_meas hfg_bdd (x : H)
    (sqrtCut_mem_modularSqrt_domain hcyc hsep x m)
  have hcongr := congrArg (fun T : H →L[ℂ] H => T (x : H))
    (spectralCalculus_congr U (sqrtMul_sqrtCut_eq_posCut m)
      hfg_meas hfg_bdd (posCut_meas m) (posCut_bdd m))
  exact hmix.trans hcongr

/-- `pmapOfPVM U posId x = Δ x`:  `posId =ᵐ (·:ℂ)` w.r.t. `μ_x` (the modular measure charges no
negatives), and the identity symbol computes the generator `= Δ`. -/
private theorem pmapOfPVM_posId_eq_modularOp (x : (modularOp M Ω).domain)
    (hpos : (x : H) ∈ ProjValMeasure.pmapDomain (modU hcyc hsep).toPVM posId)
    (hid : (x : H) ∈ ProjValMeasure.pmapDomain (modU hcyc hsep).toPVM (fun s => (s : ℂ))) :
    pmapOfPVM (modU hcyc hsep) posId posId_meas ⟨(x : H), hpos⟩ = modularOp M Ω x := by
  set U := modU hcyc hsep with hU
  have hxg : (x : H) ∈ (generator U).domain := by rw [hU, generator_genToGroup]; exact x.2
  -- posId =ᵐ id  (μ_x charges no negatives)
  have hae : posId =ᵐ[borelMeasure U (x : H)] (fun s => (s : ℂ)) := by
    have hμ : borelMeasure U (x : H) (Set.Iio (0 : ℝ)) = 0 := by
      have := borelMeasure_modular_Iio_zero hcyc hsep (x : H)
      exact this
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun s hs => ?_) hμ
    simp only [Set.mem_setOf_eq] at hs
    rw [Set.mem_Iio]
    by_contra hs0
    exact hs (by rw [posId, Set.indicator_of_mem (Set.mem_Ici.mpr (not_lt.mp hs0)), mul_one])
  rw [pmapOfPVM_congr_ae U posId (fun s => (s : ℂ)) posId_meas Complex.measurable_ofReal
      hpos hid hae]
  have hgen := pmapOfPVM_id_eq_generator U ⟨(x : H), hxg⟩ hid
  rw [hgen]
  have hval : generator U ⟨(x : H), hxg⟩ = modularOp M Ω x := by
    have hgeneq : generator U = modularOp M Ω := by rw [hU, generator_genToGroup]
    exact (le_of_eq hgeneq).2 rfl
  exact hval

/-- `x ∈ D(pmapOfPVM U posId)` and `x ∈ D(pmapOfPVM U id)`, both from `∫ s² dμ_x < ∞`
(`weak_second_moment` on `x ∈ D(Δ)`). -/
private theorem sq_integrable_of_mem_modularOp (x : (modularOp M Ω).domain) :
    Integrable (fun s : ℝ => ‖(s : ℂ)‖ ^ 2) (borelMeasure (modU hcyc hsep) (x : H)) := by
  set U := modU hcyc hsep with hU
  have hxg : (x : H) ∈ (generator U).domain := by rw [hU, generator_genToGroup]; exact x.2
  have h2 := (weak_second_moment U ⟨(x : H), hxg⟩).1
  refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem posId_mem_pmapDomain (x : (modularOp M Ω).domain) :
    (x : H) ∈ ProjValMeasure.pmapDomain (modU hcyc hsep).toPVM posId := by
  set U := modU hcyc hsep with _hU
  rw [ProjValMeasure.mem_pmapDomain]
  refine (sq_integrable_of_mem_modularOp hcyc hsep x).mono'
    (posId_meas.norm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (by
    rw [posId, norm_mul]
    by_cases hs : s ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem hs, NormOneClass.norm_one, mul_one]
    · rw [Set.indicator_of_notMem hs, norm_zero, mul_zero]; positivity) 2

private theorem id_mem_pmapDomain (x : (modularOp M Ω).domain) :
    (x : H) ∈ ProjValMeasure.pmapDomain (modU hcyc hsep).toPVM (fun s => (s : ℂ)) := by
  rw [ProjValMeasure.mem_pmapDomain]
  exact sq_integrable_of_mem_modularOp hcyc hsep x

/-- `Φ(posCut m)x → Δ x`. -/
private theorem tendsto_posCut_modularOp (x : (modularOp M Ω).domain) :
    Tendsto (fun m => spectralCalculus (modU hcyc hsep) (posCut m) (posCut_meas m) (posCut_bdd m)
        (x : H)) atTop (𝓝 (modularOp M Ω x)) := by
  set U := modU hcyc hsep with _hU
  have h := tendsto_spectralCalculus_pmapOfPVM_of_dominated U posId posId_meas
    (ξ := (x : H)) ((ProjValMeasure.mem_pmapDomain _).mp (posId_mem_pmapDomain hcyc hsep x))
    posCut posCut_meas posCut_bdd posCut_dom posCut_lim
  rw [pmapOfPVM_posId_eq_modularOp hcyc hsep x (posId_mem_pmapDomain hcyc hsep x)
    (id_mem_pmapDomain hcyc hsep x)] at h
  exact h

/-! ### The two HC2 deliverables -/

/-- **HC2 (membership).**  `Δ^{½}x ∈ D(Δ^{½})` for `x ∈ D(Δ)`.  From closedness of the self-adjoint
`Δ^{½}`: the cut-off vectors `a_m = Φ(sqrtCut m)x ∈ D(Δ^{½})` converge to `Δ^{½}x`, and their
images `Δ^{½}a_m = Φ(posCut m)x` converge to `Δx`, so the limit point `(Δ^{½}x, Δx)` lies in the
(closed) graph. -/
theorem modularSqrt_mem_domain_of_mem_modularOp (x : (modularOp M Ω).domain) :
    (modularSqrt hcyc hsep
        ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩ : H)
      ∈ (modularSqrt hcyc hsep).domain := by
  set U := modU hcyc hsep with _hU
  set S := modularSqrt hcyc hsep with _hS
  -- closedness of the self-adjoint Δ^{½}
  have hclosed : IsClosed (S.graph : Set (H × H)) :=
    (modularSqrt_isSelfAdjoint hcyc hsep).isClosed
  -- the graph points `(a_m, Δ^{½} a_m) = (Φ(sqrtCut m)x, Φ(posCut m)x)`
  set a : ℕ → H := fun m => spectralCalculus U (sqrtCut m) (sqrtCut_meas m) (sqrtCut_bdd m) (x : H)
    with _ha
  set b : ℕ → H := fun m => spectralCalculus U (posCut m) (posCut_meas m) (posCut_bdd m) (x : H)
    with _hb
  have hmemgraph : ∀ m, (a m, b m) ∈ S.graph := by
    intro m
    have hmem := sqrtCut_mem_modularSqrt_domain hcyc hsep x m
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨a m, hmem⟩, rfl, modularSqrt_sqrtCut_apply hcyc hsep x m⟩
  -- the pair converges to `(Δ^{½}x, Δx)`
  have hconv : Tendsto (fun m => (a m, b m)) atTop
      (𝓝 (S ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩, modularOp M Ω x)) := by
    rw [nhds_prod_eq]
    exact (tendsto_sqrtCut_modularSqrt hcyc hsep x).prodMk (tendsto_posCut_modularOp hcyc hsep x)
  have hlimmem : (S ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩,
      modularOp M Ω x) ∈ S.graph :=
    hclosed.mem_of_tendsto hconv (Filter.Eventually.of_forall hmemgraph)
  rw [LinearPMap.mem_graph_iff] at hlimmem
  obtain ⟨z, hz1, hz2⟩ := hlimmem
  simp only at hz1 hz2
  rw [← hz1]
  exact z.2

/-- **HC2 (the square identity).**  `Δ^{½}(Δ^{½}x) = Δx` pointwise on `D(Δ)`.  Same closed-graph
limit: `(Δ^{½}x, Δx) ∈ graph(Δ^{½})` means precisely `Δ^{½}⟨Δ^{½}x, _⟩ = Δx`. -/
theorem modularSqrt_sq_apply (x : (modularOp M Ω).domain) :
    modularSqrt hcyc hsep
        ⟨modularSqrt hcyc hsep
            ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩,
          modularSqrt_mem_domain_of_mem_modularOp hcyc hsep x⟩
      = modularOp M Ω x := by
  set U := modU hcyc hsep with _hU
  set S := modularSqrt hcyc hsep with _hS
  have hclosed : IsClosed (S.graph : Set (H × H)) :=
    (modularSqrt_isSelfAdjoint hcyc hsep).isClosed
  set a : ℕ → H := fun m => spectralCalculus U (sqrtCut m) (sqrtCut_meas m) (sqrtCut_bdd m) (x : H)
    with _ha
  set b : ℕ → H := fun m => spectralCalculus U (posCut m) (posCut_meas m) (posCut_bdd m) (x : H)
    with _hb
  have hmemgraph : ∀ m, (a m, b m) ∈ S.graph := by
    intro m
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨a m, sqrtCut_mem_modularSqrt_domain hcyc hsep x m⟩, rfl,
      modularSqrt_sqrtCut_apply hcyc hsep x m⟩
  have hconv : Tendsto (fun m => (a m, b m)) atTop
      (𝓝 (S ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩, modularOp M Ω x)) := by
    rw [nhds_prod_eq]
    exact (tendsto_sqrtCut_modularSqrt hcyc hsep x).prodMk (tendsto_posCut_modularOp hcyc hsep x)
  have hlimmem : (S ⟨(x : H), modularOp_domain_le_modularSqrt_domain hcyc hsep x.2⟩,
      modularOp M Ω x) ∈ S.graph :=
    hclosed.mem_of_tendsto hconv (Filter.Eventually.of_forall hmemgraph)
  -- membership witness gives the value
  rw [LinearPMap.mem_graph_iff] at hlimmem
  obtain ⟨z, hz1, hz2⟩ := hlimmem
  simp only at hz1 hz2
  -- `S z = Δx` and `z = ⟨Δ^{½}x, _⟩`
  rw [← hz2]
  congr 1
  exact Subtype.ext hz1.symm

end Spectra.TomitaTakesaki

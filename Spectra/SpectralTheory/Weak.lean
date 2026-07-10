/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Algebra
import Spectra.SpectralTheory.Measure.PVM
/-!
# The weak spectral theorem: moment identities

For a self-adjoint generator `A = generator U_grp` of a one-parameter unitary group, and a
vector `ψ ∈ D(A)`, the diagonal spectral measure `μ_ψ = borelMeasure U_grp ψ` has its first two
moments equal to the matrix elements of `A`:

* `∫ s ∂μ_ψ = ⟪ψ, Aψ⟫.re`     (`weak_first_moment`)
* `∫ s² ∂μ_ψ = ‖Aψ‖²`          (`weak_second_moment`)

Both are proved by the standard **truncation** argument: on the bounded band `[-N,N]` the symbol
`λ·1_{[-N,N]}` is bounded, so the bounded functional calculus applies
(`norm_sq_spectralCalculus_apply`, `generator_spectralProjection`); letting `N → ∞`
(`tendsto_spectralProjection_Icc_univ`) and passing the integrals to the limit (monotone /
dominated convergence) gives the identities for the full line.

These are exactly the inputs the Born-rule moment identities
(`QuantumMechanics.BornRule.Observable.{bornExpectation_eq_inner, bornVariance_eq_central_moment}`)
were waiting on.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open Spectra.Borel
open SpectralMeasure
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.Fourier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Spectra.QuantumMechanics

variable (U_grp : OneParameterUnitaryGroup (H := H))

namespace SpectralTheory

/-! ## The two-sided resolution of the identity -/

/-- `⋃ N, [-N, N] = ℝ`. -/
private lemma iUnion_Icc_neg_nat_eq_univ :
    (⋃ N : ℕ, Set.Icc (-(N : ℝ)) (N : ℝ)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  refine Set.mem_iUnion.mpr ⟨N, ?_⟩
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · have := neg_abs_le x; linarith
  · have := le_abs_self x; linarith

/-- **The two-sided truncation converges to the identity**: `E([-N,N]) ξ → ξ` as `N → ∞`.
Only the one-sided versions (`tendsto_spectralProjection_Icc_{Ici,Iic}`) exist upstream; this
symmetric form is what the moment limits need.  Proof: `‖ξ - E([-N,N])ξ‖² = μ_ξ([-N,N]ᶜ) → 0`
by continuity of the finite measure `μ_ξ` from above on `[-N,N]ᶜ ↓ ∅`. -/
theorem tendsto_spectralProjection_Icc_univ (ξ : H) :
    Tendsto (fun N : ℕ =>
        spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc ξ)
      atTop (𝓝 ξ) := by
  haveI : IsFiniteMeasure (borelMeasure U_grp ξ) := borelMeasure_isFiniteMeasure U_grp ξ
  -- the complements decrease to ∅
  have hanti : Antitone (fun N : ℕ => (Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ) := by
    intro m n hmn
    refine Set.compl_subset_compl.mpr ?_
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hInter : (⋂ N : ℕ, (Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ) = ∅ := by
    rw [← Set.compl_iUnion, iUnion_Icc_neg_nat_eq_univ, Set.compl_univ]
  -- measure of the complements tends to 0
  have hmeas := tendsto_measure_iInter_atTop
    (μ := borelMeasure U_grp ξ)
    (fun N : ℕ => (measurableSet_Icc.compl).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hInter, measure_empty] at hmeas
  have htoReal : Tendsto
      (fun N : ℕ => ((borelMeasure U_grp ξ) ((Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ)).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hmeas
    simpa [Function.comp_def] using h
  -- rewrite the vector distance as that measure
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ N : ℕ,
      ‖spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc ξ - ξ‖
        = Real.sqrt (((borelMeasure U_grp ξ) ((Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ)).toReal) := by
    intro N
    have hsq :
        ‖spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ measurableSet_Icc.compl ξ‖ ^ 2
        = ((borelMeasure U_grp ξ) ((Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ)).toReal :=
      norm_sq_spectralProjection U_grp ((Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ) measurableSet_Icc.compl ξ
    have hc : spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc ξ - ξ
        = - spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ measurableSet_Icc.compl ξ := by
      rw [spectralProjection_compl U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc]
      simp [ContinuousLinearMap.sub_apply]
    rw [hc, norm_neg,
      ← Real.sqrt_sq (norm_nonneg
        (spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ measurableSet_Icc.compl ξ)),
      hsq]
  simp_rw [hnorm]
  have h := (Real.continuous_sqrt.tendsto 0).comp htoReal
  simpa [Function.comp_def, Real.sqrt_zero] using h

/-! ## The truncated second moment -/

/-- On the bounded band `[-N,N]`, the second moment is the squared norm of the truncated `Aφ`:
`∫_{[-N,N]} s² dμ_φ = ‖E([-N,N])(Aφ)‖²`.  The symbol `λ·1_{[-N,N]}` is bounded, so the bounded
calculus applies: `‖Φ(λ·1_{[-N,N]})φ‖² = ∫ ‖λ·1_{[-N,N]}‖² dμ_φ` and `Φ(λ·1_{[-N,N]})φ =
A(E([-N,N])φ) = E([-N,N])(Aφ)`. -/
private lemma setIntegral_sq_Icc_eq_normSq_proj (φ : (generator U_grp).domain) (N : ℕ) :
    ∫ l in Set.Icc (-(N : ℝ)) (N : ℝ), l ^ 2 ∂(borelMeasure U_grp (φ : H))
      = ‖spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (generator U_grp φ)‖ ^ 2 := by
  have habs : ∀ x ∈ Set.Icc (-(N : ℝ)) (N : ℝ), |x| ≤ max |(-(N : ℝ))| |(N : ℝ)| :=
    fun x hx => abs_le_max_of_mem_Icc hx
  have hval : spectralCalculus U_grp
        (fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
        (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs) (φ : H)
      = spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (generator U_grp φ) := by
    rw [← generator_spectralProjection U_grp measurableSet_Icc habs (φ : H)]
    exact generator_spectralProjection_comm U_grp measurableSet_Icc φ
  have hpt : ∀ l : ℝ,
      ‖(l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l‖ ^ 2
        = Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun l => l ^ 2) l := by
    intro l
    by_cases hl : l ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
    · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl, mul_one, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    · simp [Set.indicator_of_notMem hl]
  rw [← hval, norm_sq_spectralCalculus_apply U_grp _ (id_indicator_measurable measurableSet_Icc)
      (id_indicator_bdd habs) (φ : H), ← integral_indicator measurableSet_Icc]
  exact integral_congr_ae (Filter.Eventually.of_forall fun l => (hpt l).symm)

/-! ## The second moment -/

/-- **The second-moment identity** `∫ s² dμ_φ = ‖Aφ‖²` (with integrability), for `φ ∈ D(A)`.
The truncated identity `setIntegral_sq_Icc_eq_normSq_proj` says `∫_{[-N,N]} s² = ‖E([-N,N])Aφ‖²`;
monotone convergence (`lintegral_iSup`) lifts this to the full line, with the limit identified by
`tendsto_spectralProjection_Icc_univ` applied to `Aφ`. -/
theorem weak_second_moment (φ : (generator U_grp).domain) :
    Integrable (fun s : ℝ => s ^ 2) (borelMeasure U_grp (φ : H)) ∧
      ∫ s, s ^ 2 ∂(borelMeasure U_grp (φ : H)) = ‖generator U_grp φ‖ ^ 2 := by
  haveI : IsFiniteMeasure (borelMeasure U_grp (φ : H)) := borelMeasure_isFiniteMeasure U_grp _
  haveI : IsFiniteMeasure (borelMeasure U_grp (generator U_grp φ)) :=
    borelMeasure_isFiniteMeasure U_grp _
  -- the key lintegral identity
  have hlint : ∫⁻ l, ENNReal.ofReal (l ^ 2) ∂(borelMeasure U_grp (φ : H))
      = ENNReal.ofReal (‖generator U_grp φ‖ ^ 2) := by
    set μ := borelMeasure U_grp (φ : H) with _hμ
    set F : ℕ → ℝ → ℝ≥0∞ :=
      fun N l => ENNReal.ofReal (Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun l => l ^ 2) l)
      with hFdef
    have hFmeas : ∀ N, Measurable (F N) := fun N =>
      (((measurable_id.pow_const 2).indicator measurableSet_Icc)).ennreal_ofReal
    have hFmono : Monotone F := by
      intro m n hmn l
      apply ENNReal.ofReal_le_ofReal
      have hsub : Set.Icc (-(m : ℝ)) (m : ℝ) ⊆ Set.Icc (-(n : ℝ)) (n : ℝ) :=
        Set.Icc_subset_Icc (by exact_mod_cast neg_le_neg (by exact_mod_cast hmn))
          (by exact_mod_cast hmn)
      exact Set.indicator_le_indicator_of_subset hsub (fun x => sq_nonneg x) l
    have hsup : ∀ l, ⨆ N, F N l = ENNReal.ofReal (l ^ 2) := by
      intro l
      apply le_antisymm
      · refine iSup_le fun N => ?_
        simp only [hFdef]
        exact ENNReal.ofReal_le_ofReal (Set.indicator_le_self' (fun _ _ => sq_nonneg _) l)
      · obtain ⟨N, hN⟩ := exists_nat_ge |l|
        refine le_iSup_of_le N ?_
        have hl : l ∈ Set.Icc (-(N : ℝ)) (N : ℝ) := by
          rw [Set.mem_Icc]
          exact ⟨by have := neg_abs_le l; linarith, by have := le_abs_self l; linarith⟩
        simp only [hFdef, Set.indicator_of_mem hl, le_refl]
    have hFN : ∀ N, ∫⁻ l, F N l ∂μ
        = ENNReal.ofReal (‖spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
            (generator U_grp φ)‖ ^ 2) := by
      intro N
      have hg_nonneg : 0 ≤ᵐ[μ] Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun l => l ^ 2) :=
        Filter.Eventually.of_forall (fun l => Set.indicator_nonneg (fun a _ => sq_nonneg a) l)
      have hint : Integrable (Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun l => l ^ 2)) μ := by
        refine Integrable.mono' (integrable_const ((N : ℝ) ^ 2))
          (((measurable_id.pow_const 2).indicator measurableSet_Icc).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun l => ?_)
        rw [Real.norm_eq_abs]
        by_cases hl : l ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
        · rw [Set.indicator_of_mem hl, abs_of_nonneg (sq_nonneg l)]
          obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hl
          exact sq_le_sq' h1 h2
        · rw [Set.indicator_of_notMem hl, abs_zero]; positivity
      simp only [hFdef]
      rw [← ofReal_integral_eq_lintegral_ofReal hint hg_nonneg,
        integral_indicator measurableSet_Icc, setIntegral_sq_Icc_eq_normSq_proj]
    have key : ∫⁻ l, ENNReal.ofReal (l ^ 2) ∂μ = ⨆ N, ∫⁻ l, F N l ∂μ := by
      rw [← lintegral_iSup hFmeas hFmono]
      exact lintegral_congr fun l => (hsup l).symm
    rw [key]
    simp_rw [hFN]
    have hbmono : Monotone (fun N : ℕ =>
        ENNReal.ofReal (‖spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (generator U_grp φ)‖ ^ 2)) := by
      intro m n hmn
      apply ENNReal.ofReal_le_ofReal
      rw [norm_sq_spectralProjection, norm_sq_spectralProjection]
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact measure_mono (Set.Icc_subset_Icc
        (by exact_mod_cast neg_le_neg (by exact_mod_cast hmn)) (by exact_mod_cast hmn))
    have hbtends : Tendsto (fun N : ℕ =>
        ENNReal.ofReal (‖spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (generator U_grp φ)‖ ^ 2)) atTop (𝓝 (ENNReal.ofReal (‖generator U_grp φ‖ ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((tendsto_spectralProjection_Icc_univ U_grp (generator U_grp φ)).norm.pow 2)
    exact tendsto_nhds_unique (tendsto_atTop_iSup hbmono) hbtends
  refine ⟨⟨(continuous_pow 2).aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun s => sq_nonneg s), hlint]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun s => sq_nonneg s)
      (continuous_pow 2).aestronglyMeasurable, hlint, ENNReal.toReal_ofReal (sq_nonneg _)]

/-! ## The first moment -/

/-- On the bounded band `[-N,N]`, the first moment is the real part of the truncated matrix
element: `∫_{[-N,N]} s dμ_φ = (⟪φ, E([-N,N])(Aφ)⟫).re`.  The complex integrand `λ·1_{[-N,N]}`
is the coercion of the real `λ·1_{[-N,N]}`, so its integral is real. -/
private lemma setIntegral_id_Icc_eq_re_inner (φ : (generator U_grp).domain) (N : ℕ) :
    ∫ l in Set.Icc (-(N : ℝ)) (N : ℝ), l ∂(borelMeasure U_grp (φ : H))
      = (⟪(φ : H), spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (generator U_grp φ)⟫_ℂ).re := by
  have habs : ∀ x ∈ Set.Icc (-(N : ℝ)) (N : ℝ), |x| ≤ max |(-(N : ℝ))| |(N : ℝ)| :=
    fun x hx => abs_le_max_of_mem_Icc hx
  have hval : spectralCalculus U_grp
        (fun l => (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l)
        (id_indicator_measurable measurableSet_Icc) (id_indicator_bdd habs) (φ : H)
      = spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
          (generator U_grp φ) := by
    rw [← generator_spectralProjection U_grp measurableSet_Icc habs (φ : H)]
    exact generator_spectralProjection_comm U_grp measurableSet_Icc φ
  have hinner : ⟪(φ : H), spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
        (generator U_grp φ)⟫_ℂ
      = ((∫ l in Set.Icc (-(N : ℝ)) (N : ℝ), l ∂(borelMeasure U_grp (φ : H)) : ℝ) : ℂ) := by
    rw [← hval, inner_spectralCalculus U_grp _ (id_indicator_measurable measurableSet_Icc)
        (id_indicator_bdd habs) (φ : H) (φ : H),
      spectralForm_self U_grp (φ : H) (id_indicator_measurable measurableSet_Icc)
        (id_indicator_bdd habs)]
    rw [show (∫ l, (l : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun _ => (1 : ℂ)) l
            ∂(borelMeasure U_grp (φ : H)))
          = ∫ l, ((Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun l => l) l : ℝ) : ℂ)
            ∂(borelMeasure U_grp (φ : H)) from
        integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)]
    · rw [integral_complex_ofReal, integral_indicator measurableSet_Icc]
    · by_cases hl : l ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
      · simp [Set.indicator_of_mem hl]
      · simp [Set.indicator_of_notMem hl]
  rw [hinner, Complex.ofReal_re]

/-- **The first-moment identity** `∫ s dμ_φ = ⟪φ, Aφ⟫.re` (with integrability), for `φ ∈ D(A)`.
Integrability of `s` comes from that of `s²` (`weak_second_moment`) via `|s| ≤ 1 + s²`; the
identity is the `N → ∞` limit of `setIntegral_id_Icc_eq_re_inner`, with the left side handled by
dominated convergence and the right by continuity of `⟪φ, ·⟫` along `E([-N,N])(Aφ) → Aφ`. -/
theorem weak_first_moment (φ : (generator U_grp).domain) :
    Integrable (fun s : ℝ => s) (borelMeasure U_grp (φ : H)) ∧
      ∫ s, s ∂(borelMeasure U_grp (φ : H)) = (⟪(φ : H), generator U_grp φ⟫_ℂ).re := by
  haveI : IsFiniteMeasure (borelMeasure U_grp (φ : H)) := borelMeasure_isFiniteMeasure U_grp _
  have hsq := (weak_second_moment U_grp φ).1
  have hint_id : Integrable (fun s : ℝ => s) (borelMeasure U_grp (φ : H)) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hsq)
      measurable_id.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (|s| - 1), sq_abs s, abs_nonneg s]
  refine ⟨hint_id, ?_⟩
  -- left side: dominated convergence
  have hDCT : Tendsto (fun N : ℕ =>
      ∫ l in Set.Icc (-(N : ℝ)) (N : ℝ), l ∂(borelMeasure U_grp (φ : H)))
      atTop (𝓝 (∫ s, s ∂(borelMeasure U_grp (φ : H)))) := by
    have hd := tendsto_integral_of_dominated_convergence (μ := borelMeasure U_grp (φ : H))
      (F := fun N l => Set.indicator (Set.Icc (-(N : ℝ)) (N : ℝ)) (fun l => l) l)
      (f := fun l => l) (bound := fun l => ‖l‖)
      (fun N => (measurable_id.indicator measurableSet_Icc).aestronglyMeasurable)
      hint_id.norm
      (fun N => Filter.Eventually.of_forall fun l => norm_indicator_le_norm_self (fun l => l) l)
      (Filter.Eventually.of_forall fun l => ?_)
    · simpa only [integral_indicator measurableSet_Icc] using hd
    · obtain ⟨N₀, hN₀⟩ := exists_nat_ge |l|
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
      have hNN : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hl : l ∈ Set.Icc (-(N : ℝ)) (N : ℝ) := by
        rw [Set.mem_Icc]
        exact ⟨by have := neg_abs_le l; linarith, by have := le_abs_self l; linarith⟩
      exact (Set.indicator_of_mem hl (fun l => l)).symm
  -- right side: continuity of the inner product along E([-N,N])(Aφ) → Aφ
  have hcont : Continuous (fun y : H => (⟪(φ : H), y⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner continuous_id)
  have hInner : Tendsto (fun N : ℕ =>
      (⟪(φ : H), spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
        (generator U_grp φ)⟫_ℂ).re) atTop (𝓝 ((⟪(φ : H), generator U_grp φ⟫_ℂ).re)) :=
    (hcont.tendsto _).comp (tendsto_spectralProjection_Icc_univ U_grp (generator U_grp φ))
  have hDCT' : Tendsto (fun N : ℕ =>
      (⟪(φ : H), spectralProjection U_grp (Set.Icc (-(N : ℝ)) (N : ℝ)) measurableSet_Icc
        (generator U_grp φ)⟫_ℂ).re) atTop (𝓝 (∫ s, s ∂(borelMeasure U_grp (φ : H)))) := by
    simp_rw [← setIntegral_id_Icc_eq_re_inner U_grp φ]
    exact hDCT
  exact tendsto_nhds_unique hDCT' hInner

/-! ## Transfer to the spectral PVM of a self-adjoint operator

The moment identities for `generator U_grp` transport to the projection-valued measure
`PVM.spectralPVM hA` of an arbitrary self-adjoint `A`, via Stone's theorem
`generator (genToGroup hA) = A`.  `(PVM.spectralPVM hA).diag = borelMeasure (genToGroup hA)`
holds definitionally. -/

theorem spectralPVM_integrable_id {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H)
    (hψ : ψ ∈ A.domain) :
    Integrable (fun s : ℝ => s) ((PVM.spectralPVM hA).diag ψ) := by
  have hψ' : ψ ∈ (generator (genToGroup hA)).domain := by rw [generator_genToGroup hA]; exact hψ
  exact (weak_first_moment (genToGroup hA) ⟨ψ, hψ'⟩).1

theorem spectralPVM_integrable_sq {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H)
    (hψ : ψ ∈ A.domain) :
    Integrable (fun s : ℝ => s ^ 2) ((PVM.spectralPVM hA).diag ψ) := by
  have hψ' : ψ ∈ (generator (genToGroup hA)).domain := by rw [generator_genToGroup hA]; exact hψ
  exact (weak_second_moment (genToGroup hA) ⟨ψ, hψ'⟩).1

theorem spectralPVM_integral_id {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H)
    (hψ : ψ ∈ A.domain) :
    ∫ s, s ∂((PVM.spectralPVM hA).diag ψ) = (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re := by
  have hψ' : ψ ∈ (generator (genToGroup hA)).domain := by rw [generator_genToGroup hA]; exact hψ
  have hval : generator (genToGroup hA) ⟨ψ, hψ'⟩ = A ⟨ψ, hψ⟩ :=
    (le_of_eq (generator_genToGroup hA)).2 rfl
  have h := (weak_first_moment (genToGroup hA) ⟨ψ, hψ'⟩).2
  rw [show (PVM.spectralPVM hA).diag ψ = borelMeasure (genToGroup hA) ψ from rfl, h, hval]

theorem spectralPVM_integral_sq {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H)
    (hψ : ψ ∈ A.domain) :
    ∫ s, s ^ 2 ∂((PVM.spectralPVM hA).diag ψ) = ‖A ⟨ψ, hψ⟩‖ ^ 2 := by
  have hψ' : ψ ∈ (generator (genToGroup hA)).domain := by rw [generator_genToGroup hA]; exact hψ
  have hval : generator (genToGroup hA) ⟨ψ, hψ'⟩ = A ⟨ψ, hψ⟩ :=
    (le_of_eq (generator_genToGroup hA)).2 rfl
  have h := (weak_second_moment (genToGroup hA) ⟨ψ, hψ'⟩).2
  rw [show (PVM.spectralPVM hA).diag ψ = borelMeasure (genToGroup hA) ψ from rfl, h, hval]

/-- **The central second moment as a squared norm** for `PVM.spectralPVM hA`: with the mean
`m = ∫ s dμ`, the variance `∫ (s − m)² dμ` equals `‖Aψ − m·ψ‖²` — the Robertson quantity.
Both sides expand to `‖Aψ‖² − 2m² + m²‖ψ‖²` using the first and second moments and total mass. -/
theorem spectralPVM_central_moment {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (ψ : H)
    (hψ : ψ ∈ A.domain) :
    ∫ s, (s - ∫ t, t ∂((PVM.spectralPVM hA).diag ψ)) ^ 2 ∂((PVM.spectralPVM hA).diag ψ)
      = ‖A ⟨ψ, hψ⟩ - ((∫ t, t ∂((PVM.spectralPVM hA).diag ψ) : ℝ) : ℂ) • ψ‖ ^ 2 := by
  haveI : IsFiniteMeasure ((PVM.spectralPVM hA).diag ψ) := (PVM.spectralPVM hA).diag_finite ψ
  set μ := (PVM.spectralPVM hA).diag ψ with _hμ
  set m : ℝ := ∫ t, t ∂μ with hm
  have hint1 : Integrable (fun s : ℝ => s) μ := spectralPVM_integrable_id hA ψ hψ
  have hint2 : Integrable (fun s : ℝ => s ^ 2) μ := spectralPVM_integrable_sq hA ψ hψ
  have hI1 : m = (⟪ψ, A ⟨ψ, hψ⟩⟫_ℂ).re := spectralPVM_integral_id hA ψ hψ
  have hI2 : ∫ s, s ^ 2 ∂μ = ‖A ⟨ψ, hψ⟩‖ ^ 2 := spectralPVM_integral_sq hA ψ hψ
  have hmass : (μ Set.univ).toReal = ‖ψ‖ ^ 2 :=
    ProjValMeasure.diag_univ_toReal (PVM.spectralPVM hA) ψ
  have hLHS : ∫ s, (s - m) ^ 2 ∂μ = ‖A ⟨ψ, hψ⟩‖ ^ 2 - 2 * m ^ 2 + m ^ 2 * ‖ψ‖ ^ 2 := by
    have hpt : ∀ s : ℝ, (s - m) ^ 2 = s ^ 2 - 2 * m * s + m ^ 2 := fun s => by ring
    simp_rw [hpt]
    rw [integral_add, integral_sub, integral_const_mul, integral_const, measureReal_def, hI2,
      hmass, smul_eq_mul, ← hm]
    · ring
    · exact hint2
    · exact hint1.const_mul (2 * m)
    · exact hint2.sub (hint1.const_mul (2 * m))
    · exact integrable_const _
  have hconj : (⟪A ⟨ψ, hψ⟩, ψ⟫_ℂ).re = m := by
    rw [← inner_conj_symm, Complex.conj_re]; exact hI1.symm
  have hRHS : ‖A ⟨ψ, hψ⟩ - ((m : ℝ) : ℂ) • ψ‖ ^ 2
      = ‖A ⟨ψ, hψ⟩‖ ^ 2 - 2 * m ^ 2 + m ^ 2 * ‖ψ‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, hconj]
    rw [mul_pow, sq_abs]
    ring
  rw [hLHS]
  exact hRHS.symm

end SpectralTheory
end Spectra.QuantumMechanics

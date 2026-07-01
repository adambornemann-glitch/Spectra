/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Herglotz.FejerMeans
import Mathlib.MeasureTheory.Measure.Portmanteau

open Complex MeasureTheory Topology
open scoped NNReal
open Spectra.PositiveDefinite
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Herglotz

variable (U : H →L[ℂ] H) (hU : Operator.Unitary U)

/-- The **Fejér mean measure** on `𝕋 ≅ [0, 2π)`:
`σ_N = (1/2π) F_N(θ) dθ`.

This is a positive finite measure with total mass `‖ψ‖²`. The `_hU` hypothesis is not needed to
construct the measure itself, but is kept as an explicit argument (rather than dropped) so that
`fejerMeasure_isFiniteMeasure` below can recover it from the measure's own application and remain
an unconditional `instance`; `@[nolint unusedArguments]` silences the resulting linter complaint. -/
@[nolint unusedArguments]
noncomputable def fejerMeasure (U : H →L[ℂ] H) (_hU : Operator.Unitary U) (ψ : H) (N : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 (2 * Real.pi))).withDensity
    (fun θ => ENNReal.ofReal ((1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re))

/-- The Fejér mean density is continuous. -/
lemma fejerMeanDensity_continuous (U : H →L[ℂ] H) (ψ : H) (N : ℕ) :
    Continuous (fejerMeanDensity U ψ N) := by
  unfold fejerMeanDensity
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

/-- Total mass of the Fejér mean measure: `σ_N(𝕋) = ‖ψ‖²`. -/
lemma fejerMeasure_total (ψ : H) (N : ℕ) :
    (fejerMeasure U hU ψ N (Set.Icc 0 (2 * Real.pi))).toReal = ‖ψ‖ ^ 2 := by
  set S := Set.Icc (0 : ℝ) (2 * Real.pi) with hS
  set f := fun θ : ℝ => (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re with hf_def
  -- Non-negativity of density
  have hf_nn : ∀ θ, 0 ≤ f θ := by
    intro θ; simp only [hf_def]
    exact mul_nonneg (by positivity) (fejerMeanDensity_nonneg U hU ψ N θ)
  -- Continuity / integrability of density
  have hf_cts : Continuous f :=
    continuous_const.mul (Complex.continuous_re.comp (fejerMeanDensity_continuous U ψ N))
  have hf_int : IntegrableOn f S volume :=
    hf_cts.continuousOn.integrableOn_compact isCompact_Icc
  -- Step 1: Unfold and simplify the measure
  unfold fejerMeasure
  rw [withDensity_apply (fun θ => ENNReal.ofReal (1 / (2 * Real.pi) *
        (fejerMeanDensity U ψ N θ).re)) measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, Set.inter_self]
  -- Step 2: Convert lintegral to Bochner integral
  rw [← ofReal_integral_eq_lintegral_ofReal hf_int (ae_of_all _ hf_nn),
      ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_of_all _ (fun θ => hf_nn θ)))]
  -- Step 3: Pull out 1/(2π)
  rw [show f = fun θ => (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re from rfl,
      integral_const_mul]
  -- Step 4: Commute re and ∫ via ContinuousLinearMap.integral_comp_comm
  have hF_int : IntegrableOn (fejerMeanDensity U ψ N) S volume :=
    (fejerMeanDensity_continuous U ψ N).continuousOn.integrableOn_compact isCompact_Icc
  rw [show (fun θ => (fejerMeanDensity U ψ N θ).re) =
      (fun θ => Complex.reCLM (fejerMeanDensity U ψ N θ)) from rfl]
  -- reCLM commutes with set integral (term-mode to avoid notation issues)
  rw [show (∫ θ in S, Complex.reCLM (fejerMeanDensity U ψ N θ)) =
      Complex.reCLM (∫ θ in S, fejerMeanDensity U ψ N θ)
      from ContinuousLinearMap.integral_comp_comm _ hF_int]
  rw [fejerMeanDensity_integral U ψ N]
  -- Step 5: Simplify: (1/2π) * re(2π * c(0)) = re(c(0)) = ‖ψ‖²
  rw [unitaryCorrelation_zero]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
             mul_zero, sub_zero, Complex.ofReal_re]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  field_simp; abel

/-- The Fejér weight is symmetric: `w_N(-n) = w_N(n)`. -/
lemma fejerWeight_symm (N : ℕ) (n : ℤ) :
    fejerWeight N (-n) = fejerWeight N n := by
  simp [fejerWeight, Int.natAbs_neg]

/-- The Fejér mean density is self-conjugate (hence real-valued). -/
lemma fejerMeanDensity_conj (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (θ : ℝ) :
    starRingEnd ℂ (fejerMeanDensity U ψ N θ) = fejerMeanDensity U ψ N θ := by
  simp only [fejerMeanDensity, map_sum, map_mul, conj_ofReal]
  -- Each term is now: ↑(w(n)) * conj(c(n)) * exp(I * ↑n * ↑θ)
  -- Re-index by n ↦ -n
  apply Finset.sum_nbij (fun n => -n)
  · intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
  · intro a _ b _ hab; grind
  · intro n hn;
    simp only [Finset.coe_Icc, Set.image_neg_eq_neg, Set.neg_Icc, neg_neg, Set.mem_Icc]
    simp_all only [Finset.coe_Icc, Set.mem_Icc, and_self]
  · intro n hn
    rw [fejerWeight_symm, ← unitaryCorrelation_neg U hU ψ n]
    congr 1
    -- Goal: (starRingEnd ℂ) (cexp (-(I * ↑n * ↑θ))) = cexp (I * ↑n * ↑θ)
    rw [← Complex.exp_conj]
    congr 1
    -- Goal: (starRingEnd ℂ) (-(I * ↑n * ↑θ)) = I * ↑n * ↑θ
    simp [map_neg, map_mul, Complex.conj_I, conj_ofReal, map_intCast]

/-- The Fejér mean density is real: `F_N(θ) = ↑(re(F_N(θ)))`. -/
lemma fejerMeanDensity_ofReal (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (θ : ℝ) :
    fejerMeanDensity U ψ N θ = ↑((fejerMeanDensity U ψ N θ).re) := by
  set z := fejerMeanDensity U ψ N θ
  have h := fejerMeanDensity_conj U hU ψ N θ
  -- conj z = z implies z.im = 0
  have him : z.im = 0 := by
    have := congr_arg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  conv_lhs => rw [← Complex.re_add_im z]
  simp [him]

/-- Product of exponentials on the circle. -/
lemma exp_neg_mul_exp_pos (k n : ℤ) (θ : ℝ) :
    exp (-I * ↑k * ↑θ) * exp (I * ↑n * ↑θ) = exp (I * ↑(n - k) * ↑θ) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- The NNReal version of the Fejér density. -/
noncomputable def fejerDensityNNReal (U : H →L[ℂ] H) (ψ : H) (N : ℕ) (θ : ℝ) : ℝ≥0 :=
  ((1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re).toNNReal

/-- The ENNReal density equals the coercion of the NNReal density. -/
lemma fejerDensity_eq_coe (U : H →L[ℂ] H) (ψ : H) (N : ℕ) (θ : ℝ) :
    ENNReal.ofReal ((1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re) =
    ↑(fejerDensityNNReal U ψ N θ) := by
  simp [fejerDensityNNReal, ENNReal.ofReal]

/-- The NNReal density is measurable. -/
lemma fejerDensityNNReal_measurable (U : H →L[ℂ] H) (ψ : H) (N : ℕ) :
    Measurable (fejerDensityNNReal U ψ N) :=
  (measurable_const.mul
    (Complex.measurable_re.comp (fejerMeanDensity_continuous U ψ N).measurable)).real_toNNReal

/-- Coercion of the NNReal density back to ℝ. -/
lemma fejerDensityNNReal_coe (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (θ : ℝ) :
    (↑(fejerDensityNNReal U ψ N θ) : ℝ) = (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re := by
  simp only [fejerDensityNNReal]
  exact Real.coe_toNNReal _
    (mul_nonneg (by positivity) (fejerMeanDensity_nonneg U hU ψ N θ))

/-- The Fejér density times a Fourier exponential, integrated, gives
the Fourier coefficients weighted by the Fejér weights. -/
lemma fejer_fourier_integral (U : H →L[ℂ] H) (ψ : H) (N : ℕ) (n : ℤ) :
    ∫ x in Set.Icc (0 : ℝ) (2 * Real.pi),
      fejerMeanDensity U ψ N x * exp (I * ↑n * ↑x) =
    ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
      ↑(fejerWeight N k) * unitaryCorrelation U ψ k *
      ∫ x in Set.Icc (0 : ℝ) (2 * Real.pi), exp (I * ↑(n - k) * ↑x) := by
  set S := Set.Icc (0 : ℝ) (2 * Real.pi)
  -- Step 1: Rewrite integrand as a sum
  trans (∫ x in S, ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
      ↑(fejerWeight N k) * unitaryCorrelation U ψ k *
      exp (I * ↑(n - k) * ↑x))
  · exact setIntegral_congr_fun measurableSet_Icc (fun x _ => by
      simp only [fejerMeanDensity, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _
      rw [show (↑(fejerWeight N k) : ℂ) * unitaryCorrelation U ψ k *
          exp (-I * ↑k * ↑x) * exp (I * ↑n * ↑x) =
          ↑(fejerWeight N k) * unitaryCorrelation U ψ k *
          (exp (-I * ↑k * ↑x) * exp (I * ↑n * ↑x)) from by ring,
          exp_neg_mul_exp_pos])
  -- Step 2: Exchange sum and integral
  trans (∑ k ∈ Finset.Icc (-(N : ℤ)) N,
      ∫ x in S, ↑(fejerWeight N k) * unitaryCorrelation U ψ k *
      exp (I * ↑(n - k) * ↑x))
  · exact integral_finsetSum _ (fun k _ =>
      (continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))).continuousOn.integrableOn_compact
        isCompact_Icc)
  -- Step 3: Pull constants out of each integral
  apply Finset.sum_congr rfl; intro k _
  exact integral_const_mul _ _

  /-- Orthogonality for positive integer exponential. -/
lemma set_integral_cexp_pos_int (n : ℤ) :
    ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
    Complex.exp (I * ↑n * ↑θ) =
    (if n = 0 then ↑(2 * Real.pi) else 0) := by
    have h : (fun θ : ℝ => exp (I * ↑n * ↑θ)) = (fun θ : ℝ => exp (-I * ↑(-n) * ↑θ)) := by
      ext θ; congr 1; push_cast; ring
    rw [h, set_integral_cexp_neg_int]
    simp only [neg_eq_zero, ofReal_mul, ofReal_ofNat]

/-- The `n`-th Fourier coefficient of `σ_N` is `w_N(n) · c(n)`. (Currently unused.) -/
lemma fejerMeasure_fourier (ψ : H) (N : ℕ) (n : ℤ) :
    ∫ θ in Set.Icc 0 (2 * Real.pi),
      exp (I * n * θ) ∂(fejerMeasure U hU ψ N) =
    (fejerWeight N n : ℂ) * unitaryCorrelation U ψ n := by
  set S := Set.Icc (0 : ℝ) (2 * Real.pi) with hS
  unfold fejerMeasure
  -- Step 1: Rewrite density as NNReal coercion and apply withDensity conversion
  simp_rw [fejerDensity_eq_coe]
  rw [setIntegral_withDensity_eq_setIntegral_smul
        (fejerDensityNNReal_measurable U ψ N) _ measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, Set.inter_self]
  -- Step 2: Convert NNReal smul to ℂ multiplication
  have h_smul : ∀ θ, (fejerDensityNNReal U ψ N θ) • exp (I * ↑n * ↑θ) =
      (↑((1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re) : ℂ) *
      exp (I * ↑n * ↑θ) := by
    intro θ
    have h1 : (fejerDensityNNReal U ψ N θ : ℝ) =
        (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re :=
      fejerDensityNNReal_coe U hU ψ N θ
    rw [← h1, ← Complex.real_smul]
    exact NNReal.smul_def _ _
  trans (∫ x in S, (↑((1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N x).re) : ℂ) *
      exp (I * ↑n * ↑x))
  · exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => h_smul θ)
  -- Step 3: Replace ↑(r * re(F)) with (1/2π) * F using real-valuedness
  trans ((1 / (2 * (↑Real.pi : ℂ))) * ∫ x in S,
      fejerMeanDensity U ψ N x * exp (I * ↑n * ↑x))
  · trans (∫ x in S, (1 / (2 * (↑Real.pi : ℂ))) *
        (fejerMeanDensity U ψ N x * exp (I * ↑n * ↑x)))
    · exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by
        rw [Complex.ofReal_mul, ← fejerMeanDensity_ofReal U hU ψ N θ]
        push_cast; ring)
    · exact integral_const_mul _ _
  -- Step 4: Apply the helper, orthogonality, and collapse
  rw [fejer_fourier_integral U ψ N n]
  simp_rw [set_integral_cexp_pos_int, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
  · simp only [hn, ite_true]
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
    push_cast; field_simp
  · simp only [hn, ite_false, mul_zero]
    have hw : fejerWeight N n = 0 := by
      simp only [fejerWeight, Finset.mem_Icc, not_and_or, not_le] at hn ⊢
      simp only [ite_eq_right_iff]; intro h; omega
    simp [hw]

/-- The Fejér weight converges pointwise to 1: `w_N(n) → 1` as `N → ∞`. -/
lemma fejerWeight_tendsto (n : ℤ) :
    Filter.Tendsto (fun N : ℕ => fejerWeight N n) Filter.atTop (𝓝 1) := by
  -- Step 1: Eventually w_N(n) = 1 - |n|/(N+1)
  have h_ev : (fun N : ℕ => fejerWeight N n) =ᶠ[Filter.atTop]
      (fun N : ℕ => 1 - ↑n.natAbs / (↑N + 1 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop n.natAbs] with N hN
    simp only [fejerWeight, if_pos hN]
  rw [Filter.tendsto_congr' h_ev]
  -- Step 2: (↑N + 1 : ℝ) → atTop
  have h_atTop : Filter.Tendsto (fun N : ℕ => (↑N + 1 : ℝ))
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr; intro b
    filter_upwards [Filter.eventually_ge_atTop ⌈b⌉₊] with N hN
    calc b ≤ ↑⌈b⌉₊ := Nat.le_ceil b
      _ ≤ ↑N := by exact_mod_cast hN
      _ ≤ ↑N + 1 := le_add_of_nonneg_right zero_le_one
  -- Step 3: |n|/(N+1) → 0  (constant / atTop → 0)
  have h_div : Filter.Tendsto (fun N : ℕ => (↑n.natAbs : ℝ) / (↑N + 1))
      Filter.atTop (𝓝 0) := by
    have h_inv := tendsto_inv_atTop_zero.comp h_atTop
    have := (tendsto_const_nhds (x := (↑n.natAbs : ℝ))).mul h_inv
    rwa [mul_zero] at this
  -- Step 4: 1 - |n|/(N+1) → 1 - 0 = 1
  have h_sub := (tendsto_const_nhds (x := (1 : ℝ))).sub h_div
  rwa [sub_zero] at h_sub

/-- The Fejér weight converges pointwise to 1 in ℂ. -/
lemma fejerWeight_tendsto_complex (n : ℤ) :
    Filter.Tendsto (fun N : ℕ => (fejerWeight N n : ℂ)) Filter.atTop (𝓝 1) := by
  have := (Complex.continuous_ofReal.tendsto 1).comp (fejerWeight_tendsto n)
  simp only [Complex.ofReal_one] at this
  exact this

/-- The Fejér mean measure is a finite measure. (Currently unused.) -/
instance fejerMeasure_isFiniteMeasure (ψ : H) (N : ℕ) :
    IsFiniteMeasure (fejerMeasure U hU ψ N) := by
  unfold fejerMeasure
  apply isFiniteMeasure_withDensity
  set S := Set.Icc (0 : ℝ) (2 * Real.pi)
  set g := fun θ => (1 / (2 * Real.pi)) * (fejerMeanDensity U ψ N θ).re with hg_def
  have hg_nn : ∀ θ, 0 ≤ g θ :=
    fun θ => mul_nonneg (by positivity) (fejerMeanDensity_nonneg U hU ψ N θ)
  have hg_cts : Continuous g :=
    continuous_const.mul (Complex.continuous_re.comp (fejerMeanDensity_continuous U ψ N))
  have hg_int : IntegrableOn g S volume :=
    hg_cts.continuousOn.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hg_int (ae_of_all _ hg_nn)]
  exact ENNReal.ofReal_ne_top

/-- The circle `[0, 2π]` as a compact metrizable subtype of `ℝ`. -/
abbrev Circle := Set.Icc (0 : ℝ) (2 * Real.pi)

/-- `[0, 2π]` is nonempty. (Currently unused.) -/
private instance circleNonempty : Nonempty Circle :=
  ⟨⟨0, le_refl 0, by positivity⟩⟩

/-- `[0, 2π]` is compact (subtype version). (Currently unused.) -/
private instance circleCompactSpace : CompactSpace Circle :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- Measurable embedding of the circle into ℝ. -/
private lemma measurableEmbedding_circleVal :
    MeasurableEmbedding (Subtype.val : Circle → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Icc

/-- The Fejér measure transferred to `Circle` via pullback. -/
noncomputable def fejerMeasureOnCircle (ψ : H) (N : ℕ) : Measure Circle :=
  (fejerMeasure U hU ψ N).comap Subtype.val

/-- The circle Fejér measure is finite. -/
private instance fejerMeasureOnCircle_finite (ψ : H) (N : ℕ) :
    IsFiniteMeasure (fejerMeasureOnCircle U hU ψ N) := by
  constructor
  simp only [fejerMeasureOnCircle,
    measurableEmbedding_circleVal.comap_apply _ .univ,
    Set.image_univ, Subtype.range_coe]
  exact measure_lt_top _ _

/-- Integrals on `Circle` correspond to set-integrals on `[0, 2π]`. (Currently unused.) -/
lemma integral_circle_eq_setIntegral (f : ℝ → ℂ) (ψ : H) (N : ℕ) :
    ∫ x : Circle, f x.val ∂(fejerMeasureOnCircle U hU ψ N) =
    ∫ θ in Set.Icc 0 (2 * Real.pi), f θ ∂(fejerMeasure U hU ψ N) := by
  simp only [fejerMeasureOnCircle]
  rw [← measurableEmbedding_circleVal.integral_map,
      measurableEmbedding_circleVal.map_comap,
      Subtype.range_coe]

/-- Wrap the Fejér measure on Circle as a FiniteMeasure. -/
noncomputable def fejerFiniteMeasure (ψ : H) (N : ℕ) : FiniteMeasure Circle :=
  ⟨fejerMeasureOnCircle U hU ψ N, fejerMeasureOnCircle_finite U hU ψ N⟩

/-- The mass of each Fejér finite measure on Circle equals ‖ψ‖². (Currently unused.) -/
lemma fejerFiniteMeasure_mass_toReal (ψ : H) (N : ℕ) :
    ((fejerFiniteMeasure U hU ψ N : Measure Circle) Set.univ).toReal = ‖ψ‖ ^ 2 := by
  show ((fejerMeasureOnCircle U hU ψ N) Set.univ).toReal = ‖ψ‖ ^ 2
  rw [fejerMeasureOnCircle, measurableEmbedding_circleVal.comap_apply _ .univ,
      Set.image_univ, Subtype.range_coe]
  exact fejerMeasure_total U hU ψ N

/-- **Bolzano-Weierstrass in a countable product of compact intervals.**
    Any sequence in `∏ₙ [-Bₙ, Bₙ]` has a coordinatewise convergent
    subsequence. This follows from Tychonoff + first-countability of
    the countable product `ℕ → ℝ`. (Currently unused.) -/
lemma coordinatewise_convergent_subseq
    (x : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (_hB : ∀ n, 0 ≤ B n)
    (hbnd : ∀ n k, x n k ∈ Set.Icc (-(B n)) (B n)) :
    ∃ (L : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ n, Filter.Tendsto (fun k => x n (φ k)) Filter.atTop (𝓝 (L n)) := by
  set u : ℕ → (ℕ → ℝ) := fun k n => x n k
  have hmem : ∀ k, u k ∈ Set.pi Set.univ (fun n => Set.Icc (-(B n)) (B n)) :=
    fun k n _ => hbnd n k
  have hcpt : IsCompact (Set.pi Set.univ (fun n => Set.Icc (-(B n)) (B n))) := by
    simp only [Set.pi_univ_Icc]
    exact isCompact_Icc
  obtain ⟨L, -, φ, hφ, hconv⟩ := hcpt.tendsto_subseq hmem
  rw [tendsto_pi_nhds] at hconv
  exact ⟨L, φ, hφ, fun n => hconv n⟩

/-- Integration against a probability measure is 1-Lipschitz in the
    bounded continuous function argument. (Currently unused.) -/
lemma integral_dist_le_bcf_dist (f g : BoundedContinuousFunction Circle ℝ)
    (μ : ProbabilityMeasure Circle) :
    dist (∫ x, f x ∂μ.toMeasure) (∫ x, g x ∂μ.toMeasure) ≤ dist f g := by
  haveI : IsProbabilityMeasure μ.toMeasure := μ.prop
  haveI : IsFiniteMeasure μ.toMeasure := inferInstance
  rw [Real.dist_eq, ← integral_sub (f.integrable μ.toMeasure) (g.integrable μ.toMeasure)]
  calc |∫ x, (f x - g x) ∂μ.toMeasure|
      ≤ ∫ x, |f x - g x| ∂μ.toMeasure :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _, dist f g ∂μ.toMeasure := by
        apply integral_mono_of_nonneg
          (ae_of_all _ fun _ => abs_nonneg _)
          (integrable_const _)
          (ae_of_all _ fun x => by
            simp [← Real.dist_eq]
            exact BoundedContinuousFunction.dist_coe_le_dist x)
    _ = dist f g := by
        rw [integral_const, smul_eq_mul]
        simp only [probReal_univ, one_mul]

end Spectra.Herglotz

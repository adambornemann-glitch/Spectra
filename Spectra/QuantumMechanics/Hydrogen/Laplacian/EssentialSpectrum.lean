/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.SpectralTheory.Essential.Defs
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Basic

/-!
# The essential spectrum of the free Laplacian: `σ_ess(−Δ) = [0,∞)`

`essSpectrum_laplacian : Spectra.Essential.essSpectrum laplacian_isSelfAdjoint = Set.Ici 0`.

The proof builds singular (Weyl) sequences directly in momentum space, using the Fourier
diagonalization `fourier_weakLaplacian` (`𝓕(−Δψ) =ᵐ (2π)²‖ξ‖²·𝓕ψ`).  For `λ ≥ 0` the
sequence is `ψₙ := 𝓕⁻¹(normalized indicator of the shrinking shell
`{ξ : |(2π)²‖ξ‖² − λ| ≤ 1/(n+1)}`)`; it is
normalized (Plancherel), weakly null (the shells shrink to a measure-zero sphere), and an
approximate eigenvector (`|symbol − λ| ≤ 1/(n+1)` on the shell).  The reverse inclusion
`σ_ess ⊆ [0,∞)` is positivity of `−Δ`.

## Main statements

* `mem_essSpectrum_laplacian` — the forward inclusion `[0,∞) ⊆ σ_ess(−Δ)`: every `λ ≥ 0`
  belongs to the essential spectrum, witnessed by the momentum-space Weyl sequence.
* `essSpectrum_laplacian_subset_Ici` — the reverse inclusion `σ_ess(−Δ) ⊆ [0,∞)`, from
  positivity of `−Δ`.
* `essSpectrum_laplacian` — the headline identity `σ_ess(−Δ) = [0,∞)`.
-/

open MeasureTheory Complex Filter Topology Spectra.Sobolev
open scoped InnerProductSpace ENNReal NNReal

namespace Spectra.QuantumMechanics.Hydrogen

/-- The momentum-space **energy shell** `{ξ : |(2π)²‖ξ‖² − λ| ≤ ε}`. -/
def laplacianShell (lam ε : ℝ) : Set R3 := {ξ | |laplacianSymbol ξ - lam| ≤ ε}

/-- The momentum-space symbol `ξ ↦ (2π)²‖ξ‖²` of `−Δ` is continuous. -/
lemma continuous_laplacianSymbol : Continuous laplacianSymbol := by
  unfold laplacianSymbol; fun_prop

/-- Each energy shell `{ξ : |symbol ξ − λ| ≤ ε}` is a measurable set. -/
lemma measurableSet_laplacianShell (lam ε : ℝ) : MeasurableSet (laplacianShell lam ε) :=
  (isClosed_le (continuous_abs.comp (continuous_laplacianSymbol.sub continuous_const))
    continuous_const).measurableSet

/-- The shell is contained in a ball of radius `√(λ+ε)/(2π)` (for `λ, ε ≥ 0`). -/
lemma laplacianShell_subset_closedBall {lam ε : ℝ} (_hlam : 0 ≤ lam) (_hε : 0 ≤ ε) :
    laplacianShell lam ε ⊆ Metric.closedBall 0 (Real.sqrt (lam + ε) / (2 * Real.pi)) := by
  intro ξ hξ
  simp only [laplacianShell, Set.mem_setOf_eq] at hξ
  rw [Metric.mem_closedBall, dist_zero_right]
  have _hpi : 0 < 2 * Real.pi := by positivity
  have hsym : (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 ≤ lam + ε := by
    have h := (abs_le.mp hξ).2
    unfold laplacianSymbol at h
    linarith
  have hnsq : ‖ξ‖ ^ 2 ≤ (lam + ε) / (2 * Real.pi) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith [hsym]
  calc ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((lam + ε) / (2 * Real.pi) ^ 2) := Real.sqrt_le_sqrt hnsq
    _ = Real.sqrt (lam + ε) / (2 * Real.pi) := by
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]

/-- The energy shell has finite volume (for `λ, ε ≥ 0`): it sits inside a ball. -/
lemma volume_laplacianShell_lt_top {lam ε : ℝ} (hlam : 0 ≤ lam) (hε : 0 ≤ ε) :
    volume (laplacianShell lam ε) < ∞ :=
  lt_of_le_of_lt (measure_mono (laplacianShell_subset_closedBall hlam hε))
    (measure_closedBall_lt_top)

/-- A momentum on the energy sphere: `(2π)²‖ξ₀‖² = λ`. -/
lemma laplacianSymbol_energyPoint {lam : ℝ} (hlam : 0 ≤ lam) :
    laplacianSymbol (EuclideanSpace.single (0 : Fin 3) (Real.sqrt lam / (2 * Real.pi))) = lam := by
  unfold laplacianSymbol
  rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow,
    Real.sq_sqrt hlam]
  field_simp

/-- The energy shell has positive volume (for `λ ≥ 0`, `ε > 0`): it contains a nonempty open set
around a point of the energy sphere. -/
lemma volume_laplacianShell_pos {lam ε : ℝ} (hlam : 0 ≤ lam) (hε : 0 < ε) :
    0 < volume (laplacianShell lam ε) := by
  have hopen : IsOpen {ξ : R3 | |laplacianSymbol ξ - lam| < ε} :=
    isOpen_lt (continuous_abs.comp (continuous_laplacianSymbol.sub continuous_const))
      continuous_const
  have hne : {ξ : R3 | |laplacianSymbol ξ - lam| < ε}.Nonempty :=
    ⟨EuclideanSpace.single (0 : Fin 3) (Real.sqrt lam / (2 * Real.pi)), by
      change |laplacianSymbol _ - lam| < ε
      rw [laplacianSymbol_energyPoint hlam, sub_self, abs_zero]; exact hε⟩
  have hsub : {ξ : R3 | |laplacianSymbol ξ - lam| < ε} ⊆ laplacianShell lam ε := by
    intro ξ hξ
    simp only [Set.mem_setOf_eq, laplacianShell] at hξ ⊢
    exact le_of_lt hξ
  exact lt_of_lt_of_le (hopen.measure_pos (μ := volume) hne) (measure_mono hsub)

/-- The shrinking shells `Sₙ = {|symbol − λ| ≤ 1/(n+1)}` intersect in the energy sphere. -/
lemma iInter_laplacianShell (lam : ℝ) :
    ⋂ n : ℕ, laplacianShell lam (1 / (n + 1)) = {ξ : R3 | laplacianSymbol ξ = lam} := by
  ext ξ
  simp only [Set.mem_iInter, laplacianShell, Set.mem_setOf_eq]
  constructor
  · intro h
    have hle : |laplacianSymbol ξ - lam| ≤ 0 :=
      ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall h)
    have : laplacianSymbol ξ - lam = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    linarith
  · intro h n
    rw [h, sub_self, abs_zero]; positivity

/-- The energy sphere `{ξ : symbol ξ = λ}` (for `λ ≥ 0`) has Lebesgue measure zero: it is the
sphere of radius `√λ/(2π)`, and spheres are Haar-null. -/
lemma volume_laplacianSymbol_eq_zero {lam : ℝ} (hlam : 0 ≤ lam) :
    volume {ξ : R3 | laplacianSymbol ξ = lam} = 0 := by
  have hset : {ξ : R3 | laplacianSymbol ξ = lam}
      = Metric.sphere (0 : R3) (Real.sqrt lam / (2 * Real.pi)) := by
    ext ξ
    simp only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right]
    constructor
    · intro h
      have hsq : ‖ξ‖ ^ 2 = lam / (2 * Real.pi) ^ 2 := by
        rw [eq_div_iff (by positivity)]; unfold laplacianSymbol at h; linarith
      rw [← Real.sqrt_sq (norm_nonneg ξ), hsq, Real.sqrt_div' _ (by positivity),
        Real.sqrt_sq (by positivity)]
    · intro h
      unfold laplacianSymbol
      rw [h, div_pow, Real.sq_sqrt hlam]; field_simp
  rw [hset]; exact MeasureTheory.Measure.addHaar_sphere volume 0 _

/-! ### The momentum-space Weyl sequence (for `λ ≥ 0`) -/

section Construction
variable (lam : ℝ) (hlam : 0 ≤ lam)

/-- The L²-normalized indicator of the `n`-th energy shell, in momentum space. -/
noncomputable def shellFun (n : ℕ) : l2R3 :=
  indicatorConstLp 2 (measurableSet_laplacianShell lam (1 / (n + 1)))
    (volume_laplacianShell_lt_top hlam (by positivity)).ne
    (((Real.sqrt (volume (laplacianShell lam (1 / (n + 1)))).toReal)⁻¹ : ℝ) : ℂ)

/-- The shell indicator `gₙ` is L²-normalized: `‖gₙ‖ = 1`. -/
lemma norm_shellFun (n : ℕ) : ‖shellFun lam hlam n‖ = 1 := by
  have hVpos : 0 < (volume (laplacianShell lam (1 / (n + 1)))).toReal :=
    ENNReal.toReal_pos (volume_laplacianShell_pos hlam (by positivity)).ne'
      (volume_laplacianShell_lt_top hlam (by positivity)).ne
  have hsqrt : 0 < Real.sqrt (volume (laplacianShell lam (1 / (n + 1)))).toReal :=
    Real.sqrt_pos.mpr hVpos
  rw [shellFun, norm_indicatorConstLp (by norm_num) (by norm_num), measureReal_def,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hsqrt.le),
    show ((1 : ℝ) / (2 : ℝ≥0∞).toReal) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact inv_mul_cancel₀ hsqrt.ne'

/-- The candidate Weyl sequence for `−Δ` at `λ`: `ψₙ := 𝓕⁻¹(gₙ)`. -/
noncomputable def weylSeq (n : ℕ) : l2R3 := fourierL2.symm (shellFun lam hlam n)

/-- The Weyl vector `ψₙ = 𝓕⁻¹(gₙ)` is L²-normalized: `‖ψₙ‖ = 1` (Plancherel). -/
lemma norm_weylSeq (n : ℕ) : ‖weylSeq lam hlam n‖ = 1 := by
  rw [weylSeq, LinearIsometryEquiv.norm_map, norm_shellFun]

/-- The Fourier transform of the Weyl vector is the shell indicator: `𝓕ψₙ = gₙ`. -/
@[simp] lemma fourierL2_weylSeq (n : ℕ) : fourierL2 (weylSeq lam hlam n) = shellFun lam hlam n := by
  rw [weylSeq, LinearIsometryEquiv.apply_symm_apply]

/-- `gₙ` is a.e. the constant `c` on the shell, `0` off it. -/
lemma shellFun_coeFn (n : ℕ) :
    (shellFun lam hlam n : R3 → ℂ) =ᵐ[volume]
      (laplacianShell lam (1 / (n + 1))).indicator
        (fun _ => (((Real.sqrt (volume (laplacianShell lam (1 / (n + 1)))).toReal)⁻¹ : ℝ) : ℂ))
      := by
  rw [shellFun]; exact indicatorConstLp_coeFn

/-- The Weyl vector lies in the domain `H²(ℝ³)`: `gₙ` has bounded support, so `(1+‖ξ‖²)·gₙ ∈ L²`. -/
lemma memSobolevH2_weylSeq (n : ℕ) : MemSobolevH2 (weylSeq lam hlam n) := by
  have hεpos : (0 : ℝ) < 1 / (n + 1) := by positivity
  set R : ℝ := Real.sqrt (lam + 1 / (n + 1)) / (2 * Real.pi) with _hR
  apply memSobolevH2_of_fourier_decay
  rw [fourierL2_weylSeq]
  refine MemLp.mono' (g := fun ξ => (1 + R ^ 2) * ‖(shellFun lam hlam n : R3 → ℂ) ξ‖)
    (((Lp.memLp (shellFun lam hlam n)).norm).const_mul (1 + R ^ 2)) ?_ ?_
  · exact ((Complex.continuous_ofReal.comp
      (continuous_const.add (continuous_norm.pow 2))).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable _)
  · filter_upwards [shellFun_coeFn lam hlam n] with ξ hξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hmem : ξ ∈ laplacianShell lam (1 / (n + 1))
    · have hle : ‖ξ‖ ^ 2 ≤ R ^ 2 := by
        have hball := laplacianShell_subset_closedBall hlam hεpos.le hmem
        rw [Metric.mem_closedBall, dist_zero_right] at hball
        nlinarith [norm_nonneg ξ]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    · rw [hξ, Set.indicator_of_notMem hmem]; simp

/-- The approximate-eigenvector estimate: `‖(−Δ − λ)ψₙ‖ ≤ 1/(n+1)`.  Under `𝓕`, the defect is
`(laplacianSymbol − λ)·gₙ`, bounded by `1/(n+1)` on the shell where `gₙ` lives. -/
lemma eigendefect_weylSeq (n : ℕ) :
    ‖weakLaplacian (weylSeq lam hlam n) (memSobolevH2_weylSeq lam hlam n)
      - (lam : ℂ) • (weylSeq lam hlam n)‖ ≤ 1 / (n + 1) := by
  have hcoe : (fourierL2 (weakLaplacian (weylSeq lam hlam n) (memSobolevH2_weylSeq lam hlam n)
        - (lam : ℂ) • weylSeq lam hlam n) : R3 → ℂ)
      =ᵐ[volume] fun ξ => ((laplacianSymbol ξ : ℂ) - lam) * (shellFun lam hlam n : R3 → ℂ) ξ := by
    rw [map_sub, map_smul, fourierL2_weylSeq]
    filter_upwards [Lp.coeFn_sub (fourierL2 (weakLaplacian (weylSeq lam hlam n)
        (memSobolevH2_weylSeq lam hlam n))) ((lam : ℂ) • shellFun lam hlam n),
      Lp.coeFn_smul (lam : ℂ) (shellFun lam hlam n),
      fourier_weakLaplacian (weylSeq lam hlam n) (memSobolevH2_weylSeq lam hlam n)] with ξ h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, fourierL2_weylSeq, smul_eq_mul]
    ring
  rw [← fourierL2.norm_map (weakLaplacian (weylSeq lam hlam n) (memSobolevH2_weylSeq lam hlam n)
    - (lam : ℂ) • weylSeq lam hlam n)]
  refine le_trans (Lp.norm_le_norm_of_ae_le
    (g := ((1 / (n + 1) : ℝ) : ℂ) • shellFun lam hlam n) ?_) ?_
  · filter_upwards [hcoe, Lp.coeFn_smul ((1 / (n + 1) : ℝ) : ℂ) (shellFun lam hlam n),
      shellFun_coeFn lam hlam n] with ξ hc hs hind
    rw [hc, hs, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    by_cases hmem : ξ ∈ laplacianShell lam (1 / (n + 1))
    · have hm : |laplacianSymbol ξ - lam| ≤ 1 / (n + 1) := hmem
      exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    · rw [hind, Set.indicator_of_notMem hmem]; simp
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      norm_shellFun, mul_one]

include hlam in
/-- `∫_{Sₙ} ‖𝓕h‖² → 0`: the shells shrink to the measure-zero energy sphere, so by dominated
convergence the mass of `‖𝓕h‖² ∈ L¹` on them vanishes. -/
lemma tendsto_setIntegral_normSq (h : l2R3) :
    Tendsto (fun (n : ℕ) => ∫ ξ in laplacianShell lam (1 / (n + 1)),
        ‖(fourierL2 h : R3 → ℂ) ξ‖ ^ 2 ∂volume) atTop (𝓝 0) := by
  have hmeas : AEStronglyMeasurable (fun ξ => ‖(fourierL2 h : R3 → ℂ) ξ‖ ^ 2) volume :=
    (Lp.aestronglyMeasurable (fourierL2 h)).norm.pow 2
  have hint : Integrable (fun ξ => ‖(fourierL2 h : R3 → ℂ) ξ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (fourierL2 h))).mp
      (Lp.memLp (fourierL2 h))
  have hsphere : ∀ᵐ ξ ∂volume, laplacianSymbol ξ ≠ lam := by
    rw [ae_iff]; simp only [not_not]; exact volume_laplacianSymbol_eq_zero hlam
  have hdct : Tendsto (fun (n : ℕ) => ∫ ξ, (laplacianShell lam (1 / (n + 1))).indicator
      (fun ξ => ‖(fourierL2 h : R3 → ℂ) ξ‖ ^ 2) ξ ∂volume) atTop
        (𝓝 (∫ (_ξ : R3), (0 : ℝ) ∂volume)) := by
    refine tendsto_integral_of_dominated_convergence
      (bound := fun ξ => ‖(fourierL2 h : R3 → ℂ) ξ‖ ^ 2)
      (F_measurable := fun n => hmeas.indicator (measurableSet_laplacianShell lam (1 / (n + 1))))
      (bound_integrable := hint) (h_bound := ?_) (h_lim := ?_)
    · intro n
      filter_upwards with ξ
      exact (norm_indicator_le_norm_self _ ξ).trans_eq (Real.norm_of_nonneg (sq_nonneg _))
    · filter_upwards [hsphere] with ξ hξ
      have hδ : 0 < |laplacianSymbol ξ - lam| := abs_pos.mpr (sub_ne_zero.mpr hξ)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
        (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hδ))] with n hn
      refine (Set.indicator_of_notMem (fun hmem => ?_) _).symm
      have h1 : |laplacianSymbol ξ - lam| ≤ 1 / (n + 1) := hmem
      exact absurd (Set.mem_Iio.mp hn) (not_lt.mpr h1)
  simp only [integral_zero] at hdct
  exact hdct.congr fun n => integral_indicator (measurableSet_laplacianShell lam (1 / (n + 1)))

include hlam in
/-- Cauchy–Schwarz bound: `‖⟪𝓕h, gₙ⟫‖ ≤ √(∫_{Sₙ}‖𝓕h‖²)` (because `gₙ` is normalized and lives on
`Sₙ`). -/
lemma norm_inner_shellFun_le (h : l2R3) (n : ℕ) :
    ‖⟪fourierL2 h, shellFun lam hlam n⟫_ℂ‖
      ≤ Real.sqrt (∫ ξ in laplacianShell lam (1 / (n + 1)),
          ‖(fourierL2 h : R3 → ℂ) ξ‖ ^ 2 ∂volume) := by
  have hεpos : (0 : ℝ) < 1 / (n + 1) := by positivity
  set S : Set R3 := laplacianShell lam (1 / (n + 1)) with _hSdef
  have _hmeasS : MeasurableSet S := measurableSet_laplacianShell lam (1 / (n + 1))
  have hfin : volume S ≠ ∞ := (volume_laplacianShell_lt_top hlam hεpos.le).ne
  have hVpos : 0 < (volume S).toReal :=
    ENNReal.toReal_pos (volume_laplacianShell_pos hlam hεpos).ne' hfin
  set c : ℝ := (Real.sqrt (volume S).toReal)⁻¹ with hc
  have hsqrtV : 0 < Real.sqrt (volume S).toReal := Real.sqrt_pos.mpr hVpos
  haveI : IsFiniteMeasure (volume.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_laplacianShell_lt_top hlam hεpos.le⟩
  -- Cauchy–Schwarz: ∫_S ‖F‖ ≤ √(∫_S‖F‖²)·√(vol S)
  have hCS : ∫ x in S, ‖(fourierL2 h : R3 → ℂ) x‖ ∂volume
      ≤ Real.sqrt (∫ x in S, ‖(fourierL2 h : R3 → ℂ) x‖ ^ 2 ∂volume)
        * Real.sqrt (volume S).toReal := by
    have hp2 : ENNReal.ofReal 2 = 2 := by simp
    have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict S) (p := 2) (q := 2)
      (f := fun x => ‖(fourierL2 h : R3 → ℂ) x‖) (g := fun _ => (1 : ℝ))
      (by rw [Real.holderConjugate_iff]; norm_num)
      (Eventually.of_forall fun x => norm_nonneg _) (Eventually.of_forall fun _ => zero_le_one)
      (by rw [hp2]; exact (Lp.memLp (fourierL2 h)).norm.restrict S)
      (by rw [hp2]; exact memLp_const 1)
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at key
    simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul, measureReal_def,
      Measure.restrict_apply_univ] at key
    have hconv : (∫ x in S, ‖(fourierL2 h : R3 → ℂ) x‖ ^ (2 : ℝ) ∂volume)
        = ∫ x in S, ‖(fourierL2 h : R3 → ℂ) x‖ ^ 2 ∂volume :=
      integral_congr_ae (Eventually.of_forall fun x => Real.rpow_natCast _ 2)
    rw [hconv] at key
    exact key
  -- inner product as set integral, then bound
  rw [norm_inner_symm, shellFun,
    MeasureTheory.L2.inner_indicatorConstLp_eq_setIntegral_inner]
  calc ‖∫ x in S, ⟪((c : ℂ)), (fourierL2 h : R3 → ℂ) x⟫_ℂ ∂volume‖
      ≤ ∫ x in S, ‖⟪((c : ℂ)), (fourierL2 h : R3 → ℂ) x⟫_ℂ‖ ∂volume :=
        norm_integral_le_integral_norm _
    _ = c * ∫ x in S, ‖(fourierL2 h : R3 → ℂ) x‖ ∂volume := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        change ‖⟪(c : ℂ), (fourierL2 h : R3 → ℂ) x⟫_ℂ‖ = c * ‖(fourierL2 h : R3 → ℂ) x‖
        rw [RCLike.inner_apply', norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show (0 : ℝ) ≤ c from inv_nonneg.mpr hsqrtV.le)]
    _ ≤ c * (Real.sqrt (∫ x in S, ‖(fourierL2 h : R3 → ℂ) x‖ ^ 2 ∂volume)
          * Real.sqrt (volume S).toReal) :=
        mul_le_mul_of_nonneg_left hCS (inv_nonneg.mpr hsqrtV.le)
    _ = Real.sqrt (∫ x in S, ‖(fourierL2 h : R3 → ℂ) x‖ ^ 2 ∂volume) := by
        rw [hc, mul_comm (Real.sqrt (∫ x in S, ‖(fourierL2 h : R3 → ℂ) x‖ ^ 2 ∂volume))
            (Real.sqrt (volume S).toReal), ← mul_assoc, inv_mul_cancel₀ hsqrtV.ne', one_mul]

include hlam in
/-- The Weyl sequence is weakly null. -/
lemma weaklyNull_weylSeq (h : l2R3) :
    Tendsto (fun n => ⟪h, weylSeq lam hlam n⟫_ℂ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hreduce : ∀ n, ⟪h, weylSeq lam hlam n⟫_ℂ = ⟪fourierL2 h, shellFun lam hlam n⟫_ℂ := by
    intro n
    rw [weylSeq, ← fourierL2.inner_map_map h (fourierL2.symm (shellFun lam hlam n)),
      LinearIsometryEquiv.apply_symm_apply]
  have hg : Tendsto (fun (n : ℕ) => Real.sqrt (∫ ξ in laplacianShell lam (1 / (n + 1)),
      ‖(fourierL2 h : R3 → ℂ) ξ‖ ^ 2 ∂volume)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = Real.sqrt 0 from Real.sqrt_zero.symm]
    exact (Real.continuous_sqrt.tendsto 0).comp (tendsto_setIntegral_normSq lam hlam h)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
  rw [hreduce n]; exact norm_inner_shellFun_le lam hlam h n

include hlam in
/-- **`[0,∞) ⊆ σ_ess(−Δ)`**: each `λ ≥ 0` carries the Weyl sequence `ψₙ`. -/
theorem mem_essSpectrum_laplacian :
    lam ∈ Spectra.Essential.essSpectrum laplacian_isSelfAdjoint := by
  refine Spectra.Essential.mem_essSpectrum_of_seq laplacian_isSelfAdjoint lam
    (fun n => weylSeq lam hlam n) (fun n => memSobolevH2_weylSeq lam hlam n) ?_
    (fun g => weaklyNull_weylSeq lam hlam g) ?_
  · have h1 : (fun n => ‖weylSeq lam hlam n‖) = fun _ => (1 : ℝ) := funext (norm_weylSeq lam hlam)
    rw [h1]; exact tendsto_const_nhds
  · exact squeeze_zero (fun n => norm_nonneg _) (fun n => eigendefect_weylSeq lam hlam n)
      tendsto_one_div_add_atTop_nhds_zero_nat

end Construction

/-- **`σ_ess(−Δ) ⊆ [0,∞)`**: `−Δ ≥ 0`, so a Weyl sequence at `λ` forces `λ ≥ 0`. -/
theorem essSpectrum_laplacian_subset_Ici :
    Spectra.Essential.essSpectrum laplacian_isSelfAdjoint ⊆ Set.Ici (0 : ℝ) := by
  intro lam hmem
  obtain ⟨ψ, hψnorm, _, hψeig⟩ := hmem
  rw [Set.mem_Ici]
  -- `⟪(−Δ−λ)ψₙ, ψₙ⟫ → 0`.
  have hinner0 : Tendsto (fun n => inner (𝕜 := ℂ)
      (laplacianPMap (ψ n) - (lam : ℂ) • (ψ n : l2R3)) (ψ n : l2R3)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_inner_le_norm _ _) ?_
    simpa using hψeig.mul hψnorm
  have ha : Tendsto (fun n => -(inner (𝕜 := ℂ)
      (laplacianPMap (ψ n) - (lam : ℂ) • (ψ n : l2R3)) (ψ n : l2R3)).re) atTop (𝓝 0) := by
    have h1 := (Complex.continuous_re.tendsto (0 : ℂ)).comp hinner0
    simp only [Complex.zero_re] at h1
    simpa using h1.neg
  -- `λ‖ψₙ‖² → λ`.
  have hb : Tendsto (fun n => lam * ‖(ψ n : l2R3)‖ ^ 2) atTop (𝓝 lam) := by
    simpa using (hψnorm.pow 2).const_mul lam
  -- the per-`n` inequality `−⟪(−Δ−λ)ψₙ,ψₙ⟫.re ≤ λ‖ψₙ‖²` from positivity.
  refine le_of_tendsto_of_tendsto' ha hb (fun n => ?_)
  have hnn : 0 ≤ (inner (𝕜 := ℂ) (laplacianPMap (ψ n)) (ψ n : l2R3)).re :=
    laplacian_nonneg (ψ n : l2R3) (ψ n).2
  have hself : (inner (𝕜 := ℂ) (ψ n : l2R3) (ψ n : l2R3)).re = ‖(ψ n : l2R3)‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (ψ n : l2R3)
  have hid : (inner (𝕜 := ℂ) (laplacianPMap (ψ n) - (lam : ℂ) • (ψ n : l2R3)) (ψ n : l2R3)).re
      = (inner (𝕜 := ℂ) (laplacianPMap (ψ n)) (ψ n : l2R3)).re - lam * ‖(ψ n : l2R3)‖ ^ 2 := by
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, Complex.sub_re,
      Complex.re_ofReal_mul, hself]
  rw [hid]; linarith

/-- **The essential spectrum of the free Laplacian: `σ_ess(−Δ) = [0, ∞)`.** -/
theorem essSpectrum_laplacian :
    Spectra.Essential.essSpectrum laplacian_isSelfAdjoint = Set.Ici (0 : ℝ) :=
  Set.Subset.antisymm essSpectrum_laplacian_subset_Ici
    (fun lam hlam => mem_essSpectrum_laplacian lam (Set.mem_Ici.mp hlam))

end Spectra.QuantumMechanics.Hydrogen

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Spaces.Sobolev.DensityResults
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
/-!
# Fourier multipliers and weak-derivative-from-Fourier-decay

This file is the generic (non-Hydrogen) `L²`-Fourier / Sobolev-multiplier layer,
shared by the Hydrogen Laplacian (`Hydrogen/Laplacian/Basic.lean`) and the Dirac
operator (`DiracEquation/`).  It packages the scalar `L²` Fourier transform
`fourierL2` (Plancherel), the Laplacian and first-order derivative Fourier symbols
(`laplacianSymbol`, `derivSymbol`), the resolvent symbol `resolventSymbol` with its
bounds, and the distribution-theoretic bridge between weak derivatives and Fourier
decay (`lineDerivOp_toTD_weakGradient`, `hasWeakDerivative_of_distEq`,
`weakDeriv_construct`, ...).

None of the content here references Coulomb- or hydrogen-specific material; it was
factored out verbatim from `Hydrogen/Laplacian/Basic.lean` so that the Dirac operator
files can depend on this neutral layer without importing the Hydrogen crown-jewel file.
-/

noncomputable section

open MeasureTheory Complex Filter InnerProductSpace
open Spectra.Sobolev
open FourierTransform
open scoped Topology NNReal ENNReal SchwartzMap ContDiff

namespace Spectra.Sobolev

/-- The L² Fourier transform on `L²(ℝ³)`, as an isometric equivalence (Plancherel).

    A literal one-liner: the project's custom `MeasureSpace R3` instance was removed
    (see `Spaces/Sobolev/WeakDerivative.lean`) so that `l2R3`'s measure IS Mathlib's
    `measureSpaceOfInnerProductSpace` volume — the same measure `Lp.fourierTransformₗᵢ`
    lives over.  No measure-diamond transport needed. -/
def fourierL2 : l2R3 ≃ₗᵢ[ℂ] l2R3 :=
  Lp.fourierTransformₗᵢ R3 ℂ

/-- The multiplier that −Δ becomes under the Fourier transform: `m(ξ) = (2π)²‖ξ‖²`
    (real, `≥ 0`).  Content of `SchwartzMap.laplacian_eq_fourierMultiplierCLM`
    transported to `l2R3`. -/
def laplacianSymbol (ξ : R3) : ℝ := (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2

lemma laplacianSymbol_nonneg (ξ : R3) : 0 ≤ laplacianSymbol ξ :=
  mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `fourierL2` is definitionally the L² Fourier transform `𝓕`. -/
lemma fourierL2_eq (f : l2R3) : fourierL2 f = 𝓕 f := rfl

/-- The symbol `(2π)²‖ξ‖²` as a complex function has temperate growth. -/
lemma laplacianSymbol_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun ξ : R3 => (laplacianSymbol ξ : ℂ)) := by
  unfold laplacianSymbol; fun_prop

/-- The Fourier multiplier of the `k`-th partial derivative: `2πi⟪ξ,eₖ⟫`. -/
def derivSymbol (k : Fin 3) (ξ : R3) : ℂ :=
  2 * Real.pi * Complex.I * ((inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ) : ℂ)

lemma derivSymbol_hasTemperateGrowth (k : Fin 3) :
    Function.HasTemperateGrowth (derivSymbol k) := by unfold derivSymbol; fun_prop

lemma laplacianSymbol_add_ne_zero {ε : ℂ} (hε : ε.im ≠ 0) (ξ : R3) :
    (laplacianSymbol ξ : ℂ) + ε ≠ 0 := by
  intro h
  apply hε
  have him : ((laplacianSymbol ξ : ℂ) + ε).im = 0 := by rw [h]; rfl
  simpa using him

/-- The imaginary part alone forces `|(2π)²‖ξ‖² + ε| ≥ |ε.im|`. -/
lemma abs_im_le_norm_laplacianSymbol_add (ε : ℂ) (ξ : R3) :
    |ε.im| ≤ ‖(laplacianSymbol ξ : ℂ) + ε‖ := by
  have him : ((laplacianSymbol ξ : ℂ) + ε).im = ε.im := by simp
  rw [← him]; exact abs_im_le_norm _

/-- The resolvent multiplier `1/((2π)²‖ξ‖² + ε)` for `ε ∈ {i, −i}`. -/
def resolventSymbol (ε : ℂ) (ξ : R3) : ℂ := ((laplacianSymbol ξ : ℂ) + ε)⁻¹

lemma resolventSymbol_mul_cancel {ε : ℂ} (hε : ε.im ≠ 0) (ξ : R3) :
    ((laplacianSymbol ξ : ℂ) + ε) * resolventSymbol ε ξ = 1 :=
  mul_inv_cancel₀ (laplacianSymbol_add_ne_zero hε ξ)

/-- `|1/((2π)²‖ξ‖² + ε)| ≤ 1/|ε.im|`. -/
lemma norm_resolventSymbol_le {ε : ℂ} (hε : ε.im ≠ 0) (ξ : R3) :
    ‖resolventSymbol ε ξ‖ ≤ 1 / |ε.im| := by
  rw [resolventSymbol, norm_inv, one_div]
  exact inv_anti₀ (abs_pos.mpr hε) (abs_im_le_norm_laplacianSymbol_add ε ξ)

/-- The H²-weighted resolvent symbol `(1+‖ξ‖²)/((2π)²‖ξ‖² + ε)` is bounded — this is
    what lands the solution in H² rather than just L².  Witness
    `C = 1 + (1+|ε.re|)/|ε.im|`: split `(1+‖ξ‖²) ≤ 1 + (2π)²‖ξ‖²` (as `(2π)² ≥ 1`) and
    bound `(2π)²‖ξ‖² ≤ ‖z‖ + |ε.re|` via `|Re z| ≤ ‖z‖`, `|ε.im| ≤ ‖z‖`. -/
lemma exists_bound_weighted_resolventSymbol {ε : ℂ} (hε : ε.im ≠ 0) :
    ∃ C : ℝ, ∀ ξ : R3, ‖((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * resolventSymbol ε ξ‖ ≤ C := by
  refine ⟨1 + (1 + |ε.re|) / |ε.im|, fun ξ => ?_⟩
  set s : ℝ := laplacianSymbol ξ with hs_def
  set z : ℂ := (s : ℂ) + ε with hz_def
  have hd : 0 < |ε.im| := abs_pos.mpr hε
  have him : |ε.im| ≤ ‖z‖ := abs_im_le_norm_laplacianSymbol_add ε ξ
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hd him
  -- the LHS norm equals (1+‖ξ‖²) / ‖z‖
  have lhs_eq : ‖((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * resolventSymbol ε ξ‖
      = (1 + ‖ξ‖ ^ 2) * ‖z‖⁻¹ := by
    rw [norm_mul, resolventSymbol, ← hs_def, ← hz_def, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [lhs_eq, mul_inv_le_iff₀ hzpos]
  -- goal: 1 + ‖ξ‖² ≤ (1 + (1+|ε.re|)/|ε.im|) * ‖z‖
  -- key facts
  have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hst : ‖ξ‖ ^ 2 ≤ s := by
    rw [hs_def, laplacianSymbol]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (2 * Real.pi) ^ 2 - 1) (sq_nonneg ‖ξ‖)]
  have hzre : z.re = s + ε.re := by rw [hz_def]; simp
  have hsb : s ≤ ‖z‖ + |ε.re| := by
    have h1 : s + ε.re ≤ ‖z‖ := hzre ▸ (le_abs_self z.re).trans (abs_re_le_norm z)
    nlinarith [neg_le_abs ε.re]
  rw [show (1 + (1 + |ε.re|) / |ε.im|) = (|ε.im| + 1 + |ε.re|) / |ε.im| by field_simp; ring,
    div_mul_eq_mul_div, le_div_iff₀ hd]
  nlinarith [mul_le_mul_of_nonneg_left (hst.trans hsb) hd.le,
    mul_le_mul_of_nonneg_right him (abs_nonneg ε.re), him, hd, sq_nonneg ‖ξ‖, abs_nonneg ε.re]

/-- Measurability of `ξ ↦ resolventSymbol ε ξ`.  (`fun_prop` can't do the complex
    inverse; route through `Measurable.inv`, valid since `ℂ` has `ContinuousInv₀`.) -/
lemma aestronglyMeasurable_resolventSymbol (ε : ℂ) :
    AEStronglyMeasurable (resolventSymbol ε) volume := by
  apply Measurable.aestronglyMeasurable
  unfold resolventSymbol laplacianSymbol
  apply Measurable.inv
  fun_prop

/-- Measurability of the weighted symbol. -/
lemma aestronglyMeasurable_weighted_resolventSymbol (ε : ℂ) :
    AEStronglyMeasurable
      (fun ξ => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * resolventSymbol ε ξ) volume :=
  (by fun_prop : AEStronglyMeasurable (fun ξ : R3 => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ)) volume).mul
    (aestronglyMeasurable_resolventSymbol ε)

/-- Local integrability of `(2π)²‖ξ‖² · g` for `g ∈ L²`: continuous × L²-loc. -/
lemma locallyIntegrable_laplacianSymbol_mul (g : l2R3) :
    LocallyIntegrable (fun ξ => (laplacianSymbol ξ : ℂ) * (g : R3 → ℂ) ξ) volume := by
  have hLI : LocallyIntegrable (g : R3 → ℂ) volume :=
    (Lp.memLp g).locallyIntegrable one_le_two
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  exact IntegrableOn.continuousOn_mul
    (Continuous.continuousOn (by unfold laplacianSymbol; fun_prop))
    (hLI.integrableOn_isCompact hK) hK

/-- Pointwise multiplication by an essentially-bounded measurable symbol keeps an
    L² function in L².  `eLpNorm` domination via `MemLp.of_le_mul`. -/
lemma memLp_two_boundedMul {m : R3 → ℂ} (hm : AEStronglyMeasurable m volume)
    {C : ℝ} (hC : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ C) (g : l2R3) :
    MemLp (fun ξ => m ξ * (g : R3 → ℂ) ξ) 2 volume := by
  refine MemLp.of_le_mul (c := C) (Lp.memLp g) (hm.mul (Lp.aestronglyMeasurable g)) ?_
  filter_upwards [hC] with ξ hξ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)

/-- Two L² elements with a.e.-equal representatives are equal. -/
lemma L2_ext {a b : l2R3} (h : (a : R3 → ℂ) =ᵐ[volume] (b : R3 → ℂ)) : a = b :=
  Lp.ext h

/-- Plumbing: a distributional identity `toTD A = (m • ·)(toTD B)` with `m` of
    temperate growth recovers the a.e. pointwise product, by testing against
    `C_c^∞` (`ae_eq_of_integral_contDiff_smul_eq`). -/
lemma aeEq_of_toTD_smulLeft {A B : l2R3} {m : R3 → ℂ} (hm : Function.HasTemperateGrowth m)
    (hmloc : LocallyIntegrable (fun ξ => m ξ * (B : R3 → ℂ) ξ) volume)
    (h : Lp.toTemperedDistribution A
        = TemperedDistribution.smulLeftCLM ℂ m (Lp.toTemperedDistribution B)) :
    (A : R3 → ℂ) =ᵐ[volume] fun ξ => m ξ * (B : R3 → ℂ) ξ := by
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp A).locallyIntegrable one_le_two) hmloc (fun g hg hgsupp => ?_)
  -- view the real C_c^∞ test function `g` as a complex Schwartz map
  set gℂ : 𝓢(R3, ℂ) :=
    (hgsupp.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg) with _hgℂ
  have hgℂ_coe : ⇑gℂ = fun x => ((g x : ℝ) : ℂ) := rfl
  have hpair := DFunLike.congr_fun h gℂ
  rw [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply] at hpair
  simp only [hgℂ_coe, SchwartzMap.smulLeftCLM_apply_apply hm, smul_eq_mul,
    Complex.real_smul] at hpair ⊢
  rw [hpair]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  ring

/-- Converse of `aeEq_of_toTD_smulLeft`: an a.e. pointwise product lifts to a
    distributional `smulLeft` identity (test against all Schwartz `u`). -/
lemma toTD_smulLeft_eq {A B : l2R3} {m : R3 → ℂ} (hm : Function.HasTemperateGrowth m)
    (hAB : (A : R3 → ℂ) =ᵐ[volume] fun ξ => m ξ * (B : R3 → ℂ) ξ) :
    Lp.toTemperedDistribution A
      = TemperedDistribution.smulLeftCLM ℂ m (Lp.toTemperedDistribution B) := by
  ext u
  rw [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  simp only [SchwartzMap.smulLeftCLM_apply_apply hm]
  refine integral_congr_ae ?_
  filter_upwards [hAB] with ξ hξ
  simp only [smul_eq_mul, hξ]; ring

/-- `𝓕` is injective on `𝓢'`. -/
lemma fourierTD_injective :
    Function.Injective (𝓕 : 𝓢'(R3, ℂ) → 𝓢'(R3, ℂ)) := fun a b hab => by
  have := congrArg (fun x => (𝓕⁻ x : 𝓢'(R3, ℂ))) hab
  simpa only [fourierInv_fourier_eq] using this

/-- Converse of the first-order bridge: a distributional identity
    `∂_{eₖ}(toTD ψ) = toTD g` yields a weak derivative `HasWeakDerivative ψ k g`
    (test against `C_c^∞`). -/
lemma hasWeakDerivative_of_distEq (ψ g : l2R3) (k : Fin 3)
    (hd : LineDeriv.lineDerivOp (EuclideanSpace.single k (1 : ℝ) : R3)
        (Lp.toTemperedDistribution ψ) = Lp.toTemperedDistribution g) :
    HasWeakDerivative ψ k g := by
  intro φ hφ hsupp
  set φ𝓢 : 𝓢(R3, ℂ) := hsupp.toSchwartzMap hφ with _hφ𝓢
  have hcoe : (⇑φ𝓢 : R3 → ℂ) = φ := rfl
  have hpair := DFunLike.congr_fun hd φ𝓢
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at hpair
  simp only [SchwartzMap.neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoe,
    smul_eq_mul, neg_mul] at hpair
  rw [integral_neg] at hpair
  -- hpair : -∫ fderiv·ψ = ∫ φ·g ;  goal : ∫ ψ·fderiv = -∫ g·φ
  have h1 : ∫ x, ψ x * fderiv ℝ φ x (EuclideanSpace.single k 1)
      = ∫ x, fderiv ℝ φ x (EuclideanSpace.single k 1) * ψ x := by simp_rw [mul_comm]
  have h2 : ∫ x, g x * φ x = ∫ x, φ x * g x := by simp_rw [mul_comm]
  rw [h1, h2]
  linear_combination -hpair

/-- The first-order bridge for a **smooth compactly-supported** function: here it is
    classical, via `lineDerivOp_toTemperedDistributionCLM_eq` on the Schwartz map. -/
lemma lineDerivOp_toTD_of_smooth (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hsupp : HasCompactSupport φ) (i : Fin 3) :
    LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : R3)
        (Lp.toTemperedDistribution ((memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ))
      = Lp.toTemperedDistribution ((memLp_partialDeriv φ i hφ hsupp).toLp
          (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1))) := by
  set m : R3 := EuclideanSpace.single i (1 : ℝ) with _hm
  set φ𝓢 : 𝓢(R3, ℂ) := hsupp.toSchwartzMap hφ with _hφ𝓢
  have hcoe : (⇑φ𝓢 : R3 → ℂ) = φ := rfl
  -- both L² approximants agree a.e. with the corresponding Schwartz maps
  have hLp1 : (memLp_of_smooth_compactSupport φ hφ hsupp).toLp φ = φ𝓢.toLp 2 volume := by
    apply Lp.ext
    filter_upwards [(memLp_of_smooth_compactSupport φ hφ hsupp).coeFn_toLp,
      φ𝓢.coeFn_toLp 2 volume] with x h1 h2
    rw [h1, h2, hcoe]
  have hLp2 : (memLp_partialDeriv φ i hφ hsupp).toLp (fun x => fderiv ℝ φ x m)
      = (LineDeriv.lineDerivOp m φ𝓢).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [(memLp_partialDeriv φ i hφ hsupp).coeFn_toLp,
      (LineDeriv.lineDerivOp m φ𝓢).coeFn_toLp 2 volume] with x h1 h2
    rw [h1, h2, SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoe]
  rw [hLp1, hLp2, Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq φ𝓢 m

/-- **First-order bridge (the new analytic content).**  The distributional `i`-th
    partial derivative of an `H¹` function's tempered distribution equals the
    tempered distribution of its weak derivative.

    Proof (Route B′): approximate `f` by `C_c^∞` in the H¹ norm
    (`smooth_compactly_supported_dense_H1` — first derivatives converge in L²);
    for each smooth approximant the identity is classical (`lineDerivOp_toTD_of_smooth`);
    pass to the limit using that `toTemperedDistributionCLM` and `∂ᵢ` are continuous
    on `𝓢'` (T₂). -/
lemma lineDerivOp_toTD_weakGradient (f : l2R3) (hf : MemSobolevH1 f) (i : Fin 3) :
    LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ) : R3) (Lp.toTemperedDistribution f)
      = Lp.toTemperedDistribution (weakGradient f hf i) := by
  set m : R3 := EuclideanSpace.single i (1 : ℝ) with _hm
  -- H¹ approximating sequence of `C_c^∞` functions (ε = 1/(n+1))
  choose φ hφ hsupp hand using fun n : ℕ =>
    meyers_serrin_approx_multi f (weakGradient f hf) (weakGradient_spec f hf)
      (1 / (n + 1 : ℝ)) (by positivity)
  set g : ℕ → l2R3 :=
    fun n => (memLp_of_smooth_compactSupport (φ n) (hφ n) (hsupp n)).toLp (φ n) with _hg
  set dgn : ℕ → l2R3 := fun n => (memLp_partialDeriv (φ n) i (hφ n) (hsupp n)).toLp
    (fun x => fderiv ℝ (φ n) x (EuclideanSpace.single i 1)) with _hdgn
  -- `Lp.toTemperedDistribution` is continuous (it is a CLM)
  have htoTD : (Lp.toTemperedDistribution : l2R3 → 𝓢'(R3, ℂ))
      = ⇑(Lp.toTemperedDistributionCLM ℂ (volume : Measure R3) 2) :=
    funext fun x => (Lp.toTemperedDistributionCLM_apply x).symm
  have hcont_toTD : Continuous (Lp.toTemperedDistribution : l2R3 → 𝓢'(R3, ℂ)) := by
    rw [htoTD]; exact (Lp.toTemperedDistributionCLM ℂ (volume : Measure R3) 2).continuous
  -- L² convergence from the 1/(n+1) bounds
  have hg_tend : Tendsto g atTop (𝓝 f) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev]; exact (hand n).1.le
  have hdg_tend : Tendsto dgn atTop (𝓝 (weakGradient f hf i)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev]; exact ((hand n).2 i).le
  -- the sequence `n ↦ ∂_m (toTD (gₙ))` has two limits; conclude by T₂ uniqueness
  refine tendsto_nhds_unique (l := Filter.atTop)
    (f := fun n => LineDeriv.lineDerivOp m (Lp.toTemperedDistribution (g n))) ?_ ?_
  · exact ((ContinuousLineDeriv.continuous_lineDerivOp m).tendsto _).comp
      ((hcont_toTD.tendsto f).comp hg_tend)
  · have heq : (fun n => LineDeriv.lineDerivOp m (Lp.toTemperedDistribution (g n)))
        = fun n => Lp.toTemperedDistribution (dgn n) :=
      funext fun n => lineDerivOp_toTD_of_smooth (φ n) (hφ n) (hsupp n) i
    rw [heq]
    exact (hcont_toTD.tendsto (weakGradient f hf i)).comp hdg_tend

/-- The weak gradient of an `H²` function is itself `H¹`: its weak `j`-derivative
    is the `(i,j)` second derivative of the original, which exists by `hψ.2 i j`. -/
lemma memSobolevH1_weakGradient (ψ : l2R3) (hψ : MemSobolevH2 ψ) (i : Fin 3) :
    MemSobolevH1 (weakGradient ψ (sobolevH2_le_sobolevH1 hψ) i) := by
  intro j
  obtain ⟨g, mid, hmid_i, hmid_j⟩ := hψ.2 i j
  refine ⟨g, ?_⟩
  have hmid : mid = weakGradient ψ (sobolevH2_le_sobolevH1 hψ) i :=
    hasWeakDerivative_unique ψ i mid _ hmid_i (weakGradient_spec ψ (sobolevH2_le_sobolevH1 hψ) i)
  rwa [hmid] at hmid_j

/-- `−Δψ` as the iterated weak gradient: `weakLaplacian ψ = −Σᵢ ∂ᵢ(∂ᵢψ)`. -/
lemma weakLaplacian_eq_neg_sum (ψ : l2R3) (hψ : MemSobolevH2 ψ) :
    weakLaplacian ψ hψ
      = -∑ i, weakGradient (weakGradient ψ (sobolevH2_le_sobolevH1 hψ) i)
          (memSobolevH1_weakGradient ψ hψ i) i := by
  unfold weakLaplacian
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨mid, hmid_i, hmid_ii⟩ := (hψ.2 i i).choose_spec
  have hmid : mid = weakGradient ψ (sobolevH2_le_sobolevH1 hψ) i :=
    hasWeakDerivative_unique ψ i mid _ hmid_i (weakGradient_spec ψ (sobolevH2_le_sobolevH1 hψ) i)
  rw [hmid] at hmid_ii
  exact hasWeakDerivative_unique _ i _ _ hmid_ii
    (weakGradient_spec _ (memSobolevH1_weakGradient ψ hψ i) i)

/-- **Construct the `k`-th weak derivative from Fourier decay.**  If
    `derivSymbol k · 𝓕ψ ∈ L²`, its inverse Fourier transform `g` is the weak
    `k`-derivative of `ψ`, with `𝓕g = derivSymbol k · 𝓕ψ`. -/
lemma weakDeriv_construct (ψ : l2R3) (k : Fin 3)
    (hmem : MemLp (fun ξ => derivSymbol k ξ * (fourierL2 ψ : R3 → ℂ) ξ) 2 volume) :
    ∃ g : l2R3, HasWeakDerivative ψ k g ∧
      (fourierL2 g : R3 → ℂ) =ᵐ[volume] fun ξ => derivSymbol k ξ * (fourierL2 ψ : R3 → ℂ) ξ := by
  refine ⟨fourierL2.symm (hmem.toLp _), ?_, ?_⟩
  swap
  · rw [LinearIsometryEquiv.apply_symm_apply]; exact hmem.coeFn_toLp
  -- the Fourier characterisation of the candidate `g`
  have hfg : (fourierL2 (fourierL2.symm (hmem.toLp _)) : R3 → ℂ)
      =ᵐ[volume] fun ξ => derivSymbol k ξ * (fourierL2 ψ : R3 → ℂ) ξ := by
    rw [LinearIsometryEquiv.apply_symm_apply]; exact hmem.coeFn_toLp
  set g : l2R3 := fourierL2.symm (hmem.toLp _) with _hgdef
  -- distribution identity  ∂_{eₖ}(toTD ψ) = toTD g, then test against C_c^∞
  apply hasWeakDerivative_of_distEq
  apply fourierTD_injective
  have hg₀ : Function.HasTemperateGrowth
      (fun ξ : R3 => ((inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ) : ℂ)) := by fun_prop
  rw [TemperedDistribution.fourier_lineDerivOp_eq, Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq]
  simp only [← fourierL2_eq]
  rw [toTD_smulLeft_eq (derivSymbol_hasTemperateGrowth k) hfg,
    ← ContinuousLinearMap.smul_apply, ← TemperedDistribution.smulLeftCLM_smul hg₀]
  congr 2

/-- **`H² ⇐ Fourier decay`.**  If `(1+‖ξ‖²)·𝓕ψ ∈ L²` then `ψ ∈ H²`.  (The ⇒
    direction is not needed for surjectivity.)  Proved via the *converse* of the
    first-order bridge: the Fourier multiplier `2πi⟪ξ,eₖ⟫` builds the weak derivatives. -/
theorem memSobolevH2_of_fourier_decay (ψ : l2R3)
    (h : MemLp (fun ξ => ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * (fourierL2 ψ : R3 → ℂ) ξ) 2 volume) :
    MemSobolevH2 ψ := by
  -- `‖derivSymbol k ξ‖ ≤ 2π‖ξ‖`, and the weaker `≤ 2π(1+‖ξ‖²)`
  have hbd2 : ∀ (k : Fin 3) (ξ : R3), ‖derivSymbol k ξ‖ ≤ 2 * Real.pi * ‖ξ‖ := by
    intro k ξ
    have hi : |(inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ)| ≤ ‖ξ‖ := by
      simpa using abs_real_inner_le_norm ξ (EuclideanSpace.single k (1 : ℝ))
    have hnorm : ‖derivSymbol k ξ‖
        = 2 * Real.pi * |(inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ)| := by
      simp only [derivSymbol, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, mul_one, abs_of_pos Real.pi_pos]
    rw [hnorm]
    nlinarith [Real.pi_pos, abs_nonneg (inner ℝ ξ (EuclideanSpace.single k (1 : ℝ)) : ℝ), hi]
  have hbd : ∀ (k : Fin 3) (ξ : R3), ‖derivSymbol k ξ‖ ≤ 2 * Real.pi * (1 + ‖ξ‖ ^ 2) := by
    intro k ξ
    calc ‖derivSymbol k ξ‖ ≤ 2 * Real.pi * ‖ξ‖ := hbd2 k ξ
      _ ≤ 2 * Real.pi * (1 + ‖ξ‖ ^ 2) := by nlinarith [Real.pi_pos, sq_nonneg (‖ξ‖ - 1)]
  -- `‖((1+‖ξ‖²:ℝ):ℂ)·𝓕ψ ξ‖ = (1+‖ξ‖²)·‖𝓕ψ ξ‖`
  have hwt : ∀ ξ : R3, ‖((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) * (fourierL2 ψ : R3 → ℂ) ξ‖
      = (1 + ‖ξ‖ ^ 2) * ‖(fourierL2 ψ : R3 → ℂ) ξ‖ := by
    intro ξ; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- generic L²-membership of a Fourier multiplier dominated by `C(1+‖ξ‖²)·𝓕ψ`
  have hmemMul : ∀ (k : Fin 3) (B : l2R3),
      (B : R3 → ℂ) =ᵐ[volume] (fourierL2 ψ : R3 → ℂ) →
      MemLp (fun ξ => derivSymbol k ξ * (B : R3 → ℂ) ξ) 2 volume := by
    intro k B hB
    refine MemLp.of_le_mul (c := 2 * Real.pi) h
      ((by unfold derivSymbol; fun_prop : AEStronglyMeasurable (derivSymbol k) volume).mul
        (Lp.aestronglyMeasurable B)) ?_
    filter_upwards [hB] with ξ hξ
    rw [norm_mul, hξ, hwt, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbd k ξ) (norm_nonneg ((fourierL2 ψ : R3 → ℂ) ξ))
  -- first weak derivatives
  have hmem1 : ∀ k, MemLp (fun ξ => derivSymbol k ξ * (fourierL2 ψ : R3 → ℂ) ξ) 2 volume :=
    fun k => hmemMul k (fourierL2 ψ) (Filter.EventuallyEq.refl _ _)
  choose g hg_wd hg_four using fun k => weakDeriv_construct ψ k (hmem1 k)
  refine ⟨fun k => ⟨g k, hg_wd k⟩, fun i j => ?_⟩
  -- second derivative: differentiate `g i` once more in direction `j`
  have hmem2 : MemLp (fun ξ => derivSymbol j ξ * (fourierL2 (g i) : R3 → ℂ) ξ) 2 volume := by
    refine MemLp.of_le_mul (c := (2 * Real.pi) ^ 2) h
      ((by unfold derivSymbol; fun_prop : AEStronglyMeasurable (derivSymbol j) volume).mul
        (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [hg_four i] with ξ hξ
    rw [norm_mul, hξ, norm_mul, hwt]
    have hprod : ‖derivSymbol j ξ‖ * ‖derivSymbol i ξ‖ ≤ (2 * Real.pi) ^ 2 * (1 + ‖ξ‖ ^ 2) := by
      calc ‖derivSymbol j ξ‖ * ‖derivSymbol i ξ‖
          ≤ (2 * Real.pi * ‖ξ‖) * (2 * Real.pi * ‖ξ‖) :=
            mul_le_mul (hbd2 j ξ) (hbd2 i ξ) (norm_nonneg _) (by positivity)
        _ = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by ring
        _ ≤ (2 * Real.pi) ^ 2 * (1 + ‖ξ‖ ^ 2) := by nlinarith [Real.pi_pos, sq_nonneg ‖ξ‖]
    calc ‖derivSymbol j ξ‖ * (‖derivSymbol i ξ‖ * ‖(fourierL2 ψ : R3 → ℂ) ξ‖)
        = (‖derivSymbol j ξ‖ * ‖derivSymbol i ξ‖) * ‖(fourierL2 ψ : R3 → ℂ) ξ‖ := by ring
      _ ≤ ((2 * Real.pi) ^ 2 * (1 + ‖ξ‖ ^ 2)) * ‖(fourierL2 ψ : R3 → ℂ) ξ‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = (2 * Real.pi) ^ 2 * ((1 + ‖ξ‖ ^ 2) * ‖(fourierL2 ψ : R3 → ℂ) ξ‖) := by ring
  obtain ⟨gij, hgij_wd, _⟩ := weakDeriv_construct (g i) j hmem2
  exact ⟨gij, g i, hg_wd i, hgij_wd⟩

end Spectra.Sobolev

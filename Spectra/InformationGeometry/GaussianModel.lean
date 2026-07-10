/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.InformationGeometry.Fisher.Information
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
/-!
# The Gaussian shift model — a statistical model with prescribed Fisher matrix

This file builds the **first concrete `StatisticalModel`** in Spectra: a multivariate
Gaussian *location* family whose Fisher information matrix is a prescribed Gram matrix
`Rᵀ R`.  Given any real matrix `R : Matrix (Fin m) (Fin n) ℝ` (`m` sample coordinates,
`n` parameters) it produces a `RegularStatisticalModel n (Fin m → ℝ)` with

  `density R θ x = ∏ k, gaussianPDFReal (R.mulVec θ k) 1 (x k)`,

i.e. `m` independent unit-variance Gaussians whose mean vector is the **linear** image
`R θ` of the parameter.  Its score is the affine field `sᵢ(θ, x) = (Rᵀ (x − R θ))ᵢ`, so
the Fisher matrix is the **constant** Gram matrix `g_{ij} = (Rᵀ R)_{ij}`
(`gaussianShiftModel_fisherMatrix`).

The point of this construction is the quantum-information-geometry **weld**: since every
symmetric PSD matrix `G` factors as `G = Rᵀ R` (`Matrix.posSemidef_iff_eq_sum_vecMulVec`),
choosing the quantum metric `G = 4·Cov` realises the quantum Fisher metric as the Fisher
metric of an honest classical model — which is what turns
`QuantumMechanics.FisherModel.quantumRLDFisherModel` into a genuine functor (no assumed
`fisherMatrix = 4·Cov` hypothesis).  See `QuantumMechanics/FisherModel.lean`.

The construction needs no positive-definiteness: every coordinate has variance `1`, and
the mean map `R` may be arbitrary (in particular rectangular or singular), so the model
exists for any PSD target `G = Rᵀ R`.

## Main definitions

* `gaussianShiftModel R` — the `RegularStatisticalModel n (Fin m → ℝ)`.

## Main results

* `gaussianShiftModel_fisherMatrix` — `fisherMatrix θ i j = (Rᵀ R)_{ij}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Finset Matrix
open scoped Topology ENNReal NNReal

namespace Spectra.InformationGeometry

variable {m n : ℕ}

/-! ### The density -/

/-- The Gaussian shift density `p(θ, x) = ∏ k, N(x k ; (R θ)ₖ, 1)`. -/
def gaussianShiftDensity (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) (x : Fin m → ℝ) : ℝ :=
  ∏ k, gaussianPDFReal (R.mulVec θ k) 1 (x k)

lemma gaussianShiftDensity_nonneg (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) (x : Fin m → ℝ) : 0 ≤ gaussianShiftDensity R θ x :=
  Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

lemma gaussianShiftDensity_pos (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) (x : Fin m → ℝ) : 0 < gaussianShiftDensity R θ x :=
  Finset.prod_pos fun k _ => gaussianPDFReal_pos _ _ _ (by norm_num)

lemma measurable_gaussianShiftDensity (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) : Measurable (gaussianShiftDensity R θ) := by
  unfold gaussianShiftDensity
  refine Finset.measurable_prod _ ?_
  intro k _
  exact (measurable_gaussianPDFReal _ _).comp (measurable_pi_apply k)

lemma integral_gaussianShiftDensity (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) :
    ∫ x, gaussianShiftDensity R θ x = 1 := by
  unfold gaussianShiftDensity
  rw [integral_fintype_prod_volume_eq_prod (fun k (xk : ℝ) => gaussianPDFReal (R.mulVec θ k) 1 xk)]
  simp [integral_gaussianPDFReal_eq_one]

/-! ### The mean-coordinate functional as a continuous linear map -/

/-- The `k`-th coordinate of the mean vector `R θ`, as a continuous linear functional of
`θ ∈ ParamSpace n`.  Concretely `meanCLM R k θ = (R θ)ₖ = ∑ l, R k l * θ l`. -/
def meanCLM (R : Matrix (Fin m) (Fin n) ℝ) (k : Fin m) : ParamSpace n →L[ℝ] ℝ :=
  ∑ l : Fin n, (R k l) • EuclideanSpace.proj l

@[simp]
lemma meanCLM_apply (R : Matrix (Fin m) (Fin n) ℝ) (k : Fin m) (θ : ParamSpace n) :
    meanCLM R k θ = (R.mulVec θ) k := by
  simp only [meanCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    EuclideanSpace.coe_proj, smul_eq_mul]
  rw [Matrix.mulVec_eq_sum]
  simp [Finset.sum_apply, mul_comm]

/-- `θ ↦ (R θ)ₖ` agrees with the CLM `meanCLM R k`. -/
lemma meanCoord_eq_clm (R : Matrix (Fin m) (Fin n) ℝ) (k : Fin m) :
    (fun θ : ParamSpace n => (R.mulVec θ) k) = meanCLM R k := by
  ext θ; rw [meanCLM_apply]

/-! ### The single Gaussian factor and its derivative -/

/-- The `k`-th Gaussian factor of the density, as a function of `θ`:
`θ ↦ gaussianPDFReal ((R θ)ₖ) 1 (x k)`. -/
def gaussianFactor (R : Matrix (Fin m) (Fin n) ℝ) (k : Fin m) (x : Fin m → ℝ)
    (θ : ParamSpace n) : ℝ :=
  gaussianPDFReal (R.mulVec θ k) 1 (x k)

lemma gaussianFactor_eq (R : Matrix (Fin m) (Fin n) ℝ) (k : Fin m) (x : Fin m → ℝ)
    (θ : ParamSpace n) :
    gaussianFactor R k x θ =
      (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x k - R.mulVec θ k) ^ 2 / 2) := by
  simp only [gaussianFactor, gaussianPDFReal_def]
  norm_num

/-- The Fréchet derivative of the `k`-th Gaussian factor:
`D_θ (gaussianFactor R k x) = gaussianFactor R k x θ • (x k - (R θ)ₖ) • (meanCLM R k)`. -/
lemma hasFDerivAt_gaussianFactor (R : Matrix (Fin m) (Fin n) ℝ) (k : Fin m) (x : Fin m → ℝ)
    (θ : ParamSpace n) :
    HasFDerivAt (gaussianFactor R k x)
      (gaussianFactor R k x θ • ((x k - R.mulVec θ k) • (meanCLM R k))) θ := by
  -- gaussianFactor = c₀ * exp(u(θ)), u(θ) = -(x k - L θ)²/2, L = meanCLM R k
  have hL : HasFDerivAt (fun θ' : ParamSpace n => (R.mulVec θ' k))
      (meanCLM R k) θ := by
    rw [meanCoord_eq_clm]
    exact (meanCLM R k).hasFDerivAt
  -- u(θ) = -(x k - L θ)²/2
  set L := meanCLM R k with _hLdef
  -- derivative of θ ↦ x k - L θ is -L
  have hsub : HasFDerivAt (fun θ' : ParamSpace n => x k - R.mulVec θ' k) (-L) θ := by
    have h0 := (hasFDerivAt_const (x k) θ).sub hL
    rw [zero_sub] at h0
    exact h0
  -- derivative of θ ↦ (x k - L θ)^2 is 2(x k - Lθ) • (-L)
  have hsq : HasFDerivAt (fun θ' : ParamSpace n => (x k - R.mulVec θ' k) ^ 2)
      ((2 * (x k - R.mulVec θ k)) • (-L)) θ := by
    have := hsub.pow 2
    simpa [pow_one, two_mul, mul_comm] using this
  -- derivative of θ ↦ -(x k - Lθ)^2/2 is (x k - Lθ) • L
  have hu : HasFDerivAt (fun θ' : ParamSpace n => -(x k - R.mulVec θ' k) ^ 2 / 2)
      (((x k - R.mulVec θ k)) • L) θ := by
    -- -(...)²/2 = (-2⁻¹) • (...)²
    have h1 := hsq.const_smul (-(2 : ℝ)⁻¹)
    have hfun2 : ((-(2 : ℝ)⁻¹) • fun θ' : ParamSpace n => (x k - R.mulVec θ' k) ^ 2) =
        (fun θ' : ParamSpace n => -(x k - R.mulVec θ' k) ^ 2 / 2) := by
      ext θ'; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hfun2] at h1
    convert h1 using 1
    rw [smul_smul, smul_neg, ← neg_smul]
    congr 1
    ring
  -- exp
  have hexp := hu.exp
  -- multiply by constant c₀
  have hconst : HasFDerivAt
      (fun θ' : ParamSpace n => (Real.sqrt (2 * π))⁻¹ *
        Real.exp (-(x k - R.mulVec θ' k) ^ 2 / 2))
      ((Real.sqrt (2 * π))⁻¹ • (Real.exp (-(x k - R.mulVec θ k) ^ 2 / 2) •
        ((x k - R.mulVec θ k) • L))) θ :=
    hexp.const_smul (Real.sqrt (2 * π))⁻¹
  -- rewrite the function and derivative
  have hfun : gaussianFactor R k x =
      (fun θ' : ParamSpace n => (Real.sqrt (2 * π))⁻¹ *
        Real.exp (-(x k - R.mulVec θ' k) ^ 2 / 2)) := by
    ext θ'; rw [gaussianFactor_eq]
  rw [hfun]
  convert hconst using 1
  simp only [smul_smul, mul_assoc]

/-! ### The score covector and the density derivative -/

/-- The score covector at `(θ, x)`: the continuous linear functional
`v ↦ ∑ k, (x k - (R θ)ₖ) · (R v)ₖ`.  Evaluated at `eᵢ` it gives the score
`∑ k, (x k - (R θ)ₖ) · R k i = (Rᵀ (x - R θ))ᵢ`. -/
def scoreCLM (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) (x : Fin m → ℝ) :
    ParamSpace n →L[ℝ] ℝ :=
  ∑ k : Fin m, (x k - R.mulVec θ k) • (meanCLM R k)

/-- The scalar score in direction `i`: `∑ k, (x k - (R θ)ₖ) · R k i`. -/
def scoreFun (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) (i : Fin n)
    (x : Fin m → ℝ) : ℝ :=
  ∑ k : Fin m, (x k - R.mulVec θ k) * R k i

@[simp]
lemma scoreCLM_single (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) (x : Fin m → ℝ)
    (i : Fin n) :
    scoreCLM R θ x (EuclideanSpace.single i 1) = scoreFun R θ i x := by
  simp only [scoreCLM, scoreFun, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [meanCLM_apply]
  -- (R.mulVec (EuclideanSpace.single i 1)) k = R k i
  congr 1
  have : ((EuclideanSpace.single i (1 : ℝ)) : ParamSpace n).ofLp = Pi.single i (1 : ℝ) := by
    ext l; simp [EuclideanSpace.single, PiLp.single_apply, Pi.single_apply]
  change (R.mulVec ((EuclideanSpace.single i (1 : ℝ)) : ParamSpace n).ofLp) k = R k i
  rw [this, Matrix.mulVec_single_one]
  rfl

/-- **The key density-derivative lemma (product rule).**  The density
`θ ↦ ∏ k, gaussianPDFReal ((R θ)ₖ) 1 (x k)` is Fréchet differentiable in `θ`,
with derivative the scalar `density · scoreCLM`. -/
lemma hasFDerivAt_gaussianShiftDensity (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) (x : Fin m → ℝ) :
    HasFDerivAt (fun θ' => gaussianShiftDensity R θ' x)
      (gaussianShiftDensity R θ x • scoreCLM R θ x) θ := by
  classical
  -- density = ∏ k, gaussianFactor R k x
  have hdens : (fun θ' => gaussianShiftDensity R θ' x) =
      (∏ k : Fin m, gaussianFactor R k x ·) := by
    ext θ'; simp only [gaussianShiftDensity, gaussianFactor]
  rw [hdens]
  -- product rule
  have hprod := HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Fin m)))
    (g := fun k => gaussianFactor R k x)
    (g' := fun k => gaussianFactor R k x θ • ((x k - R.mulVec θ k) • (meanCLM R k)))
    (fun k _ => hasFDerivAt_gaussianFactor R k x θ)
  convert hprod using 1
  -- show density • scoreCLM = ∑ k, (∏ j≠k, factor_j) • (factor_k • (...))
  rw [scoreCLM, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- LHS: density • ((x k - ..) • L);  RHS: (∏ erase factor) • (factor_k • ((x k - ..) • L))
  have hscalar : gaussianShiftDensity R θ x =
      (∏ j ∈ Finset.univ.erase k, gaussianFactor R j x θ) * gaussianFactor R k x θ := by
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    simp only [gaussianShiftDensity, gaussianFactor]
  rw [hscalar]
  simp only [smul_smul, mul_assoc]

/-- The Fréchet derivative of the density equals `density • scoreCLM`. -/
lemma fderiv_gaussianShiftDensity (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) (x : Fin m → ℝ) :
    fderiv ℝ (fun θ' => gaussianShiftDensity R θ' x) θ =
      gaussianShiftDensity R θ x • scoreCLM R θ x :=
  (hasFDerivAt_gaussianShiftDensity R θ x).fderiv

/-- The `i`-th partial derivative of the density:
`∂ᵢ p(θ, x) = p(θ, x) · scoreFun R θ i x`. -/
lemma partialDensity_gaussianShift (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) (i : Fin n) (x : Fin m → ℝ) :
    fderiv ℝ (fun θ' => gaussianShiftDensity R θ' x) θ (EuclideanSpace.single i 1) =
      gaussianShiftDensity R θ x * scoreFun R θ i x := by
  rw [fderiv_gaussianShiftDensity]
  simp [ContinuousLinearMap.smul_apply, scoreCLM_single, smul_eq_mul]

/-- The score component equals `scoreFun`. -/
lemma score_gaussianShift (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) (i : Fin n) (x : Fin m → ℝ) :
    (fderiv ℝ (fun θ' => gaussianShiftDensity R θ' x) θ (EuclideanSpace.single i 1)) /
        gaussianShiftDensity R θ x = scoreFun R θ i x := by
  rw [partialDensity_gaussianShift]
  rw [mul_comm, mul_div_assoc, div_self (ne_of_gt (gaussianShiftDensity_pos R θ x)), mul_one]

/-! ### Smoothness of the density -/

/-- Each Gaussian factor is `C^∞` in `θ`.  (It is in fact real-analytic, but the
statement is kept at `C^∞` (`(⊤ : ℕ∞)`) to match `StatisticalModel.density_smooth`.) -/
lemma contDiff_gaussianFactor (R : Matrix (Fin m) (Fin n) ℝ) (k : Fin m) (x : Fin m → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianFactor R k x) := by
  have hfun : gaussianFactor R k x =
      (fun θ' : ParamSpace n => (Real.sqrt (2 * π))⁻¹ *
        Real.exp (-(x k - meanCLM R k θ') ^ 2 / 2)) := by
    ext θ'; rw [gaussianFactor_eq, meanCLM_apply]
  rw [hfun]
  have hmean : ContDiff ℝ (⊤ : ℕ∞) (fun θ' : ParamSpace n => meanCLM R k θ') :=
    (meanCLM R k).contDiff
  apply contDiff_const.mul
  apply ContDiff.exp
  apply ContDiff.div_const
  apply ContDiff.neg
  apply ContDiff.pow
  exact contDiff_const.sub hmean

/-- The density is `C^∞` in `θ` for each `x`. -/
lemma contDiff_gaussianShiftDensity (R : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun θ => gaussianShiftDensity R θ x) := by
  have hfun : (fun θ => gaussianShiftDensity R θ x) =
      (fun θ => ∏ k : Fin m, gaussianFactor R k x θ) := by
    ext θ; simp only [gaussianShiftDensity, gaussianFactor]
  rw [hfun]
  exact contDiff_prod (fun k _ => contDiff_gaussianFactor R k x)

/-! ### One-dimensional Gaussian moment facts -/

/-- The Gaussian variance parameter `1 : ℝ≥0` is nonzero. -/
private lemma one_nnreal_ne_zero : (1 : ℝ≥0) ≠ 0 := one_ne_zero

/-- **First central moment** of the unit-variance Gaussian:
`∫ x, (x - μ) · gaussianPDFReal μ 1 x = 0`. -/
lemma gaussian_first_central_moment (μ : ℝ) :
    ∫ x, (x - μ) * gaussianPDFReal μ 1 x = 0 := by
  have hbridge : ∫ x, (x - μ) * gaussianPDFReal μ 1 x =
      ∫ x, (x - μ) ∂(gaussianReal μ 1) := by
    rw [integral_gaussianReal_eq_integral_smul one_nnreal_ne_zero]
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [smul_eq_mul]; ring
  rw [hbridge]
  have hg : Integrable (fun x : ℝ => x) (gaussianReal μ 1) :=
    (memLp_id_gaussianReal (μ := μ) (v := 1) 1).integrable (by norm_num)
  rw [integral_sub hg (integrable_const μ)]
  rw [integral_id_gaussianReal]
  simp

/-- **Second central moment** of the unit-variance Gaussian:
`∫ x, (x - μ)² · gaussianPDFReal μ 1 x = 1`. -/
lemma gaussian_second_central_moment (μ : ℝ) :
    ∫ x, (x - μ) ^ 2 * gaussianPDFReal μ 1 x = 1 := by
  have hbridge : ∫ x, (x - μ) ^ 2 * gaussianPDFReal μ 1 x =
      ∫ x, (x - μ) ^ 2 ∂(gaussianReal μ 1) := by
    rw [integral_gaussianReal_eq_integral_smul one_nnreal_ne_zero]
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [smul_eq_mul]; ring
  rw [hbridge]
  -- This is the variance of id under gaussianReal μ 1, which equals 1.
  have hvar : Var[id; gaussianReal μ 1] = ((1 : ℝ≥0) : ℝ) := by
    rw [variance_id_gaussianReal]
  rw [variance_eq_integral (by fun_prop)] at hvar
  simp only [id_eq, integral_id_gaussianReal] at hvar
  rw [hvar]
  norm_num

/-! ### Measurability of the density derivative -/

/-- `x ↦ scoreCLM R θ x` is continuous. -/
lemma continuous_scoreCLM (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) :
    Continuous (fun x : Fin m → ℝ => scoreCLM R θ x) := by
  unfold scoreCLM
  refine continuous_finsetSum _ (fun k _ => ?_)
  refine Continuous.smul ?_ continuous_const
  exact (continuous_apply k).sub continuous_const

/-- `x ↦ gaussianShiftDensity R θ x` is continuous. -/
lemma continuous_gaussianShiftDensity (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) :
    Continuous (fun x : Fin m → ℝ => gaussianShiftDensity R θ x) := by
  unfold gaussianShiftDensity
  refine continuous_finsetProd _ (fun k _ => ?_)
  -- gaussianPDFReal μ v is continuous, composed with the projection x ↦ x k
  have hpdf : Continuous (gaussianPDFReal (R.mulVec θ k) 1) := by
    unfold gaussianPDFReal
    refine continuous_const.mul (Continuous.rexp ?_)
    exact ((continuous_id.sub continuous_const).pow 2).neg.div_const _
  exact hpdf.comp (continuous_apply k)

/-- The Fréchet derivative of the density is `AEStronglyMeasurable` in `x`. -/
lemma aestronglyMeasurable_fderiv_gaussianShiftDensity (R : Matrix (Fin m) (Fin n) ℝ)
    (θ : ParamSpace n) :
    AEStronglyMeasurable
      (fun x => fderiv ℝ (fun θ' => gaussianShiftDensity R θ' x) θ)
      (volume : Measure (Fin m → ℝ)) := by
  have hfun : (fun x => fderiv ℝ (fun θ' => gaussianShiftDensity R θ' x) θ) =
      (fun x => gaussianShiftDensity R θ x • scoreCLM R θ x) := by
    ext x; rw [fderiv_gaussianShiftDensity]
  rw [hfun]
  refine Continuous.aestronglyMeasurable ?_
  exact (continuous_gaussianShiftDensity R θ).smul (continuous_scoreCLM R θ)

/-! ### Per-coordinate integrability facts -/

/-- Bridge: `g` is integrable wrt `gaussianReal μ 1` iff `gaussianPDFReal μ 1 · * g` is
integrable wrt `volume`. -/
lemma integrable_gaussianReal_iff (μ : ℝ) (g : ℝ → ℝ) :
    Integrable (fun t => gaussianPDFReal μ 1 t * g t) volume ↔
      Integrable g (gaussianReal μ 1) := by
  rw [gaussianReal_of_var_ne_zero μ one_nnreal_ne_zero, gaussianPDF_def]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDFReal _ _).ennreal_ofReal
    (ae_of_all _ fun t => by exact_mod_cast ENNReal.ofReal_lt_top)]
  constructor
  · intro h
    refine h.congr ?_
    filter_upwards with t
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]
  · intro h
    refine h.congr ?_
    filter_upwards with t
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul]

/-- `t ↦ (t - μ) · gaussianPDFReal μ 1 t` is integrable. -/
lemma integrable_centered_gaussianPDFReal (μ : ℝ) :
    Integrable (fun t => (t - μ) * gaussianPDFReal μ 1 t) volume := by
  have hcomm : (fun t => (t - μ) * gaussianPDFReal μ 1 t) =
      (fun t => gaussianPDFReal μ 1 t * (t - μ)) := by ext t; rw [mul_comm]
  rw [hcomm, integrable_gaussianReal_iff]
  exact (memLp_id_gaussianReal (μ := μ) (v := 1) 1).integrable (by norm_num) |>.sub
    (integrable_const μ)

/-- `t ↦ (t - μ)² · gaussianPDFReal μ 1 t` is integrable. -/
lemma integrable_centered_sq_gaussianPDFReal (μ : ℝ) :
    Integrable (fun t => (t - μ) ^ 2 * gaussianPDFReal μ 1 t) volume := by
  have hcomm : (fun t => (t - μ) ^ 2 * gaussianPDFReal μ 1 t) =
      (fun t => gaussianPDFReal μ 1 t * (t - μ) ^ 2) := by ext t; rw [mul_comm]
  rw [hcomm, integrable_gaussianReal_iff]
  have h2 : Integrable (fun t : ℝ => t ^ 2) (gaussianReal μ 1) := by
    simpa [id_eq, pow_two] using (memLp_id_gaussianReal (μ := μ) (v := 1) 2).integrable_sq
  have hlin : Integrable (fun t : ℝ => t) (gaussianReal μ 1) :=
    (memLp_id_gaussianReal (μ := μ) (v := 1) 1).integrable (by norm_num)
  have hexp : (fun t : ℝ => (t - μ) ^ 2) = (fun t => t ^ 2 - 2 * μ * t + μ ^ 2) := by
    ext t; ring
  rw [hexp]
  exact (h2.sub (hlin.const_mul (2 * μ))).add (integrable_const _)

/-- The Gaussian PDF (as a 1-D factor) is integrable. -/
lemma integrable_gaussianPDFReal_one (μ : ℝ) :
    Integrable (fun t => gaussianPDFReal μ 1 t) volume :=
  integrable_gaussianPDFReal μ 1

/-! ### The pair integral over the product Gaussian -/

/-- The per-coordinate factor of the centered-pair integrand. -/
private def pairFactor (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) (a b : Fin m)
    (k : Fin m) (t : ℝ) : ℝ :=
  (if k = a then (t - R.mulVec θ a) else 1) * (if k = b then (t - R.mulVec θ b) else 1) *
    gaussianPDFReal (R.mulVec θ k) 1 t

/-- The centered-pair integrand factorizes coordinatewise as `∏ k, pairFactor k (x k)`. -/
private lemma centered_pair_eq_prod (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n)
    (a b : Fin m) (x : Fin m → ℝ) :
    (x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x =
      ∏ k : Fin m, pairFactor R θ a b k (x k) := by
  classical
  simp only [pairFactor, gaussianShiftDensity]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' Finset.univ a (fun k => (x k - R.mulVec θ a))]
  rw [Finset.prod_ite_eq' Finset.univ b (fun k => (x k - R.mulVec θ b))]
  simp only [Finset.mem_univ, if_true]

/-- Each per-coordinate factor is integrable. -/
private lemma integrable_pairFactor (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n)
    (a b : Fin m) (k : Fin m) :
    Integrable (pairFactor R θ a b k) volume := by
  classical
  rcases eq_or_ne k a with hka | hka <;> rcases eq_or_ne k b with hkb | hkb
  · -- k = a = b
    subst hka; subst hkb
    have hf : pairFactor R θ k k k =
        (fun t => (t - R.mulVec θ k) ^ 2 * gaussianPDFReal (R.mulVec θ k) 1 t) := by
      ext t; simp only [pairFactor, if_true]; ring
    rw [hf]; exact integrable_centered_sq_gaussianPDFReal _
  · -- k = a ≠ b
    subst hka
    have hf : pairFactor R θ k b k =
        (fun t => (t - R.mulVec θ k) * gaussianPDFReal (R.mulVec θ k) 1 t) := by
      ext t; simp only [pairFactor, if_true, if_neg hkb]; ring
    rw [hf]; exact integrable_centered_gaussianPDFReal _
  · -- k ≠ a, k = b
    subst hkb
    have hf : pairFactor R θ a k k =
        (fun t => (t - R.mulVec θ k) * gaussianPDFReal (R.mulVec θ k) 1 t) := by
      ext t; simp only [pairFactor, if_true, if_neg hka]; ring
    rw [hf]; exact integrable_centered_gaussianPDFReal _
  · -- k ≠ a, k ≠ b
    have hf : pairFactor R θ a b k = (fun t => gaussianPDFReal (R.mulVec θ k) 1 t) := by
      ext t; simp only [pairFactor, if_neg hka, if_neg hkb]; ring
    rw [hf]; exact integrable_gaussianPDFReal_one _

/-- The integral of each per-coordinate factor. -/
private lemma integral_pairFactor (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n)
    (a b : Fin m) (k : Fin m) :
    ∫ t, pairFactor R θ a b k t =
      (if k = a ∧ k = b then (1 : ℝ) else if k = a ∨ k = b then 0 else 1) := by
  classical
  rcases eq_or_ne k a with hka | hka <;> rcases eq_or_ne k b with hkb | hkb
  · subst hka; subst hkb
    have hf : pairFactor R θ k k k =
        (fun t => (t - R.mulVec θ k) ^ 2 * gaussianPDFReal (R.mulVec θ k) 1 t) := by
      ext t; simp only [pairFactor, if_true]; ring
    rw [hf, gaussian_second_central_moment]; simp
  · subst hka
    have hf : pairFactor R θ k b k =
        (fun t => (t - R.mulVec θ k) * gaussianPDFReal (R.mulVec θ k) 1 t) := by
      ext t; simp only [pairFactor, if_true, if_neg hkb]; ring
    rw [hf, gaussian_first_central_moment]; simp [hkb]
  · subst hkb
    have hf : pairFactor R θ a k k =
        (fun t => (t - R.mulVec θ k) * gaussianPDFReal (R.mulVec θ k) 1 t) := by
      ext t; simp only [pairFactor, if_true, if_neg hka]; ring
    rw [hf, gaussian_first_central_moment]; simp [hka]
  · have hf : pairFactor R θ a b k = (fun t => gaussianPDFReal (R.mulVec θ k) 1 t) := by
      ext t; simp only [pairFactor, if_neg hka, if_neg hkb]; ring
    rw [hf, integral_gaussianPDFReal_eq_one _ one_nnreal_ne_zero]; simp [hka, hkb]

/-- The centered-pair integral over the product Gaussian. -/
lemma integral_centered_pair (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) (a b : Fin m) :
    ∫ x, (x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x =
      (if a = b then (1 : ℝ) else 0) := by
  classical
  -- Rewrite integrand as product over coordinates
  have hcong : (fun x : Fin m → ℝ =>
      (x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x) =
      (fun x => ∏ k : Fin m, pairFactor R θ a b k (x k)) := by
    ext x; exact centered_pair_eq_prod R θ a b x
  rw [hcong]
  rw [integral_fintype_prod_volume_eq_prod (fun k => pairFactor R θ a b k)]
  -- ∏ k, ∫ pairFactor k
  simp_rw [integral_pairFactor R θ a b]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    -- product: at k=a, factor = 1; elsewhere k ≠ a so "k=a∨k=a" false, =1
    apply Finset.prod_eq_one
    intro k _
    by_cases hk : k = a
    · simp [hk]
    · simp [hk]
  · rw [if_neg hab]
    -- product has the factor at k=a equal to 0 (since a=a but a≠b)
    refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    simp [hab]

/-- Integrability of the centered-pair integrand over the product Gaussian. -/
lemma integrable_centered_pair (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n) (a b : Fin m) :
    Integrable (fun x : Fin m → ℝ =>
      (x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x) volume := by
  classical
  have hcong : (fun x : Fin m → ℝ =>
      (x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x) =
      (fun x => ∏ k : Fin m, pairFactor R θ a b k (x k)) := by
    ext x; exact centered_pair_eq_prod R θ a b x
  rw [hcong, show (volume : Measure (Fin m → ℝ)) = Measure.pi (fun _ => volume) from volume_pi]
  exact MeasureTheory.Integrable.fintype_prod (fun k => integrable_pairFactor R θ a b k)

/-! ### Score square-integrability and the Fisher integral -/

/-- The product `scoreFun i · scoreFun j · density` expands into a finite sum of
centered-pair integrands. -/
lemma scoreFun_mul_density_eq_sum (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n)
    (i j : Fin n) (x : Fin m → ℝ) :
    scoreFun R θ i x * scoreFun R θ j x * gaussianShiftDensity R θ x =
      ∑ a : Fin m, ∑ b : Fin m,
        (R a i * R b j) *
          ((x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x) := by
  simp only [scoreFun]
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The Fisher integrand `scoreFun i · scoreFun j · density` is integrable. -/
lemma integrable_scoreFun_mul_density (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n)
    (i j : Fin n) :
    Integrable (fun x => scoreFun R θ i x * scoreFun R θ j x * gaussianShiftDensity R θ x)
      volume := by
  have hcong : (fun x => scoreFun R θ i x * scoreFun R θ j x * gaussianShiftDensity R θ x) =
      (fun x => ∑ a : Fin m, ∑ b : Fin m,
        (R a i * R b j) *
          ((x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x)) := by
    ext x; exact scoreFun_mul_density_eq_sum R θ i j x
  rw [hcong]
  refine integrable_finsetSum _ (fun a _ => ?_)
  refine integrable_finsetSum _ (fun b _ => ?_)
  exact (integrable_centered_pair R θ a b).const_mul _

/-- The Fisher integral `∫ scoreFun i · scoreFun j · density = (Rᵀ R) i j`. -/
lemma integral_scoreFun_mul_density (R : Matrix (Fin m) (Fin n) ℝ) (θ : ParamSpace n)
    (i j : Fin n) :
    ∫ x, scoreFun R θ i x * scoreFun R θ j x * gaussianShiftDensity R θ x =
      (Rᵀ * R) i j := by
  have hcong : (fun x => scoreFun R θ i x * scoreFun R θ j x * gaussianShiftDensity R θ x) =
      (fun x => ∑ a : Fin m, ∑ b : Fin m,
        (R a i * R b j) *
          ((x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x)) := by
    ext x; exact scoreFun_mul_density_eq_sum R θ i j x
  rw [hcong]
  -- exchange ∫ and the double finite sum
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun b _ => (integrable_centered_pair R θ a b).const_mul _))]
  have hinner : ∀ a : Fin m,
      ∫ x, ∑ b : Fin m, (R a i * R b j) *
        ((x a - R.mulVec θ a) * (x b - R.mulVec θ b) * gaussianShiftDensity R θ x) =
      ∑ b : Fin m, (R a i * R b j) * (if a = b then (1 : ℝ) else 0) := by
    intro a
    rw [integral_finsetSum _ (fun b _ => (integrable_centered_pair R θ a b).const_mul _)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [integral_const_mul, integral_centered_pair]
  simp_rw [hinner]
  -- ∑ a ∑ b R a i R b j (if a = b then 1 else 0) = ∑ a R a i R a j = (Rᵀ R) i j
  have hcollapse : ∀ a : Fin m,
      ∑ b : Fin m, (R a i * R b j) * (if a = b then (1 : ℝ) else 0) = R a i * R a j := by
    intro a
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba; simp [Ne.symm hba]
    · intro h; exact absurd (Finset.mem_univ a) h
  simp_rw [hcollapse]
  -- (Rᵀ * R) i j = ∑ a, R a i * R a j
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Matrix.transpose_apply]

/-! ### The integrable derivative bound -/

/-- The mean-norm constant: `K = ∑ₖ ‖meanCLM R k‖`, an upper bound for `|mₖ|` when
`‖θ‖ ≤ 1` and a Lipschitz weight for the score. -/
def meanNormConst (R : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ k : Fin m, ‖meanCLM R k‖

lemma meanNormConst_nonneg (R : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ meanNormConst R :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- For `‖θ‖ ≤ 1`, the `k`-th mean is bounded: `|mₖ| ≤ ‖meanCLM R k‖`. -/
lemma abs_mean_le (R : Matrix (Fin m) (Fin n) ℝ) {θ : ParamSpace n} (hθ : ‖θ‖ ≤ 1)
    (k : Fin m) : |R.mulVec θ k| ≤ ‖meanCLM R k‖ := by
  rw [← meanCLM_apply R k θ]
  calc |meanCLM R k θ| = ‖meanCLM R k θ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖meanCLM R k‖ * ‖θ‖ := (meanCLM R k).le_opNorm θ
    _ ≤ ‖meanCLM R k‖ * 1 := by
        apply mul_le_mul_of_nonneg_left hθ (norm_nonneg _)
    _ = ‖meanCLM R k‖ := mul_one _

/-- The density-bound constant `C₁ = (√(2π))⁻¹ · exp(K²/2)`. -/
def densityBoundConst (R : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (Real.sqrt (2 * π))⁻¹ * Real.exp ((meanNormConst R) ^ 2 / 2)

lemma densityBoundConst_nonneg (R : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ densityBoundConst R := by
  unfold densityBoundConst
  positivity

/-- Per-coordinate Gaussian factor bound: for `‖θ‖ ≤ 1`,
`gaussianPDFReal mₖ 1 t ≤ C₁ · exp(-t²/4)`. -/
lemma gaussianFactor_le (R : Matrix (Fin m) (Fin n) ℝ) {θ : ParamSpace n} (hθ : ‖θ‖ ≤ 1)
    (k : Fin m) (t : ℝ) :
    gaussianPDFReal (R.mulVec θ k) 1 t ≤ densityBoundConst R * Real.exp (-t ^ 2 / 4) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]
  unfold densityBoundConst
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- -(t - m)²/2 ≤ K²/2 + (-t²/4)
  have hm : (R.mulVec θ k) ^ 2 ≤ (meanNormConst R) ^ 2 := by
    have h1 : |R.mulVec θ k| ≤ ‖meanCLM R k‖ := abs_mean_le R hθ k
    have h2 : ‖meanCLM R k‖ ≤ meanNormConst R := by
      unfold meanNormConst
      exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ k)
    have h3 : |R.mulVec θ k| ≤ meanNormConst R := le_trans h1 h2
    calc (R.mulVec θ k) ^ 2 = |R.mulVec θ k| ^ 2 := (sq_abs _).symm
      _ ≤ (meanNormConst R) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _) h3
  -- (t - m)² ≥ t²/2 - m², so -(t-m)²/2 ≤ -t²/4 + m²/2 ≤ K²/2 - t²/4
  -- Key: 2·(t-m)² - t² + 2m² = (t - 2m)² ≥ 0
  have hkey : 2 * (t - R.mulVec θ k) ^ 2 - t ^ 2 + 2 * (R.mulVec θ k) ^ 2 =
      (t - 2 * R.mulVec θ k) ^ 2 := by ring
  nlinarith [sq_nonneg (t - 2 * R.mulVec θ k), hm, hkey]

/-- Density bound: for `‖θ‖ ≤ 1`,
`density θ x ≤ C₁^m · ∏ₖ exp(-xₖ²/4)`. -/
lemma gaussianShiftDensity_le (R : Matrix (Fin m) (Fin n) ℝ) {θ : ParamSpace n} (hθ : ‖θ‖ ≤ 1)
    (x : Fin m → ℝ) :
    gaussianShiftDensity R θ x ≤
      (densityBoundConst R) ^ m * ∏ k : Fin m, Real.exp (-(x k) ^ 2 / 4) := by
  unfold gaussianShiftDensity
  have hrhs : (densityBoundConst R) ^ m * ∏ k : Fin m, Real.exp (-(x k) ^ 2 / 4) =
      ∏ k : Fin m, (densityBoundConst R * Real.exp (-(x k) ^ 2 / 4)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hrhs]
  apply Finset.prod_le_prod
  · intro k _; exact gaussianPDFReal_nonneg _ _ _
  · intro k _; exact gaussianFactor_le R hθ k (x k)

/-- The score-norm bound: for `‖θ‖ ≤ 1`,
`‖scoreCLM R θ x‖ ≤ ∑ₖ (|xₖ| + K) · ‖meanCLM R k‖`. -/
lemma norm_scoreCLM_le (R : Matrix (Fin m) (Fin n) ℝ) {θ : ParamSpace n} (hθ : ‖θ‖ ≤ 1)
    (x : Fin m → ℝ) :
    ‖scoreCLM R θ x‖ ≤ ∑ k : Fin m, (|x k| + meanNormConst R) * ‖meanCLM R k‖ := by
  unfold scoreCLM
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  -- |x k - m_k| ≤ |x k| + K
  calc |x k - R.mulVec θ k| ≤ |x k| + |R.mulVec θ k| := abs_sub _ _
    _ ≤ |x k| + meanNormConst R := by
        gcongr
        refine le_trans (abs_mean_le R hθ k) ?_
        unfold meanNormConst
        exact Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ k)

/-- The integrable derivative bound function. -/
def gaussianDerivBound (R : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) : ℝ :=
  (densityBoundConst R) ^ m *
    ((∑ k : Fin m, (|x k| + meanNormConst R) * ‖meanCLM R k‖) *
      ∏ k : Fin m, Real.exp (-(x k) ^ 2 / 4))

lemma gaussianDerivBound_nonneg (R : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) :
    0 ≤ gaussianDerivBound R x := by
  unfold gaussianDerivBound
  apply mul_nonneg (pow_nonneg (densityBoundConst_nonneg R) m)
  apply mul_nonneg
  · refine Finset.sum_nonneg (fun k _ => mul_nonneg ?_ (norm_nonneg _))
    exact add_nonneg (abs_nonneg _) (meanNormConst_nonneg R)
  · exact Finset.prod_nonneg (fun k _ => by positivity)

/-- `t ↦ exp(-t²/4)` is integrable over `volume`. -/
lemma integrable_exp_neg_sq_div_four :
    Integrable (fun t : ℝ => Real.exp (-(t) ^ 2 / 4)) volume := by
  have : (fun t : ℝ => Real.exp (-(t) ^ 2 / 4)) = (fun t : ℝ => Real.exp (-(4:ℝ)⁻¹ * t ^ 2)) := by
    ext t
    have : -(t) ^ 2 / 4 = -(4:ℝ)⁻¹ * t ^ 2 := by ring
    rw [this]
  rw [this]
  exact integrable_exp_neg_mul_sq (by norm_num)

/-- `t ↦ (|t| + c) · exp(-t²/4)` is integrable over `volume`. -/
lemma integrable_abs_add_mul_exp (c : ℝ) :
    Integrable (fun t : ℝ => (|t| + c) * Real.exp (-(t) ^ 2 / 4)) volume := by
  have hexp := integrable_exp_neg_sq_div_four
  have habs : Integrable (fun t : ℝ => |t| * Real.exp (-(t) ^ 2 / 4)) volume := by
    have : (fun t : ℝ => |t| * Real.exp (-(t) ^ 2 / 4)) =
        (fun t : ℝ => |t * Real.exp (-(t) ^ 2 / 4)|) := by
      ext t; rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    rw [this]
    apply (Integrable.abs ?_)
    have : (fun t : ℝ => t * Real.exp (-(t) ^ 2 / 4)) =
        (fun t : ℝ => t * Real.exp (-(4:ℝ)⁻¹ * t ^ 2)) := by
      ext t
      have : -(t) ^ 2 / 4 = -(4:ℝ)⁻¹ * t ^ 2 := by ring
      rw [this]
    rw [this]
    exact integrable_mul_exp_neg_mul_sq (by norm_num)
  have hsum : (fun t : ℝ => (|t| + c) * Real.exp (-(t) ^ 2 / 4)) =
      (fun t : ℝ => |t| * Real.exp (-(t) ^ 2 / 4) + c * Real.exp (-(t) ^ 2 / 4)) := by
    ext t; ring
  rw [hsum]
  exact habs.add (hexp.const_mul c)

/-- Per-coordinate factor used to split `gaussianDerivBound` into a sum of products. -/
private def boundFactor (R : Matrix (Fin m) (Fin n) ℝ) (k : Fin m) (j : Fin m) (t : ℝ) : ℝ :=
  if j = k then (|t| + meanNormConst R) * Real.exp (-(t) ^ 2 / 4) else Real.exp (-(t) ^ 2 / 4)

private lemma integrable_boundFactor (R : Matrix (Fin m) (Fin n) ℝ) (k j : Fin m) :
    Integrable (boundFactor R k j) volume := by
  unfold boundFactor
  by_cases h : j = k
  · simp only [h, if_true]; exact integrable_abs_add_mul_exp _
  · simp only [h, if_false]; exact integrable_exp_neg_sq_div_four

/-- `gaussianDerivBound` rewrites as a finite sum of coordinatewise products. -/
private lemma gaussianDerivBound_eq_sum (R : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) :
    gaussianDerivBound R x =
      ∑ k : Fin m, (densityBoundConst R) ^ m * ‖meanCLM R k‖ *
        ∏ j : Fin m, boundFactor R k j (x j) := by
  classical
  unfold gaussianDerivBound
  -- ∏ boundFactor k = (|x k|+K) ∏ exp
  have hprod : ∀ k : Fin m, ∏ j : Fin m, boundFactor R k j (x j) =
      (|x k| + meanNormConst R) * ∏ j : Fin m, Real.exp (-(x j) ^ 2 / 4) := by
    intro k
    have hfac : ∀ j : Fin m, boundFactor R k j (x j) =
        Real.exp (-(x j) ^ 2 / 4) * (if j = k then (|x j| + meanNormConst R) else 1) := by
      intro j; unfold boundFactor; by_cases h : j = k <;> simp [h, mul_comm]
    simp_rw [hfac]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k
        (fun j => (|x j| + meanNormConst R))]
    simp only [Finset.mem_univ, if_true]
    ring
  simp_rw [hprod]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-- The derivative bound is integrable over `Fin m → ℝ`. -/
lemma integrable_gaussianDerivBound (R : Matrix (Fin m) (Fin n) ℝ) :
    Integrable (gaussianDerivBound R) (volume : Measure (Fin m → ℝ)) := by
  have hcong : gaussianDerivBound R =
      (fun x => ∑ k : Fin m, (densityBoundConst R) ^ m * ‖meanCLM R k‖ *
        ∏ j : Fin m, boundFactor R k j (x j)) := by
    ext x; exact gaussianDerivBound_eq_sum R x
  rw [hcong]
  refine integrable_finsetSum _ (fun k _ => ?_)
  apply Integrable.const_mul
  rw [show (volume : Measure (Fin m → ℝ)) = Measure.pi (fun _ => volume) from volume_pi]
  exact MeasureTheory.Integrable.fintype_prod (fun j => integrable_boundFactor R k j)

/-- The key bound: `‖D_θ p(θ, x)‖ ≤ gaussianDerivBound R x` for `θ ∈ ball 0 1`. -/
lemma density_fderiv_norm_le_bound (R : Matrix (Fin m) (Fin n) ℝ) {θ : ParamSpace n}
    (hθ : θ ∈ Metric.ball (0 : ParamSpace n) 1) (x : Fin m → ℝ) :
    ‖fderiv ℝ (fun θ' => gaussianShiftDensity R θ' x) θ‖ ≤ gaussianDerivBound R x := by
  have hθ1 : ‖θ‖ ≤ 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hθ
    exact le_of_lt hθ
  rw [fderiv_gaussianShiftDensity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (gaussianShiftDensity_nonneg R θ x)]
  unfold gaussianDerivBound
  -- density · ‖scoreCLM‖ ≤ (C₁^m ∏ exp) · (∑ ...)
  calc gaussianShiftDensity R θ x * ‖scoreCLM R θ x‖
      ≤ ((densityBoundConst R) ^ m * ∏ k : Fin m, Real.exp (-(x k) ^ 2 / 4)) *
          (∑ k : Fin m, (|x k| + meanNormConst R) * ‖meanCLM R k‖) := by
        apply mul_le_mul (gaussianShiftDensity_le R hθ1 x) (norm_scoreCLM_le R hθ1 x)
          (norm_nonneg _)
        apply mul_nonneg (pow_nonneg (densityBoundConst_nonneg R) m)
        exact Finset.prod_nonneg (fun k _ => by positivity)
    _ = (densityBoundConst R) ^ m *
          ((∑ k : Fin m, (|x k| + meanNormConst R) * ‖meanCLM R k‖) *
            ∏ k : Fin m, Real.exp (-(x k) ^ 2 / 4)) := by ring

/-! ### The model -/

/-- The **Gaussian shift model** with mean map `R`: a `RegularStatisticalModel` on
`Fin m → ℝ` whose Fisher matrix is the constant Gram matrix `Rᵀ R`. -/
def gaussianShiftModel (R : Matrix (Fin m) (Fin n) ℝ) :
    RegularStatisticalModel n (Fin m → ℝ) where
  paramDomain := Metric.ball 0 1
  isOpen_paramDomain := Metric.isOpen_ball
  nonempty_paramDomain := ⟨0, by simp⟩
  refMeasure := volume
  sigmaFinite_refMeasure := by infer_instance
  density := gaussianShiftDensity R
  density_nonneg := fun θ _ x => gaussianShiftDensity_nonneg R θ x
  density_measurable := fun θ _ => measurable_gaussianShiftDensity R θ
  density_integral_one := fun θ _ => integral_gaussianShiftDensity R θ
  density_pos_ae := fun θ _ => ae_of_all _ fun x => gaussianShiftDensity_pos R θ x
  density_smooth := fun x => (contDiff_gaussianShiftDensity R x).contDiffOn
  derivBound := gaussianDerivBound R
  derivBound_integrable := integrable_gaussianDerivBound R
  derivBound_nonneg := gaussianDerivBound_nonneg R
  density_fderiv_norm_le := fun θ hθ x => density_fderiv_norm_le_bound R hθ x
  score_sq_integrable := by
    intro θ _ i
    -- the integrand equals (scoreFun θ i)² · density
    have hcong : (fun ω => ((fderiv ℝ (fun θ' => gaussianShiftDensity R θ' ω) θ
          (EuclideanSpace.single i 1)) / gaussianShiftDensity R θ ω) ^ 2 *
            gaussianShiftDensity R θ ω) =
        (fun ω => scoreFun R θ i ω * scoreFun R θ i ω * gaussianShiftDensity R θ ω) := by
      ext ω
      rw [score_gaussianShift]
      ring
    rw [hcong]
    exact integrable_scoreFun_mul_density R θ i i
  density_fderiv_aestronglyMeasurable :=
    fun θ _ => aestronglyMeasurable_fderiv_gaussianShiftDensity R θ

/-! ### The Fisher matrix -/

/-- **The Fisher matrix of the Gaussian shift model is the Gram matrix `Rᵀ R`.**
Since each coordinate has unit variance and the mean is linear in `θ`, the score is the
affine field `s(θ, x) = Rᵀ (x − R θ)`, whose covariance under the model is `Rᵀ R`. -/
theorem gaussianShiftModel_fisherMatrix (R : Matrix (Fin m) (Fin n) ℝ)
    {θ : ParamSpace n} (_ : θ ∈ (gaussianShiftModel R).paramDomain) (i j : Fin n) :
    (gaussianShiftModel R).fisherMatrix θ i j = (Rᵀ * R) i j := by
  rw [RegularStatisticalModel.fisherMatrix]
  -- rewrite the integrand: score = scoreFun, density = gaussianShiftDensity
  have hcong : (fun ω => (gaussianShiftModel R).score θ i ω *
      (gaussianShiftModel R).score θ j ω * (gaussianShiftModel R).density θ ω) =
      (fun ω => scoreFun R θ i ω * scoreFun R θ j ω * gaussianShiftDensity R θ ω) := by
    ext ω
    change ((gaussianShiftModel R).partialDensity θ i ω / (gaussianShiftModel R).density θ ω) *
      ((gaussianShiftModel R).partialDensity θ j ω / (gaussianShiftModel R).density θ ω) *
      (gaussianShiftModel R).density θ ω = _
    simp only [RegularStatisticalModel.partialDensity]
    change ((fderiv ℝ (fun θ' => gaussianShiftDensity R θ' ω) θ (EuclideanSpace.single i 1)) /
        gaussianShiftDensity R θ ω) *
      ((fderiv ℝ (fun θ' => gaussianShiftDensity R θ' ω) θ (EuclideanSpace.single j 1)) /
        gaussianShiftDensity R θ ω) * gaussianShiftDensity R θ ω = _
    rw [score_gaussianShift, score_gaussianShift]
  rw [hcong]
  exact integral_scoreFun_mul_density R θ i j

end Spectra.InformationGeometry

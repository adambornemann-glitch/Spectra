/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Perturbation.Hardy.Inequality.Basic
import Spectra.Spaces.Sobolev.WeakDerivative
import Spectra.Spaces.Sobolev.IntegrationByParts
import Spectra.Spaces.Sobolev.DensityResults
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! ## Better docstring to go here soon-/
open MeasureTheory Complex Filter ContinuousLinearMap
open MeasurableSet ContDiffBump Topology
open Spectra.Sobolev
open scoped Topology NNReal ENNReal TopologicalSpace ProbabilityTheory
open scoped Pointwise ContDiff RealInnerProductSpace

namespace Spectra.QuantumMechanics.Hydrogen

/-! ## Gradient of a radial function

The technical core of the sharpness argument: for a radial function `φ(x) = g(‖x‖)`,
the pointwise Dirichlet integrand `∑ᵢ |∂ᵢφ|²` equals `(g'(‖x‖))²`. -/

/-- Fréchet derivative of the Euclidean norm away from the origin:
    `∇‖·‖(x) = ‖x‖⁻¹ • ⟪x, ·⟫`. Derived from `‖y‖ = √(‖y‖²)` and `fderiv_norm_sq`. -/
lemma hasFDerivAt_norm_ne_zero {x : R3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : R3 => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  -- `√` is differentiable at `‖x‖² > 0`.
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖x‖ ^ 2))) (‖x‖ ^ 2) :=
    Real.hasDerivAt_sqrt (ne_of_gt hsq)
  -- Compose with `y ↦ ‖y‖²`.
  have hcomp : HasFDerivAt (fun y : R3 => Real.sqrt (‖y‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x :=
    hsqrt.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  -- `√(‖y‖²) = ‖y‖` pointwise, and the derivative simplifies to `‖x‖⁻¹ • innerSL ℝ x`.
  have hfun : (fun y : R3 => Real.sqrt (‖y‖ ^ 2)) = (fun y : R3 => ‖y‖) := by
    funext y; exact Real.sqrt_sq (norm_nonneg y)
  rw [hfun] at hcomp
  have h2 : (2 : ℕ) • innerSL ℝ x = (2 : ℝ) • innerSL ℝ x := by
    rw [← Nat.cast_smul_eq_nsmul ℝ]; norm_num
  have hder : (1 / (2 * Real.sqrt (‖x‖ ^ 2))) • (2 • innerSL ℝ x)
      = ‖x‖⁻¹ • innerSL ℝ x := by
    rw [Real.sqrt_sq hpos.le, h2, smul_smul]
    congr 1
    field_simp
  rwa [hder] at hcomp

/-- **Radial gradient identity (M3).** For a real radial profile `g` differentiable on
    `(0,∞)` with derivative `g'`, the squared gradient of the complex radial function
    `φ(x) = (g(‖x‖) : ℂ)` is `(g'(‖x‖))²` away from the origin. -/
lemma radial_gradient_sq {g g' : ℝ → ℝ}
    (hg : ∀ r : ℝ, 0 < r → HasDerivAt g (g' r) r) {x : R3} (hx : x ≠ 0) :
    ∑ i : Fin 3,
        ‖fderiv ℝ (fun y : R3 => (g ‖y‖ : ℂ)) x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
      = (g' ‖x‖) ^ 2 := by
  have hpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  -- Chain rule: `g ∘ ‖·‖` then `ofReal`.
  have hN : HasFDerivAt (fun y : R3 => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x :=
    hasFDerivAt_norm_ne_zero hx
  have hgr : HasDerivAt g (g' ‖x‖) ‖x‖ := hg ‖x‖ hpos
  have hcomp : HasFDerivAt (fun y : R3 => g ‖y‖)
      ((g' ‖x‖) • (‖x‖⁻¹ • innerSL ℝ x)) x :=
    hgr.comp_hasFDerivAt x hN
  have hC : HasFDerivAt (fun y : R3 => (g ‖y‖ : ℂ))
      (Complex.ofRealCLM.comp ((g' ‖x‖) • (‖x‖⁻¹ • innerSL ℝ x))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hcomp
  rw [hC.fderiv]
  set c : ℝ := g' ‖x‖ with hc
  set ρ : ℝ := ‖x‖⁻¹ with hρ
  -- Evaluate each component as a real number cast into `ℂ`.
  have hcoe : ∀ i : Fin 3,
      (Complex.ofRealCLM.comp (c • (ρ • innerSL ℝ x)))
          (EuclideanSpace.single i (1 : ℝ))
        = ((c * (ρ * x i) : ℝ) : ℂ) := by
    intro i
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, innerSL_apply_apply,
        EuclideanSpace.inner_single_right]
    simp only [one_mul, starRingEnd_apply, star_trivial, smul_eq_mul,
      Complex.ofRealCLM_apply]
  simp only [hcoe]
  -- `‖(real : ℂ)‖² = real²`, then factor and use `∑ (xᵢ)² = ‖x‖²`.
  have hnorm : ∀ i : Fin 3, ‖((c * (ρ * x i) : ℝ) : ℂ)‖ ^ 2
      = (c ^ 2 * ρ ^ 2) * (x i) ^ 2 := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
  simp only [hnorm]
  rw [← Finset.mul_sum]
  have hsum : ∑ i : Fin 3, (x i) ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  rw [hsum, hc, hρ, mul_assoc, inv_pow,
      inv_mul_cancel₀ (by positivity : (‖x‖ : ℝ) ^ 2 ≠ 0), mul_one]

/-! ## Radial reduction of the Rayleigh integrals

For a radial `C_c^∞` function `φ(x) = (g(‖x‖) : ℂ)`, both `hardyIntegral` and
`gradientNormSq` reduce to one-dimensional radial integrals against a fixed positive
geometric constant `radialConst = 3 · vol(unit ball) = 4π`. We never evaluate the
constant: it cancels in the Rayleigh ratio. -/

/-- The geometric constant `dim ℝ³ · vol(unit ball) = 4π` from the radial disintegration. -/
noncomputable def radialConst : ℝ :=
  (Module.finrank ℝ R3 : ℝ) * (volume : Measure R3).real (Metric.ball 0 1)

lemma radialConst_pos : 0 < radialConst := by
  have h2 : 0 < (volume : Measure R3).real (Metric.ball 0 1) := by
    have hpos : 0 < (volume : Measure R3) (Metric.ball 0 1) :=
      Metric.measure_ball_pos (volume : Measure R3) 0 one_pos
    have hlt : (volume : Measure R3) (Metric.ball 0 1) < ⊤ := measure_ball_lt_top
    rw [MeasureTheory.measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' hlt.ne
  have h1 : (0 : ℝ) < (Module.finrank ℝ R3 : ℝ) := by
    rw [finrank_euclideanSpace_fin]; norm_num
  rw [radialConst]; positivity

/-- **Radial disintegration.** The Lebesgue integral of a radial integrand `f(‖x‖)` over
    `ℝ³` is `radialConst · ∫₀^∞ r²·f(r) dr`. Packages `integral_fun_norm_addHaar`. -/
lemma radialReduction (f : ℝ → ℝ) :
    ∫ x, f ‖x‖ ∂(volume : Measure R3)
      = radialConst * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * f r := by
  haveI : (volume : Measure R3).IsAddHaarMeasure := inferInstance
  have hdim : Module.finrank ℝ R3 = 3 := finrank_euclideanSpace_fin
  rw [MeasureTheory.integral_fun_norm_addHaar (volume : Measure R3) f, hdim]
  have hint : (∫ y in Set.Ioi (0 : ℝ), y ^ (3 - 1) • f y)
      = ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * f r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _; norm_num
  rw [hint, radialConst, hdim, nsmul_eq_mul, smul_eq_mul]
  push_cast; ring

/-- **Hardy integral of a radial function** as a 1-D radial integral. -/
lemma hardyIntegral_radial {g : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ (fun y : R3 => (g ‖y‖ : ℂ)))
    (hsupp : HasCompactSupport (fun y : R3 => (g ‖y‖ : ℂ))) :
    hardyIntegral
        ((memLp_of_smooth_compactSupport (fun y : R3 => (g ‖y‖ : ℂ)) hsmooth hsupp).toLp _)
      = radialConst * ∫ r in Set.Ioi (0 : ℝ), g r ^ 2 := by
  rw [hardyIntegral_toLp (memLp_of_smooth_compactSupport _ hsmooth hsupp)]
  have key : (fun x : R3 => inverseRSq x * ‖(g ‖x‖ : ℂ)‖ ^ 2)
      = fun x : R3 => (fun r => (if r = 0 then 0 else 1 / r ^ 2) * g r ^ 2) ‖x‖ := by
    funext x
    simp only [inverseRSq]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [key, radialReduction (fun r => (if r = 0 then 0 else 1 / r ^ 2) * g r ^ 2)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hrne : r ≠ 0 := ne_of_gt hr
  change r ^ 2 * ((if r = 0 then 0 else 1 / r ^ 2) * g r ^ 2) = g r ^ 2
  rw [if_neg hrne]
  field_simp

/-- **Dirichlet integral of a radial function** as a 1-D radial integral. -/
lemma gradientNormSq_radial {g g' : ℝ → ℝ}
    (hg : ∀ r : ℝ, 0 < r → HasDerivAt g (g' r) r)
    (hsmooth : ContDiff ℝ ∞ (fun y : R3 => (g ‖y‖ : ℂ)))
    (hsupp : HasCompactSupport (fun y : R3 => (g ‖y‖ : ℂ))) :
    gradientNormSq
        ((memLp_of_smooth_compactSupport (fun y : R3 => (g ‖y‖ : ℂ)) hsmooth hsupp).toLp _)
        (sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 _ hsmooth hsupp
          (memLp_of_smooth_compactSupport _ hsmooth hsupp)))
      = radialConst * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (g' r) ^ 2 := by
  rw [gradientNormSq_toLp hsmooth hsupp (memLp_of_smooth_compactSupport _ hsmooth hsupp)]
  have hae : ∀ᵐ x ∂(volume : Measure R3), x ≠ 0 := by
    have hz : (volume : Measure R3) {x : R3 | x = 0} = 0 := by
      have he : {x : R3 | x = 0} = {(0 : R3)} := by ext x; simp
      rw [he]; exact measure_singleton 0
    rw [ae_iff]; simp only [ne_eq, not_not]; exact hz
  have key : (∫ x, ∑ i : Fin 3,
        ‖fderiv ℝ (fun y : R3 => (g ‖y‖ : ℂ)) x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
      = ∫ x : R3, (fun r => (g' r) ^ 2) ‖x‖ := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    exact radial_gradient_sq hg hx
  rw [key, radialReduction (fun r => (g' r) ^ 2)]

/-! ## The fixed bump profile `η`

A single smooth bump on `ℝ`, `= 1` on `[-½,½]`, supported in `(-1,1)`. Its `log`-scale
dilation drives the optimizing sequence. We only need: smooth, compactly supported,
`η = 0` off `(-1,1)`, and `∫ η² > 0`. -/

/-- The reference bump: rOut = 1, rIn = ½. -/
noncomputable def bumpη : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The bump as a plain function `ℝ → ℝ`. -/
noncomputable def etaFn : ℝ → ℝ := fun t => bumpη t

lemma etaFn_contDiff : ContDiff ℝ ∞ etaFn := bumpη.contDiff

lemma etaFn_hasCompactSupport : HasCompactSupport etaFn := bumpη.hasCompactSupport

lemma etaFn_nonneg (t : ℝ) : 0 ≤ etaFn t := bumpη.nonneg

/-- `η` vanishes outside `(-1,1)`. -/
lemma etaFn_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : etaFn t = 0 := by
  have h : t ∉ Function.support (⇑bumpη) := by
    rw [bumpη.support_eq]
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact ht
  simpa only [etaFn, Function.mem_support, ne_eq, not_not] using h

lemma etaFn_integrable_sq : Integrable (fun t => etaFn t ^ 2) :=
  (etaFn_contDiff.continuous.pow 2).integrable_of_hasCompactSupport
    (etaFn_hasCompactSupport.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num))

/-- `∫ η² > 0`: `η` is continuous, nonnegative, and positive at `0`. -/
lemma etaFn_sq_integral_pos : 0 < ∫ t, etaFn t ^ 2 := by
  rw [integral_pos_iff_support_of_nonneg (fun t => sq_nonneg _) etaFn_integrable_sq]
  have hsupp : Function.support (fun t => etaFn t ^ 2) = Function.support (⇑bumpη) := by
    ext t; simp only [Function.mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
      not_false_eq_true, etaFn]
  rw [hsupp, bumpη.support_eq]
  exact Metric.measure_ball_pos _ _ bumpη.rOut_pos

/-! ## The optimizing profile `gₙ` and `φₙ`

`gₙ(r) = r^{-1/2}·η(log r / n)`, the Emden–Fowler dilation of the bump. The complex
radial optimizer is `φₙ(x) = (gₙ(‖x‖) : ℂ)`, genuinely `C_c^∞` (it vanishes near `0`). -/

/-- Radial profile `gₙ(r) = r^{-1/2}·η(log r / n)`. -/
noncomputable def gN (n r : ℝ) : ℝ := r ^ (-(1:ℝ)/2) * etaFn (Real.log r / n)

/-- Its derivative on `(0,∞)`: `gₙ'(r) = r^{-3/2}(η'(log r/n)/n − η(log r/n)/2)`. -/
noncomputable def gN' (n r : ℝ) : ℝ :=
  r ^ (-(3:ℝ)/2) * (deriv etaFn (Real.log r / n) / n - etaFn (Real.log r / n) / 2)

/-- The complex radial optimizer `φₙ(x) = (gₙ(‖x‖) : ℂ)`. -/
noncomputable def phiN (n : ℝ) : R3 → ℂ := fun y => (gN n ‖y‖ : ℂ)

lemma gN_eq_zero_of_one_le {n r : ℝ} (h : 1 ≤ |Real.log r / n|) :
    gN n r = 0 := by
  rw [gN, etaFn_zero_of_one_le_abs h, mul_zero]

lemma gN_eq_zero_of_lt {n : ℝ} (hn : 0 < n) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < Real.exp (-n)) : gN n r = 0 := by
  rcases eq_or_lt_of_le hr0 with h | hpos
  · rw [gN, ← h, Real.zero_rpow (by norm_num), zero_mul]
  · apply gN_eq_zero_of_one_le
    rw [abs_div, abs_of_pos hn, le_div_iff₀ hn, one_mul]
    have hlog : Real.log r < -n := by
      have := Real.log_lt_log hpos hr; rwa [Real.log_exp] at this
    rw [abs_of_neg (by linarith : Real.log r < 0)]; linarith

/-- The derivative of `gₙ` on `(0,∞)`. -/
lemma gN_hasDerivAt {n : ℝ} {r : ℝ} (hr : 0 < r) :
    HasDerivAt (gN n) (gN' n r) r := by
  have ha : HasDerivAt (fun x : ℝ => x ^ (-(1:ℝ)/2)) (-(1:ℝ)/2 * r ^ (-(1:ℝ)/2 - 1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hr.ne')
  have hlog : HasDerivAt (fun x : ℝ => Real.log x / n) (r⁻¹ / n) r :=
    (Real.hasDerivAt_log hr.ne').div_const n
  have heta : HasDerivAt etaFn (deriv etaFn (Real.log r / n)) (Real.log r / n) :=
    (etaFn_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hb : HasDerivAt (fun x : ℝ => etaFn (Real.log x / n))
      (deriv etaFn (Real.log r / n) * (r⁻¹ / n)) r := heta.comp r hlog
  convert ha.mul hb using 1
  rw [gN', show (-(1:ℝ)/2 - 1) = -(3:ℝ)/2 from by ring]
  have e1 : r ^ (-(1:ℝ)/2) * r⁻¹ = r ^ (-(3:ℝ)/2) := by
    rw [← Real.rpow_neg_one r, ← Real.rpow_add hr]; norm_num
  have e2 : r ^ (-(1:ℝ)/2) * (deriv etaFn (Real.log r / n) * (r⁻¹ / n))
      = r ^ (-(3:ℝ)/2) * (deriv etaFn (Real.log r / n) / n) := by
    rw [← e1]; ring
  rw [e2]; ring

lemma gN_contDiffAt {n : ℝ} {r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ∞ (gN n) r := by
  change ContDiffAt ℝ ∞ (fun x => x ^ (-(1:ℝ)/2) * etaFn (Real.log x / n)) r
  exact (Real.contDiffAt_rpow_const_of_ne hr.ne').mul
    (etaFn_contDiff.contDiffAt.comp r ((Real.contDiffAt_log.mpr hr.ne').div_const n))

/-- `φₙ` is smooth: a composition off the origin, and `≡ 0` near the origin. -/
lemma phiN_contDiff {n : ℝ} (hn : 0 < n) : ContDiff ℝ ∞ (phiN n) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · have h0 : ContDiffAt ℝ ∞ (fun _ : R3 => (0 : ℂ)) 0 := contDiffAt_const
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : R3) (Real.exp_pos (-n))] with z hz
    have hzr : ‖z‖ < Real.exp (-n) := by simpa [dist_zero_right] using hz
    change (gN n ‖z‖ : ℂ) = (0 : ℂ)
    rw [gN_eq_zero_of_lt hn (norm_nonneg z) hzr, Complex.ofReal_zero]
  · change ContDiffAt ℝ ∞ (fun y : R3 => (gN n ‖y‖ : ℂ)) y
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp y
      ((gN_contDiffAt (norm_pos_iff.mpr hy)).comp y (contDiffAt_norm (𝕜 := ℝ) hy))

/-- `φₙ` has compact support (in the closed ball of radius `eⁿ`). -/
lemma phiN_hasCompactSupport {n : ℝ} (hn : 0 < n) : HasCompactSupport (phiN n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : R3) (Real.exp n))
  intro y hy
  change (gN n ‖y‖ : ℂ) = 0
  have hynorm : Real.exp n < ‖y‖ := by
    simpa [dist_zero_right, Metric.mem_closedBall, not_le] using hy
  rw [gN_eq_zero_of_one_le ?_, Complex.ofReal_zero]
  rw [abs_div, abs_of_pos hn, le_div_iff₀ hn, one_mul]
  have hlog : n < Real.log ‖y‖ := by
    have := Real.log_lt_log (Real.exp_pos n) hynorm; rwa [Real.log_exp] at this
  rw [abs_of_pos (by linarith : (0:ℝ) < Real.log ‖y‖)]; linarith

/-! ## The 1-D radial integrals

Evaluate the two radial integrals via the Emden–Fowler substitution `r = eᵗ`
(`∫₀^∞ r⁻¹·k(log r) dr = ∫_ℝ k`) and the rescaling `t ↦ t/n`. -/

/-- **Log substitution.** `∫₀^∞ r⁻¹·k(log r) dr = ∫_ℝ k(t) dt`. The map `t ↦ eᵗ` is a
    `C¹` bijection `ℝ → (0,∞)` with derivative `eᵗ`, cancelling the `r⁻¹` weight. -/
lemma logChange (k : ℝ → ℝ) :
    ∫ r in Set.Ioi (0 : ℝ), r⁻¹ * k (Real.log r) = ∫ t : ℝ, k t := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
    (s := Set.univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn) (fun r => r⁻¹ * k (Real.log r))
  simp only [Set.image_univ, Real.range_exp] at h
  rw [h, setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.log_exp]
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (Real.exp_pos x).ne', one_mul]

/-- **M4 — Hardy radial integral.** `∫₀^∞ gₙ² = n·∫η²`. -/
lemma hardyIntegral_value {n : ℝ} (hn : 0 < n) :
    ∫ r in Set.Ioi (0 : ℝ), gN n r ^ 2 = n * ∫ t, etaFn t ^ 2 := by
  have step1 : ∫ r in Set.Ioi (0 : ℝ), gN n r ^ 2
      = ∫ r in Set.Ioi (0 : ℝ), r⁻¹ * (fun u => etaFn (u / n) ^ 2) (Real.log r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [gN, mul_pow]
    congr 1
    rw [pow_two, ← Real.rpow_add hr, show -(1:ℝ)/2 + -(1:ℝ)/2 = -1 from by ring,
        Real.rpow_neg_one]
  rw [step1, logChange (fun u => etaFn (u / n) ^ 2)]
  have hbeta : (∫ t, (fun u => etaFn (u / n) ^ 2) t)
      = ∫ t, (fun u => etaFn u ^ 2) (t / n) := rfl
  rw [hbeta, Measure.integral_comp_div (fun u => etaFn u ^ 2) n, abs_of_pos hn, smul_eq_mul]

/-- **M5 — Dirichlet radial integral.** `∫₀^∞ r²·(gₙ')² = n·∫(η'/n − η/2)²`. -/
lemma gradientNormSq_value {n : ℝ} (hn : 0 < n) :
    ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (gN' n r) ^ 2
      = n * ∫ s, (deriv etaFn s / n - etaFn s / 2) ^ 2 := by
  have step1 : ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (gN' n r) ^ 2
      = ∫ r in Set.Ioi (0 : ℝ), r⁻¹ *
          (fun u => (deriv etaFn (u / n) / n - etaFn (u / n) / 2) ^ 2) (Real.log r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [gN', mul_pow]
    rw [← mul_assoc]
    congr 1
    rw [pow_two (r ^ (-(3:ℝ)/2)), ← Real.rpow_add hr,
        show -(3:ℝ)/2 + -(3:ℝ)/2 = -3 from by ring,
        ← Real.rpow_natCast r 2, ← Real.rpow_add hr,
        show ((2:ℕ):ℝ) + -3 = -1 from by push_cast; ring, Real.rpow_neg_one]
  rw [step1, logChange (fun u => (deriv etaFn (u / n) / n - etaFn (u / n) / 2) ^ 2)]
  have hbeta : (∫ t, (fun u => (deriv etaFn (u / n) / n - etaFn (u / n) / 2) ^ 2) t)
      = ∫ t, (fun s => (deriv etaFn s / n - etaFn s / 2) ^ 2) (t / n) := rfl
  rw [hbeta, Measure.integral_comp_div (fun s => (deriv etaFn s / n - etaFn s / 2) ^ 2) n,
      abs_of_pos hn, smul_eq_mul]

/-- Expansion of the Dirichlet 1-D integrand: `∫(η'/n − η/2)² = ∫η'²/n² − ∫η'η/n + ∫η²/4`.
    The `1/n²` and `1/n` terms vanish in the limit; only `∫η²/4` survives. -/
lemma denom_expand {n : ℝ} (hn : n ≠ 0) :
    ∫ s, (deriv etaFn s / n - etaFn s / 2) ^ 2
      = (∫ s, (deriv etaFn s) ^ 2) / n ^ 2
        - (∫ s, deriv etaFn s * etaFn s) / n + (∫ s, etaFn s ^ 2) / 4 := by
  have hDcont : Continuous (deriv etaFn) := etaFn_contDiff.continuous_deriv (by norm_num)
  have hDsupp : HasCompactSupport (deriv etaFn) := etaFn_hasCompactSupport.deriv
  have hA : Integrable (fun s => (deriv etaFn s) ^ 2) :=
    (hDcont.pow 2).integrable_of_hasCompactSupport
      (hDsupp.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num))
  have hB : Integrable (fun s => deriv etaFn s * etaFn s) :=
    (hDcont.mul etaFn_contDiff.continuous).integrable_of_hasCompactSupport hDsupp.mul_right
  have hpt : ∀ s, (deriv etaFn s / n - etaFn s / 2) ^ 2
      = (deriv etaFn s) ^ 2 / n ^ 2 - deriv etaFn s * etaFn s / n + etaFn s ^ 2 / 4 := by
    intro s; field_simp; ring
  simp_rw [hpt]
  have hf : Integrable (fun s => deriv etaFn s ^ 2 / n ^ 2 - deriv etaFn s * etaFn s / n) :=
    (hA.div_const _).sub (hB.div_const _)
  rw [integral_add hf (etaFn_integrable_sq.div_const _),
      integral_sub (hA.div_const _) (hB.div_const _),
      integral_div, integral_div, integral_div]

/-! ## Sharpness of the constant -/
/-- **The constant 4 is sharp.**

    There is no `C < 4` such that `∫|ψ|²/|x|² ≤ C·∫|∇ψ|²` for all `ψ ∈ H¹(ℝ³)`.

    **Proof.** The Emden–Fowler optimizing family `φₙ(x) = |x|^{−1/2}·η(log|x|/n)`
    (`η` a fixed smooth bump) is genuinely `C_c^∞` (it vanishes near `0`). Reducing both
    Rayleigh integrals to one-dimensional radial integrals (`radialReduction`) and the
    substitution `r = eᵗ` (`logChange`) gives, with `Ia = ∫η² > 0`, `Ib = ∫η'²`,
    `Ic = ∫η'η`, and the positive geometric constant `K = radialConst`:
      `hardyIntegral φₙ = K·n·Ia`,  `gradientNormSq φₙ = K·n·(Ib/n² − Ic/n + Ia/4)`.
    Feeding `φₙ` to the hypothesis and cancelling `K·n > 0` yields
    `Ia ≤ C·(Ib/n² − Ic/n + Ia/4)` for every `n > 0`. Letting `n → ∞`, the right side
    tends to `C·(Ia/4)`, so `Ia ≤ C·Ia/4`; since `Ia > 0`, `4 ≤ C`.

    The extremiser `|x|^{−1/2}` lies in `H¹_loc` but not `H¹`, so the infimum `4` is
    approached but never attained. -/
theorem hardy_constant_sharp :
    ∀ C : ℝ, (∀ (ψ : l2R3) (hψ : MemSobolevH1 ψ),
      hardyIntegral ψ ≤ C * gradientNormSq ψ hψ) → 4 ≤ C := by
  intro C hC
  have hIa_pos : 0 < ∫ s, etaFn s ^ 2 := etaFn_sq_integral_pos
  -- For each `n > 0`, apply the hypothesis to `φₙ` and cancel the factor `radialConst·n`.
  have hkey : ∀ n : ℝ, 0 < n →
      (∫ s, etaFn s ^ 2)
        ≤ C * ((∫ s, (deriv etaFn s) ^ 2) / n ^ 2
              - (∫ s, deriv etaFn s * etaFn s) / n + (∫ s, etaFn s ^ 2) / 4) := by
    intro n hn
    have hsm : ContDiff ℝ ∞ (fun y : R3 => (gN n ‖y‖ : ℂ)) := phiN_contDiff hn
    have hsp : HasCompactSupport (fun y : R3 => (gN n ‖y‖ : ℂ)) := phiN_hasCompactSupport hn
    have hmem := memLp_of_smooth_compactSupport (fun y : R3 => (gN n ‖y‖ : ℂ)) hsm hsp
    have hH1 : MemSobolevH1 (hmem.toLp _) :=
      sobolevH2_le_sobolevH1 (smooth_compactSupport_memSobolevH2 _ hsm hsp hmem)
    have happ := hC (hmem.toLp _) hH1
    rw [hardyIntegral_radial hsm hsp,
        gradientNormSq_radial (fun r _ => gN_hasDerivAt (n := n) ‹_›) hsm hsp,
        hardyIntegral_value hn, gradientNormSq_value hn, denom_expand hn.ne'] at happ
    have hKpos : 0 < radialConst * n := mul_pos radialConst_pos hn
    rw [show radialConst * (n * ∫ s, etaFn s ^ 2)
            = (radialConst * n) * (∫ s, etaFn s ^ 2) from by ring,
        show C * (radialConst * (n * ((∫ s, (deriv etaFn s) ^ 2) / n ^ 2
              - (∫ s, deriv etaFn s * etaFn s) / n + (∫ s, etaFn s ^ 2) / 4)))
            = (radialConst * n) * (C * ((∫ s, (deriv etaFn s) ^ 2) / n ^ 2
              - (∫ s, deriv etaFn s * etaFn s) / n + (∫ s, etaFn s ^ 2) / 4)) from by ring] at happ
    exact le_of_mul_le_mul_left happ hKpos
  -- Pass to the limit `n → ∞`: the `1/n²` and `1/n` terms vanish.
  have hb1 : Tendsto (fun n : ℝ => (∫ s, (deriv etaFn s) ^ 2) / n ^ 2) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds (tendsto_pow_atTop (by norm_num))
  have hb2 : Tendsto (fun n : ℝ => (∫ s, deriv etaFn s * etaFn s) / n) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hdenom : Tendsto (fun n : ℝ => (∫ s, (deriv etaFn s) ^ 2) / n ^ 2
        - (∫ s, deriv etaFn s * etaFn s) / n + (∫ s, etaFn s ^ 2) / 4) atTop
        (𝓝 (0 - 0 + (∫ s, etaFn s ^ 2) / 4)) :=
    (hb1.sub hb2).add tendsto_const_nhds
  have hle : (∫ s, etaFn s ^ 2) ≤ C * (0 - 0 + (∫ s, etaFn s ^ 2) / 4) := by
    refine ge_of_tendsto (hdenom.const_mul C) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    exact hkey n hn
  nlinarith [hIa_pos, hle]

end Spectra.QuantumMechanics.Hydrogen

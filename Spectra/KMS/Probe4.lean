import Spectra.KMS.AnalyticElements

open Complex Set Filter Topology MeasureTheory
open Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

-- The pointwise bound. Given z in ball z0 1, R := ‖z0‖ + 1.
example (α : Dynamics A) (a : A) (n : ℕ) (hn : 0 < (n : ℝ)) (z0 : ℂ) (z : ℂ)
    (hz : z ∈ Metric.ball z0 1) (t : ℝ) :
    ‖((2 * (n : ℂ) * (((t : ℂ)) - z)) * Complex.exp (-(n : ℂ) * (((t : ℂ)) - z) ^ 2)) • α.evolve t a‖
      ≤ (2 * (n:ℝ) * Real.exp (2 * (n:ℝ) * (‖z0‖ + 1)^2) * ‖a‖)
          * (|t| + (‖z0‖ + 1)) * Real.exp (-(n / 2 : ℝ) * t ^ 2) := by
  set R := ‖z0‖ + 1 with hR
  have hRpos : 0 ≤ R := by positivity
  -- bounds on z.re, z.im, ‖z‖
  have hzn : ‖z‖ ≤ R := by
    have : ‖z‖ ≤ ‖z0‖ + ‖z - z0‖ := by
      have := norm_add_le z0 (z - z0); simpa using this
    have hd : ‖z - z0‖ < 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
    rw [hR]; linarith
  have hzre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hzn
  have hzim : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hzn
  -- rewrite the norm
  rw [norm_smul, norm_mul, α.norm_evolve, norm_exp]
  -- re computation
  have hre : (-(n : ℂ) * (((t : ℂ)) - z) ^ 2).re = -(n : ℝ) * ((t - z.re)^2 - z.im^2) := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, pow_two]
    ring
  rw [hre]
  -- Factor 1: ‖2n(t-z)‖ ≤ 2n(|t| + R)
  have hf1 : ‖2 * (n : ℂ) * (((t : ℂ)) - z)‖ ≤ 2 * (n:ℝ) * (|t| + R) := by
    rw [norm_mul, norm_mul]
    have hcoeff : ‖(2 : ℂ)‖ * ‖(n : ℂ)‖ = 2 * (n:ℝ) := by
      rw [Complex.norm_natCast]; norm_num
    rw [hcoeff]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖(((t : ℂ)) - z)‖ ≤ ‖(t : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = |t| + ‖z‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |t| + R := by gcongr
  -- Factor 2: exp(-n((t-z.re)^2 - z.im^2)) ≤ exp(2nR^2) * exp(-(n/2)t^2)
  have hf2 : Real.exp (-(n:ℝ) * ((t - z.re)^2 - z.im^2))
      ≤ Real.exp (2 * (n:ℝ) * R^2) * Real.exp (-(n / 2 : ℝ) * t ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- need: -n((t-z.re)^2 - z.im^2) ≤ 2nR^2 - (n/2)t^2
    -- (t - z.re)^2 ≥ t^2/2 - z.re^2 ; z.re^2 ≤ R^2 ; z.im^2 ≤ R^2
    have hkey : (t - z.re)^2 ≥ t^2/2 - z.re^2 := by nlinarith [sq_nonneg (t - 2*z.re)]
    have hre2 : z.re^2 ≤ R^2 := by
      have := abs_le.mp hzre; nlinarith [abs_nonneg z.re, hRpos]
    have him2 : z.im^2 ≤ R^2 := by
      have := abs_le.mp hzim; nlinarith [abs_nonneg z.im, hRpos]
    nlinarith [hn.le]
  -- Combine
  have hexp_nonneg : (0:ℝ) ≤ Real.exp (-(n:ℝ) * ((t - z.re)^2 - z.im^2)) := Real.exp_nonneg _
  have hnorm_nonneg : (0:ℝ) ≤ ‖a‖ := norm_nonneg _
  calc ‖2 * (n : ℂ) * (((t : ℂ)) - z)‖ * Real.exp (-(n:ℝ) * ((t - z.re)^2 - z.im^2)) * ‖a‖
      ≤ (2 * (n:ℝ) * (|t| + R)) * (Real.exp (2 * (n:ℝ) * R^2) * Real.exp (-(n / 2 : ℝ) * t ^ 2)) * ‖a‖ := by
        gcongr
    _ = (2 * (n:ℝ) * Real.exp (2 * (n:ℝ) * R^2) * ‖a‖) * (|t| + R) * Real.exp (-(n / 2 : ℝ) * t ^ 2) := by
        ring

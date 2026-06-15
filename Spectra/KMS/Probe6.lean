import Spectra.KMS.AnalyticElements

open Complex Set Filter Topology MeasureTheory
open Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

-- Continuity of F z in u (for measurability)
example (α : Dynamics A) (a : A) (n : ℕ) (z : ℂ) :
    Continuous (fun u : ℝ => Complex.exp (-(n : ℂ) * (((u : ℂ)) - z) ^ 2) • α.evolve u a) := by
  apply Continuous.smul
  · apply Complex.continuous_exp.comp
    fun_prop
  · exact α.continuous_evolve a

-- Integrability of F z for general z
example (α : Dynamics A) (a : A) (n : ℕ) (hn : 0 < (n : ℝ)) (z : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (-(n : ℂ) * (((u : ℂ)) - z) ^ 2) • α.evolve u a) := by
  have hcont : Continuous (fun u : ℝ => Complex.exp (-(n : ℂ) * (((u : ℂ)) - z) ^ 2) • α.evolve u a) := by
    apply Continuous.smul
    · exact Complex.continuous_exp.comp (by fun_prop)
    · exact α.continuous_evolve a
  -- majorant: exp(n z.im^2) * ‖a‖ * exp(-n (u - z.re)^2)... but simpler: use exp(-(n/2) u^2) bound
  -- ‖F z u‖ = exp(-n((u-z.re)^2 - z.im^2)) * ‖a‖ ≤ exp(n R^2)*exp(n R^2)... use the same idea
  set R := |z.re| with hRdef
  have hb : 0 < (n / 2 : ℝ) := by positivity
  refine Integrable.mono'
    (((integrable_exp_neg_mul_sq hb).const_mul (Real.exp (2 * (n:ℝ) * (|z.re|^2 + |z.im|^2)) * ‖a‖)))
    hcont.aestronglyMeasurable ?_
  filter_upwards with u
  rw [norm_smul, norm_exp]
  have hre : (-(n : ℂ) * (((u : ℂ)) - z) ^ 2).re = -(n : ℝ) * ((u - z.re)^2 - z.im^2) := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, pow_two]
    ring
  rw [hre, α.norm_evolve]
  -- exp(-n((u-z.re)^2 - z.im^2)) * ‖a‖ ≤ exp(C) * exp(-(n/2)u^2) * ‖a‖
  have hkey : (u - z.re)^2 ≥ u^2/2 - z.re^2 := by nlinarith [sq_nonneg (u - 2*z.re)]
  have hbound : -(n:ℝ) * ((u - z.re)^2 - z.im^2) ≤ 2 * (n:ℝ) * (|z.re|^2 + |z.im|^2) + (-(n/2:ℝ) * u^2) := by
    have h1 : z.re^2 = |z.re|^2 := (sq_abs z.re).symm
    have h2 : z.im^2 ≤ |z.im|^2 := by rw [sq_abs]
    nlinarith [hn.le, sq_nonneg z.re, sq_nonneg z.im]
  calc Real.exp (-(n:ℝ) * ((u - z.re)^2 - z.im^2)) * ‖a‖
      ≤ Real.exp (2 * (n:ℝ) * (|z.re|^2 + |z.im|^2) + (-(n/2:ℝ) * u^2)) * ‖a‖ := by
        gcongr
        exact Real.exp_le_exp.mpr hbound
    _ = Real.exp (2 * (n:ℝ) * (|z.re|^2 + |z.im|^2)) * ‖a‖ * Real.exp (-(n/2:ℝ) * u^2) := by
        rw [Real.exp_add]; ring

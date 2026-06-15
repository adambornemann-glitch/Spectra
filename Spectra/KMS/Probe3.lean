import Spectra.KMS.AnalyticElements

open Complex Set Filter Topology MeasureTheory
open Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

-- norm of the derivative value
example (α : Dynamics A) (a : A) (n : ℕ) (z : ℂ) (t : ℝ) :
    ‖((2 * (n : ℂ) * (((t : ℂ)) - z)) * Complex.exp (-(n : ℂ) * (((t : ℂ)) - z) ^ 2)) • α.evolve t a‖
      = ‖2 * (n : ℂ) * (((t : ℂ)) - z)‖ * Real.exp (-(n : ℝ) * ((t - z.re)^2 - z.im^2)) * ‖a‖ := by
  rw [norm_smul, norm_mul, α.norm_evolve]
  congr 1
  rw [norm_exp]
  congr 1
  -- re of -(n) * ((t) - z)^2
  have : (-(n : ℂ) * (((t : ℂ)) - z) ^ 2).re = -(n : ℝ) * ((t - z.re)^2 - z.im^2) := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, pow_two]
    ring
  rw [this]

-- the integrability of the majorant: C * (|u| + R) * exp(-(n/2) u^2)
example (n : ℕ) (hn : 0 < (n : ℝ)) (C R : ℝ) :
    Integrable (fun u : ℝ => C * (|u| + R) * Real.exp (-(n / 2 : ℝ) * u ^ 2)) := by
  have hb : 0 < (n / 2 : ℝ) := by positivity
  have h1 : Integrable (fun u : ℝ => |u| * Real.exp (-(n / 2 : ℝ) * u ^ 2)) := by
    have hmul := (integrable_mul_exp_neg_mul_sq hb)
    rw [← integrable_norm_iff hmul.aestronglyMeasurable] at hmul
    refine hmul.congr ?_
    filter_upwards with u
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (Real.exp _),
      abs_of_nonneg (Real.exp_nonneg _)]
  have h2 : Integrable (fun u : ℝ => R * Real.exp (-(n / 2 : ℝ) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul R
  have h3 : Integrable (fun u : ℝ => |u| * Real.exp (-(n / 2 : ℝ) * u ^ 2)
      + R * Real.exp (-(n / 2 : ℝ) * u ^ 2)) := h1.add h2
  have h4 := h3.const_mul C
  refine h4.congr ?_
  filter_upwards with u
  ring

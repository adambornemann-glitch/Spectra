import Spectra.KMS.AnalyticElements

open Complex Set Filter Topology MeasureTheory
open ComplexConjugate

namespace Spectra.KMS

variable {A : Type*} [CStarAlgebra A]

/-- **Gaussian approximate identity.** The Gaussian-smoothed elements converge to `a`:
`a_n = √(n/π) ∫ e^{-n t²} α_t(a) dt → a`. This is the Bratteli–Robinson approximation showing
that, together with analyticity of each `a_n`, the analytic elements are dense. -/
theorem Dynamics.gaussianSmooth_tendsto (α : Dynamics A) (a : A) :
    Filter.Tendsto (fun n : ℕ => α.gaussianSmooth a n) Filter.atTop (nhds a) := by
  -- Reduce to the norm of the difference tending to 0.
  rw [← tendsto_sub_nhds_zero_iff]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  -- The rescaled scalar integral, whose limit drives everything.
  have hresc : Filter.Tendsto
      (fun n : ℕ => ∫ s : ℝ, Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖)
      Filter.atTop (nhds 0) := by
    -- pointwise limit
    have hptw : ∀ s : ℝ, Filter.Tendsto
        (fun n : ℕ => Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖)
        Filter.atTop (nhds 0) := by
      intro s
      have htz : Filter.Tendsto (fun n : ℕ => s / Real.sqrt (n : ℝ)) Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        have h2 := h1.const_mul s
        simp only [mul_zero] at h2
        simpa only [div_eq_mul_inv] using h2
      have hcont : Filter.Tendsto (fun n : ℕ => α.evolve (s / Real.sqrt (n : ℝ)) a)
          Filter.atTop (nhds a) := by
        have h0 := ((α.continuous_evolve a).tendsto 0).comp htz
        simpa [Function.comp_def, α.evolve_zero] using h0
      have hnorm : Filter.Tendsto (fun n : ℕ => ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖)
          Filter.atTop (nhds 0) := by simpa using (hcont.sub_const a).norm
      simpa using hnorm.const_mul (Real.exp (-s ^ 2))
    -- bound
    set bnd : ℝ → ℝ := fun s => Real.exp (-1 * s ^ 2) * (2 * ‖a‖) with hbnd
    have hbnd_int : Integrable bnd :=
      (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)).mul_const _
    have hlim : (∫ _s : ℝ, (0 : ℝ)) = 0 := by simp
    rw [← hlim]
    apply tendsto_integral_filter_of_dominated_convergence bnd
    · filter_upwards with n
      apply Continuous.aestronglyMeasurable
      apply Continuous.mul (by fun_prop)
      apply Continuous.norm
      exact (α.continuous_evolve a).comp (by fun_prop) |>.sub continuous_const
    · filter_upwards with n
      filter_upwards with s
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simp only [hbnd]
      have hexp : Real.exp (-1 * s ^ 2) = Real.exp (-s ^ 2) := by norm_num
      rw [hexp]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      calc ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖
          ≤ ‖α.evolve (s / Real.sqrt (n : ℝ)) a‖ + ‖a‖ := norm_sub_le _ _
        _ = 2 * ‖a‖ := by rw [α.norm_evolve]; ring
    · exact hbnd_int
    · filter_upwards with s
      exact hptw s
  -- Squeeze `‖a_n - a‖` by `(1/√π) * (rescaled integral)`, eventually for `n ≥ 1`.
  have hsq : Filter.Tendsto
      (fun n : ℕ => (1 / Real.sqrt Real.pi)
        * ∫ s : ℝ, Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖)
      Filter.atTop (nhds 0) := by
    have := hresc.const_mul (1 / Real.sqrt Real.pi)
    simpa using this
  refine squeeze_zero_norm' ?_ ?_
  · -- ‖ ‖a_n - a‖ ‖ ≤ (1/√π) * rescaled,  eventually for n ≥ 1
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    -- normalization representation of `a`
    have hrep : a = Real.sqrt ((n : ℝ) / Real.pi)
        • ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) • a := by
      rw [integral_smul_const, integral_gaussian, smul_smul, ← Real.sqrt_mul (by positivity),
        div_mul_div_comm, mul_comm (n : ℝ) Real.pi, div_self (by positivity), Real.sqrt_one,
        one_smul]
    -- difference formula
    have hdiff : α.gaussianSmooth a n - a
        = Real.sqrt ((n : ℝ) / Real.pi)
            • ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) • (α.evolve t a - a) := by
      unfold Dynamics.gaussianSmooth
      have hsub : (fun t : ℝ => Real.exp (-(n : ℝ) * t ^ 2) • (α.evolve t a - a))
          = (fun t : ℝ => Real.exp (-(n : ℝ) * t ^ 2) • α.evolve t a
              - Real.exp (-(n : ℝ) * t ^ 2) • a) := by
        ext t; rw [smul_sub]
      rw [hsub, integral_sub (α.integrable_gaussian_smul a hnpos)
        ((integrable_exp_neg_mul_sq hnpos).smul_const a), smul_sub, ← hrep]
    -- norm bound (scalar integral)
    have hnb : ‖α.gaussianSmooth a n - a‖
        ≤ Real.sqrt ((n : ℝ) / Real.pi)
            * ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) * ‖α.evolve t a - a‖ := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
      congr 1; ext t
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    -- rescaling
    have hres : Real.sqrt ((n : ℝ) / Real.pi)
          * ∫ t : ℝ, Real.exp (-(n : ℝ) * t ^ 2) * ‖α.evolve t a - a‖
        = (1 / Real.sqrt Real.pi)
            * ∫ s : ℝ, Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖ := by
      set g : ℝ → ℝ := fun s => Real.exp (-s ^ 2) * ‖α.evolve (s / Real.sqrt (n : ℝ)) a - a‖
        with hg
      have hcomp : (fun t : ℝ => Real.exp (-(n : ℝ) * t ^ 2) * ‖α.evolve t a - a‖)
          = (fun t : ℝ => g (Real.sqrt (n : ℝ) * t)) := by
        ext t
        simp only [hg]
        have hsqn : Real.sqrt (n : ℝ) * t / Real.sqrt (n : ℝ) = t := by
          rw [mul_comm, mul_div_assoc, div_self (by positivity : Real.sqrt (n : ℝ) ≠ 0), mul_one]
        rw [hsqn]
        congr 2
        rw [mul_pow, Real.sq_sqrt hnpos.le]; ring
      rw [hcomp, MeasureTheory.Measure.integral_comp_mul_left g (Real.sqrt (n : ℝ)), smul_eq_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹), ← mul_assoc,
        Real.sqrt_div hnpos.le Real.pi, div_mul_eq_mul_div,
        mul_inv_cancel₀ (by positivity : Real.sqrt (n : ℝ) ≠ 0)]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), ← hres]
    exact hnb
  · exact hsq

/-- **Density of the analytic elements.** Conditional on each Gaussian-smoothed element being
analytic (Brick A), the analytic elements are dense in `A`: every `a` is the limit of the analytic
sequence `a_n`. -/
theorem Dynamics.analyticElements_dense (α : Dynamics A)
    (hAn : ∀ a (n : ℕ), 0 < (n : ℝ) → α.IsAnalyticElement (α.gaussianSmooth a n)) :
    Dense (α.analyticElements) := by
  intro a
  refine mem_closure_of_tendsto (α.gaussianSmooth_tendsto a) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  exact (α.mem_analyticElements).mpr (hAn a n hnpos)

end Spectra.KMS

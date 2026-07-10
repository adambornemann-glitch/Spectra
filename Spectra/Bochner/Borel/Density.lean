/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/

import Spectra.Bochner.Borel.Fubini
import Spectra.Kernel.Lorentzian
/-!
# The Poisson Density of a Diagonal Resolvent

For a one-parameter unitary group `U_grp` with generator resolvent `R(z)`, the diagonal matrix
element `⟪ξ, R(λ+iε)ξ⟫` has non-negative imaginary part; normalizing it gives the Poisson
density `borelDensity U_grp ξ hε λ := (1/π)·Im⟪ξ, R(λ+iε)ξ⟫`. This file establishes its
core analytic properties and its Fourier-inversion link back to the group, feeding
`Bochner/Borel/CDF.lean`.

## Main definitions

* `borelDensity`: the Poisson density `(1/π)·Im⟪ξ, R(λ+iε)ξ⟫`.

## Main statements

* `borelDensity_nonneg`, `borelDensity_continuous`: sign and continuity in `λ`.
* `borelDensity_le`: the uniform bound `borelDensity ε λ ≤ ‖ξ‖²/(πε)`.
* `borelDensity_mass`: `borelDensity` is integrable with total mass `‖ξ‖²`.
* `borelDensity_fourier`: Fourier inversion,
  `∫ e^{iλt}·borelDensity ε = e^{-ε|t|}·⟨ξ,U(t)ξ⟩`.

## Implementation notes

`borelDensity` need not be integrable a priori, so the mass and Fourier-inversion identities
are both established by regularizing with `e^{-δ|λ|}` and letting `δ → 0⁺`: the regularized
integrals are the honest Poisson-kernel integrals of `⟨ξ,U(t)ξ⟩` (via
`fourier_poisson_tendsto` and `fourier_regularized_value`), which are controlled directly.
`borelDensity_mass` passes to
the `δ → 0` limit along the countable sequence `δₙ = 1/(n+1)` rather than the full filter,
since Beppo Levi's monotone convergence theorem needs a sequence; `borelDensity_le` supplies
the dominating function that makes each regularized integral finite in the first place.

## References

* Reed, Simon, *Methods of Modern Mathematical Physics I*, Section VII (Herglotz/Poisson
  representation of the resolvent).

## Tags

Poisson kernel, resolvent, Herglotz representation, one-parameter unitary group
-/
open Complex MeasureTheory Filter Topology
open Spectra.Resolvent
open Spectra.Fourier
open Spectra.Kernels
open Spectra.OneParameterUnitaryGroup
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Borel

/-- Poisson density of the diagonal resolvent:
`pε(λ) := (1/π)·Im⟪ξ, R(λ+iε)ξ⟫`. -/
noncomputable def borelDensity
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (lambda : ℝ) : ℝ :=
  let z : ℂ := ⟨lambda, ε⟩
  (1 / Real.pi) *
    (⟪ξ, resolvent z hε.ne'
        (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp)
        (range_minus_i_eq_top U_grp) ξ⟫_ℂ).im

/-- `fourier_identity` recast: the Fourier integral equals `2π · borelDensity`. -/
lemma fourier_integral_eq_density
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (lambda : ℝ) :
    (∫ t : ℝ, cexp (-(I * (lambda : ℂ) * (t : ℂ))) *
              cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ)
      = ((2 * Real.pi * borelDensity U_grp ξ hε lambda : ℝ) : ℂ) := by
  rw [← fourier_identity U_grp ξ hε lambda]
  unfold borelDensity
  push_cast
  field_simp

/-- Per-δ identity: `2π · ∫_λ borelDensity·e^{-δ|λ|}` equals the Poisson-form integral
    (as complex numbers). -/
lemma regularized_density_value
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ((2 * Real.pi * (∫ lambda : ℝ,
        borelDensity U_grp ξ hε lambda * Real.exp (-(δ * |lambda|))) : ℝ) : ℂ)
      = ∫ t : ℝ, cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ
                * ((2 * δ / (t ^ 2 + δ ^ 2) : ℝ) : ℂ) := by
  rw [← fubini_regularized U_grp ξ hε hδ]
  have hstep :
      (∫ lambda : ℝ, (∫ t : ℝ, cexp (-(I * (lambda : ℂ) * (t : ℂ))) *
                              cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ)
                   * (Real.exp (-(δ * |lambda|)) : ℂ))
      = ∫ lambda : ℝ, ((2 * Real.pi *
                    (borelDensity U_grp ξ hε lambda * Real.exp
                  (-(δ * |lambda|))) : ℝ) : ℂ) := by
    congr 1; funext lambda
    rw [fourier_integral_eq_density U_grp ξ hε lambda]
    push_cast; ring
  rw [hstep, integral_complex_ofReal, ← integral_const_mul]

/-- The Poisson density is nonnegative:
immediate from `Im⟪ξ, R(z)ξ⟫ = z.im·‖R(z)ξ‖²`. -/
lemma borelDensity_nonneg
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (lambda : ℝ) :
    0 ≤ borelDensity U_grp ξ hε lambda := by
  unfold borelDensity
  refine mul_nonneg (by positivity) ?_
  rw [im_resolvent_diag (generator_isFormalAdjoint U_grp)
        (range_plus_i_eq_top U_grp)
        (range_minus_i_eq_top U_grp)
        (⟨lambda, ε⟩ : ℂ) hε.ne' ξ]
  exact mul_nonneg hε.le (sq_nonneg _)

/-- The Poisson integral centered at `t` tends to
`2π·cexp(-(ε|t|))·⟨ξ,U(t)ξ⟩` as `δ → 0⁺`. -/
lemma fourier_poisson_tendsto
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto (fun δ : ℝ => ∫ s : ℝ, cexp (-(↑ε * ↑|s|)) * ⟪ξ, U_grp.U s ξ⟫_ℂ
                * ((2 * δ / ((t - s) ^ 2 + δ ^ 2) : ℝ) : ℂ))
      (𝓝[>] 0)
      (𝓝 (((2 * Real.pi : ℝ) : ℂ) *
        (cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ))) := by
  set g : ℝ → ℂ := fun s => cexp (-(↑ε * ↑|s|)) * ⟪ξ, U_grp.U s ξ⟫_ℂ with hg_def
  have hg_cont : Continuous g := by
    rw [hg_def]
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      (Continuous.inner continuous_const (U_grp.strong_continuous ξ))
  have he_int : Integrable (fun s : ℝ => Real.exp (-(ε * |s|))) volume :=
    integrable_exp_neg_abs_mul hε
  have hg_int : Integrable g volume := by
    refine (he_int.const_mul (‖ξ‖ ^ 2)).mono' hg_cont.aestronglyMeasurable ?_
    filter_upwards with s
    rw [hg_def]
    simp only [norm_mul, Complex.norm_exp]
    have h_re : (-(↑ε * ↑|s|) : ℂ).re = -(ε * |s|) := by simp [Complex.mul_re]
    rw [h_re]
    have h_inner : ‖⟪ξ, U_grp.U s ξ⟫_ℂ‖ ≤ ‖ξ‖ ^ 2 :=
      calc ‖⟪ξ, U_grp.U s ξ⟫_ℂ‖
          ≤ ‖ξ‖ * ‖U_grp.U s ξ‖ := norm_inner_le_norm _ _
        _ = ‖ξ‖ * ‖ξ‖ := by rw [norm_preserving U_grp s ξ]
        _ = ‖ξ‖ ^ 2 := by ring
    calc Real.exp (-(ε * |s|)) * ‖⟪ξ, U_grp.U s ξ⟫_ℂ‖
        ≤ Real.exp (-(ε * |s|)) * ‖ξ‖ ^ 2 := by gcongr
      _ = ‖ξ‖ ^ 2 * Real.exp (-(ε * |s|)) := by ring
  -- lorentzian_approx_delta at t, scaled by 2π.
  have h_lor := lorentzian_approx_delta g hg_cont hg_int t
  have h_scaled := h_lor.const_smul (2 * Real.pi : ℝ)
  have h_limit_eq : (2 * Real.pi : ℝ) • (g t)
      = ((2 * Real.pi : ℝ) : ℂ) * (cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ) := by
    simp only [hg_def, Complex.real_smul]
  rw [h_limit_eq] at h_scaled
  refine h_scaled.congr (fun δ => ?_)
  rw [smul_smul, show (2 * Real.pi * (1 / Real.pi) : ℝ) = 2 by field_simp, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with s
  rw [smul_smul, Complex.real_smul]
  push_cast; ring

/-- The Poisson-form integral tends to `2π‖ξ‖²` as `δ → 0⁺` — the `t = 0` case of
`fourier_poisson_tendsto`, since `(0 - s)² = s²` and
`cexp(-ε|0|)·⟨ξ,U(0)ξ⟩ = ‖ξ‖²`. -/
lemma poisson_integral_tendsto
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ, cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ
                * ((2 * δ / (t ^ 2 + δ ^ 2) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((2 * Real.pi * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
  have h := fourier_poisson_tendsto U_grp ξ hε 0
  have hlim :
      cexp (-(↑ε * ↑|(0 : ℝ)|)) * ⟪ξ, U_grp.U (0 : ℝ) ξ⟫_ℂ
        = (‖ξ‖ ^ 2 : ℂ) := by
    simp only [abs_zero, mul_zero, neg_zero, Complex.ofReal_zero, Complex.exp_zero, one_mul]
    rw [U_grp.identity, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K]
    ring_nf; rfl
  have hkernel : (fun δ : ℝ => ∫ s : ℝ, cexp (-(↑ε * ↑|s|)) * ⟪ξ, U_grp.U s ξ⟫_ℂ
                    * ((2 * δ / ((0 - s) ^ 2 + δ ^ 2) : ℝ) : ℂ))
      = (fun δ : ℝ => ∫ t : ℝ, cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ
                    * ((2 * δ / (t ^ 2 + δ ^ 2) : ℝ) : ℂ)) := by
    funext δ; congr 1; funext s; rw [zero_sub, neg_sq]
  rw [hlim, hkernel] at h
  rwa [show ((2 * Real.pi : ℝ) : ℂ) * (‖ξ‖ ^ 2 : ℂ)
      = ((2 * Real.pi * ‖ξ‖ ^ 2 : ℝ) : ℂ) from by push_cast; ring] at h

/-- The Poisson density is continuous in `λ`,
by continuity of the resolvent on the strip. -/
lemma borelDensity_continuous
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) {ε : ℝ} (hε : 0 < ε) :
    Continuous (borelDensity U_grp ξ hε) := by
  unfold borelDensity
  refine continuous_const.mul (Complex.continuous_im.comp ?_)
  exact continuous_const.inner
    (resolvent_continuous_at_height
      (generator_isFormalAdjoint U_grp)
      (range_plus_i_eq_top U_grp)
      (range_minus_i_eq_top U_grp) hε ξ)

/-- `∫_λ borelDensity·e^{-δ|λ|} → ‖ξ‖²` as `δ → 0⁺`. -/
lemma regularized_mass_tendsto
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun δ : ℝ => ∫ lambda : ℝ,
        borelDensity U_grp ξ hε lambda * Real.exp (-(δ * |lambda|)))
      (𝓝[>] 0) (𝓝 (‖ξ‖ ^ 2)) := by
  have hpoisson := poisson_integral_tendsto U_grp ξ hε
  have h_eq : (fun δ : ℝ => ((2 * Real.pi * (∫ lambda : ℝ,
                borelDensity U_grp ξ hε lambda * Real.exp (-(δ * |lambda|))) : ℝ) : ℂ))
              =ᶠ[𝓝[>] 0]
              (fun δ : ℝ => ∫ t : ℝ, cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ
                * ((2 * δ / (t ^ 2 + δ ^ 2) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact regularized_density_value U_grp ξ hε (Set.mem_Ioi.mp hδ)
  have hcast := hpoisson.congr' h_eq.symm
  have hre : Tendsto (fun δ : ℝ => 2 * Real.pi * (∫ lambda : ℝ,
                borelDensity U_grp ξ hε lambda * Real.exp (-(δ * |lambda|))))
      (𝓝[>] 0) (𝓝 (2 * Real.pi * ‖ξ‖ ^ 2)) := by
    have h := (Complex.continuous_re.tendsto _).comp hcast
    simpa only [Function.comp_def, Complex.ofReal_re] using h
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hfinal := hre.const_mul (1 / (2 * Real.pi))
  rw [show (1 / (2 * Real.pi)) * (2 * Real.pi * ‖ξ‖ ^ 2) = ‖ξ‖ ^ 2 by
        rw [one_div, inv_mul_cancel_left₀ h2pi]] at hfinal
  refine hfinal.congr (fun δ => ?_)
  rw [← mul_assoc, one_div_mul_cancel h2pi, one_mul]

/-- Uniform bound `borelDensity ε λ ≤ ‖ξ‖²/(πε)`. -/
lemma borelDensity_le
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (lambda : ℝ) :
    borelDensity U_grp ξ hε lambda ≤ ‖ξ‖ ^ 2 / (Real.pi * ε) := by
  set Rξ := resolvent (⟨lambda, ε⟩ : ℂ) hε.ne' (generator_isFormalAdjoint U_grp)
    (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ with hRξ
  have him : (⟪ξ, Rξ⟫_ℂ).im = ε * ‖Rξ‖ ^ 2 := by
    rw [hRξ, im_resolvent_diag (generator_isFormalAdjoint U_grp)
    (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) (⟨lambda, ε⟩ : ℂ) hε.ne' ξ]
  have hval : borelDensity U_grp ξ hε lambda = ε / Real.pi * ‖Rξ‖ ^ 2 := by
    unfold borelDensity
    simp only [← hRξ, him]; ring
  have hcs : ε * ‖Rξ‖ ^ 2 ≤ ‖ξ‖ * ‖Rξ‖ := by
    have h1 : (⟪ξ, Rξ⟫_ℂ).im ≤ ‖⟪ξ, Rξ⟫_ℂ‖ := im_le_norm _
    rw [← him]; exact h1.trans (norm_inner_le_norm ξ Rξ)
  have key : ε * ‖Rξ‖ ≤ ‖ξ‖ := by
    rcases eq_or_lt_of_le (norm_nonneg Rξ) with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg ξ
    · have h2 : (ε * ‖Rξ‖) * ‖Rξ‖ ≤ ‖ξ‖ * ‖Rξ‖ := by
        rw [mul_assoc, ← pow_two]; exact hcs
      exact le_of_mul_le_mul_right h2 hpos
  rw [hval, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : (ε * ‖Rξ‖) * (ε * ‖Rξ‖) ≤ ‖ξ‖ * ‖ξ‖ :=
    mul_le_mul key key (by positivity) (norm_nonneg ξ)
  nlinarith [hsq, Real.pi_pos]

/-- `borelDensity ε` is integrable with total mass `‖ξ‖²`. -/
theorem borelDensity_mass
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (borelDensity U_grp ξ hε) volume ∧
      ∫ lambda : ℝ, borelDensity U_grp ξ hε lambda = ‖ξ‖ ^ 2 := by
  set D : ℝ → ℝ := borelDensity U_grp ξ hε with hD_def
  have hD_nonneg : ∀ lambda, 0 ≤ D lambda :=
    fun lambda => borelDensity_nonneg U_grp ξ hε lambda
  have hD_cont : Continuous D := borelDensity_continuous U_grp ξ hε
  have hexp_int : ∀ {c : ℝ}, 0 < c →
      Integrable (fun lambda : ℝ => Real.exp (-(c * |lambda|))) volume :=
    fun hc => integrable_exp_neg_abs_mul hc
  -- δₙ = 1/(n+1) ↓ 0 within (0, ∞).
  set dseq : ℕ → ℝ := fun n => 1 / (n + 1) with hdseq_def
  have hdseq_pos : ∀ n, 0 < dseq n := fun n => by positivity
  have hdseq_anti : Antitone dseq := by
    intro m n hmn
    simp only [hdseq_def]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hdseq_tendsto : Tendsto dseq atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · rw [hdseq_def]; exact tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Filter.Eventually.of_forall hdseq_pos
  -- fₙ λ = D λ · e^{-δₙ|λ|}.
  set f : ℕ → ℝ → ℝ := fun n lambda => D lambda * Real.exp (-(dseq n * |lambda|))
    with hf_def
  have hf_nonneg : ∀ n lambda, 0 ≤ f n lambda := fun n lambda =>
    mul_nonneg (hD_nonneg lambda) (Real.exp_nonneg _)
  have hf_cont : ∀ n, Continuous (f n) := by
    intro n
    simp only [hf_def]
    exact hD_cont.mul (Real.continuous_exp.comp ((continuous_const.mul continuous_abs).neg))
  have hf_int : ∀ n, Integrable (f n) volume := by
    intro n
    refine ((hexp_int (hdseq_pos n)).const_mul (‖ξ‖ ^ 2 / (Real.pi * ε))).mono'
      (hf_cont n).aestronglyMeasurable ?_
    filter_upwards with lambda
    simp only [hf_def, norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (hD_nonneg lambda), abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_right (borelDensity_le U_grp ξ hε lambda) (Real.exp_nonneg _)
  have hf_mono : ∀ lambda, Monotone (fun n => f n lambda) := by
    intro lambda m n hmn
    simp only [hf_def]
    refine mul_le_mul_of_nonneg_left ?_ (hD_nonneg lambda)
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    exact mul_le_mul_of_nonneg_right (hdseq_anti hmn) (abs_nonneg lambda)
  have hf_tendsto : ∀ lambda, Tendsto (fun n => f n lambda) atTop (𝓝 (D lambda)) := by
    intro lambda
    simp only [hf_def]
    have hd0 : Tendsto dseq atTop (𝓝 0) := hdseq_tendsto.mono_right nhdsWithin_le_nhds
    have h1 : Tendsto (fun n => Real.exp (-(dseq n * |lambda|))) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n => -(dseq n * |lambda|)) atTop (𝓝 0) := by
        simpa using (hd0.mul_const |lambda|).neg
      simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h2
    simpa using h1.const_mul (D lambda)
  -- Beppo Levi in ℝ≥0∞.
  have hmono' : ∀ᵐ lambda ∂volume, Monotone (fun n => ENNReal.ofReal (f n lambda)) := by
    refine Filter.Eventually.of_forall fun lambda => ?_
    intro m n hmn
    exact ENNReal.ofReal_le_ofReal (hf_mono lambda hmn)
  have htend' : ∀ᵐ lambda ∂volume,
      Tendsto (fun n => ENNReal.ofReal (f n lambda)) atTop (𝓝 (ENNReal.ofReal (D lambda))) := by
    refine Filter.Eventually.of_forall fun lambda => ?_
    exact (ENNReal.continuous_ofReal.tendsto _).comp (hf_tendsto lambda)
  have h_mct := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ((hf_cont n).measurable.ennreal_ofReal).aemeasurable) hmono' htend'
  -- ∫ fₙ → ‖ξ‖² along the sequence, lifted through ofReal and the lintegral identity.
  have h_int_tendsto :
      Tendsto (fun n => ∫ lambda, f n lambda ∂volume) atTop (𝓝 (‖ξ‖ ^ 2)) := by
    refine ((regularized_mass_tendsto U_grp ξ hε).comp hdseq_tendsto).congr (fun n => ?_)
    simp only [Function.comp_apply, hf_def, hD_def]
  have h_lim : Tendsto (fun n => ∫⁻ lambda, ENNReal.ofReal (f n lambda) ∂volume) atTop
      (𝓝 (ENNReal.ofReal (‖ξ‖ ^ 2))) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp h_int_tendsto
    refine h.congr (fun n => ?_)
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hf_int n)
      (Filter.Eventually.of_forall (hf_nonneg n))
  have h_mass :
      ∫⁻ lambda, ENNReal.ofReal (D lambda) ∂volume = ENNReal.ofReal (‖ξ‖ ^ 2) :=
    tendsto_nhds_unique h_mct h_lim
  -- Integrability and value.
  have hD_int : Integrable D volume := by
    refine ⟨hD_cont.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hD_nonneg), h_mass]
    exact ENNReal.ofReal_lt_top
  refine ⟨hD_int, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hD_nonneg)
    hD_cont.aestronglyMeasurable, h_mass, ENNReal.toReal_ofReal (by positivity)]

/-- Per-δ phase identity: `2π·∫_λ e^{iλt} borelDensity·e^{-δ|λ|}` equals the Poisson
    integral centered at `t`. -/
lemma fourier_regularized_value
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ((2 * Real.pi : ℝ) : ℂ) * (∫ lambda : ℝ, cexp (I * ↑lambda * ↑t) *
        (borelDensity U_grp ξ hε lambda : ℂ) * (Real.exp (-(δ * |lambda|)) : ℂ))
      = ∫ s : ℝ, cexp (-(↑ε * ↑|s|)) * ⟪ξ, U_grp.U s ξ⟫_ℂ
                * ((2 * δ / ((t - s) ^ 2 + δ ^ 2) : ℝ) : ℂ) := by
  let F : ℝ → ℝ → ℂ := fun lambda s =>
    (cexp (I * ↑lambda * ↑t) * (Real.exp (-(δ * |lambda|)) : ℂ)) *
    (cexp (-(I * ↑lambda * ↑s)) * cexp (-(↑ε * ↑|s|)) * ⟪ξ, U_grp.U s ξ⟫_ℂ)
  have hδ_int : Integrable (fun lambda : ℝ => Real.exp (-(δ * |lambda|))) volume :=
    integrable_exp_neg_abs_mul hδ
  have hε_int : Integrable (fun s : ℝ => Real.exp (-(ε * |s|))) volume :=
    integrable_exp_neg_abs_mul hε
  have hF_int : Integrable (Function.uncurry F) (volume.prod volume) := by
    have h_meas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
      apply Continuous.aestronglyMeasurable
      change Continuous (fun p : ℝ × ℝ =>
        (cexp (I * ↑p.1 * ↑t) * (Real.exp (-(δ * |p.1|)) : ℂ)) *
        (cexp (-(I * ↑p.1 * ↑p.2)) * cexp (-(↑ε * ↑|p.2|)) * ⟪ξ, U_grp.U p.2 ξ⟫_ℂ))
      apply Continuous.mul
      · apply Continuous.mul
        · exact Complex.continuous_exp.comp (by fun_prop)
        · exact Complex.continuous_ofReal.comp (by fun_prop)
      · apply Continuous.mul
        · apply Continuous.mul
          · exact Complex.continuous_exp.comp (by fun_prop)
          · exact Complex.continuous_exp.comp (by fun_prop)
        · exact (Continuous.inner continuous_const
            (U_grp.strong_continuous ξ)).comp continuous_snd
    have h_dom : Integrable
        (fun p : ℝ × ℝ => ‖ξ‖ ^ 2 * (Real.exp (-(δ * |p.1|)) * Real.exp (-(ε * |p.2|))))
        (volume.prod volume) :=
      (hδ_int.mul_prod hε_int).const_mul _
    refine h_dom.mono' h_meas ?_
    filter_upwards with p
    change ‖(cexp (I * ↑p.1 * ↑t) * (Real.exp (-(δ * |p.1|)) : ℂ)) *
          (cexp (-(I * ↑p.1 * ↑p.2)) * cexp (-(↑ε * ↑|p.2|)) *
            ⟪ξ, U_grp.U p.2 ξ⟫_ℂ)‖ ≤
          ‖ξ‖ ^ 2 * (Real.exp (-(δ * |p.1|)) * Real.exp (-(ε * |p.2|)))
    simp only [norm_mul, Complex.norm_exp, Complex.norm_real]
    have h0 : (I * ↑p.1 * ↑t).re = 0 := by simp [Complex.mul_re]
    have h1 : (-(I * ↑p.1 * ↑p.2)).re = 0 := by simp [Complex.mul_re]
    have h2 : (-(↑ε * ↑|p.2|) : ℂ).re = -(ε * |p.2|) := by simp [Complex.mul_re]
    rw [h0, h1, h2]
    simp only [Real.exp_zero, one_mul, Real.abs_exp, Real.norm_eq_abs]
    have h_inner : ‖⟪ξ, U_grp.U p.2 ξ⟫_ℂ‖ ≤ ‖ξ‖ ^ 2 := by
      calc ‖⟪ξ, U_grp.U p.2 ξ⟫_ℂ‖
          ≤ ‖ξ‖ * ‖U_grp.U p.2 ξ‖ := norm_inner_le_norm _ _
        _ = ‖ξ‖ * ‖ξ‖ := by rw [norm_preserving U_grp p.2 ξ]
        _ = ‖ξ‖ ^ 2 := by ring
    nlinarith [mul_nonneg (mul_pos (Real.exp_pos (-(δ * |p.1|)))
        (Real.exp_pos (-(ε * |p.2|)))).le (sub_nonneg.mpr h_inner),
      Real.exp_pos (-(δ * |p.1|)), Real.exp_pos (-(ε * |p.2|)),
      norm_nonneg ⟪ξ, U_grp.U p.2 ξ⟫_ℂ]
  -- Move 2π in, expose the inner s-integral via fourier_integral_eq_density, swap.
  rw [← integral_const_mul]
  have hstep : (fun lambda : ℝ => ((2 * Real.pi : ℝ) : ℂ) *
        (cexp (I * ↑lambda * ↑t) * (borelDensity U_grp ξ hε lambda : ℂ) *
          (Real.exp (-(δ * |lambda|)) : ℂ)))
      = (fun lambda : ℝ => ∫ s : ℝ, F lambda s) := by
    funext lambda
    have hpull : (∫ s : ℝ, F lambda s)
        = (cexp (I * ↑lambda * ↑t) * (Real.exp (-(δ * |lambda|)) : ℂ)) *
          (∫ s : ℝ, cexp (-(I * ↑lambda * ↑s)) * cexp (-(↑ε * ↑|s|)) *
            ⟪ξ, U_grp.U s ξ⟫_ℂ) := by
      simp only [F]; rw [integral_const_mul]
    rw [hpull, fourier_integral_eq_density U_grp ξ hε lambda]
    push_cast; ring
  rw [hstep, integral_integral_swap (f := F) hF_int]
  congr 1; funext s
  have hreorder : (fun lambda : ℝ => F lambda s)
      = (fun lambda : ℝ => (cexp (-(↑ε * ↑|s|)) * ⟪ξ, U_grp.U s ξ⟫_ℂ) *
          (cexp (-(I * ↑lambda * ↑(s - t))) * (Real.exp (-(δ * |lambda|)) : ℂ))) := by
    funext lambda
    simp only [F]
    have hexp : cexp (I * ↑lambda * ↑t) * cexp (-(I * ↑lambda * ↑s))
        = cexp (-(I * ↑lambda * ↑(s - t))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [show (cexp (I * ↑lambda * ↑t) * (Real.exp (-(δ * |lambda|)) : ℂ)) *
          (cexp (-(I * ↑lambda * ↑s)) * cexp (-(↑ε * ↑|s|)) * ⟪ξ, U_grp.U s ξ⟫_ℂ)
          = (cexp (I * ↑lambda * ↑t) * cexp (-(I * ↑lambda * ↑s))) *
            ((Real.exp (-(δ * |lambda|)) : ℂ) * cexp (-(↑ε * ↑|s|)) *
              ⟪ξ, U_grp.U s ξ⟫_ℂ) from by ring]
    rw [hexp]; ring
  rw [hreorder, integral_const_mul, fourier_kernel_eval hδ (s - t)]
  push_cast; ring

/-- Fourier inversion of the density:
`∫ e^{iλt} borelDensity ε = cexp(-(ε|t|))·⟨ξ,U(t)ξ⟩`. -/
theorem borelDensity_fourier
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∫ lambda : ℝ, cexp (I * ↑lambda * ↑t) * (borelDensity U_grp ξ hε lambda : ℂ)
      = cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ := by
  have hD_int : Integrable (borelDensity U_grp ξ hε) volume := (borelDensity_mass U_grp ξ hε).1
  -- LHS limit by dominated convergence along 𝓝[>] 0.
  have h_lhs : Tendsto (fun δ : ℝ => ∫ lambda : ℝ, cexp (I * ↑lambda * ↑t) *
        (borelDensity U_grp ξ hε lambda : ℂ) * (Real.exp (-(δ * |lambda|)) : ℂ))
      (𝓝[>] 0)
      (𝓝 (∫ lambda : ℝ,
        cexp (I * ↑lambda * ↑t) * (borelDensity U_grp ξ hε lambda : ℂ))) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun lambda => borelDensity U_grp ξ hε lambda)
    · refine Filter.Eventually.of_forall (fun δ => ?_)
      apply Continuous.aestronglyMeasurable
      exact ((Complex.continuous_exp.comp (by fun_prop)).mul
        (Complex.continuous_ofReal.comp (borelDensity_continuous U_grp ξ hε))).mul
        (Complex.continuous_ofReal.comp (by fun_prop))
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ' : 0 < δ := Set.mem_Ioi.mp hδ
      filter_upwards with lambda
      have hexp_le : Real.exp (-(δ * |lambda|)) ≤ 1 := by
        have h_nonpos : -(δ * |lambda|) ≤ 0 := by
          have := mul_nonneg hδ'.le (abs_nonneg lambda); linarith
        calc Real.exp (-(δ * |lambda|)) ≤ Real.exp 0 := Real.exp_le_exp.mpr h_nonpos
          _ = 1 := Real.exp_zero
      simp only [ofReal_exp, ofReal_neg, ofReal_mul, Complex.norm_mul, Complex.norm_exp,
        Complex.norm_real, norm_real, Real.norm_eq_abs, show (I * ↑lambda * ↑t).re = 0
        from by simp [Complex.mul_re], Real.exp_zero, one_mul,
        abs_of_nonneg (borelDensity_nonneg U_grp ξ hε lambda)]
      simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, ge_iff_le]
      calc borelDensity U_grp ξ hε lambda * Real.exp (-(δ * |lambda|))
          ≤ borelDensity U_grp ξ hε lambda * 1 :=
            mul_le_mul_of_nonneg_left hexp_le (borelDensity_nonneg U_grp ξ hε lambda)
        _ = borelDensity U_grp ξ hε lambda := mul_one _
    · exact hD_int
    · refine Filter.Eventually.of_forall (fun lambda => ?_)
      have hr : Tendsto (fun δ : ℝ => Real.exp (-(δ * |lambda|))) (𝓝[>] 0) (𝓝 1) := by
        have hc : Continuous (fun δ : ℝ => Real.exp (-(δ * |lambda|))) := by fun_prop
        refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
        simpa using hc.tendsto 0
      have hlim1 :
          Tendsto (fun δ : ℝ => (Real.exp (-(δ * |lambda|)) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
        have := (Complex.continuous_ofReal.tendsto 1).comp hr
        simpa [Function.comp_def] using this
      simpa using (Filter.Tendsto.const_mul
        (cexp (I * ↑lambda * ↑t) * (borelDensity U_grp ξ hε lambda : ℂ)) hlim1)
  -- RHS limit via fourier_regularized_value + fourier_poisson_tendsto.
  have h_rhs : Tendsto (fun δ : ℝ => ((2 * Real.pi : ℝ) : ℂ) * ∫ lambda : ℝ,
        cexp (I * ↑lambda * ↑t) * (borelDensity U_grp ξ hε lambda : ℂ) *
        (Real.exp (-(δ * |lambda|)) : ℂ))
      (𝓝[>] 0)
      (𝓝 (((2 * Real.pi : ℝ) : ℂ) *
        (cexp (-(↑ε * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ))) := by
    refine (fourier_poisson_tendsto U_grp ξ hε t).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (fourier_regularized_value U_grp ξ hε t (Set.mem_Ioi.mp hδ)).symm
  -- Match limits, cancel 2π.
  have h_lhs_scaled := h_lhs.const_mul ((2 * Real.pi : ℝ) : ℂ)
  have h_unique := tendsto_nhds_unique h_rhs h_lhs_scaled
  have h2pi_ne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  exact (mul_left_cancel₀ h2pi_ne h_unique).symm

end Spectra.Borel

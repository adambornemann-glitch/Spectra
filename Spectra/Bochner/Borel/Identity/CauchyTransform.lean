/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.Bochner.Borel.CDF
import Spectra.Kernel.Resolvent
import Spectra.Resolvent.Identities

/-!
# The Cauchy Transform of the Helly Limit and the Diagonal Resolvent

The Bochner-route proof of the spectral theorem identifies the diagonal resolvent matrix element
`⟪ξ, R(z)ξ⟫` (`z` off the real axis) as the Cauchy transform of a limit measure obtained via
Helly selection from the mollified Poisson densities `borelDensity`. This file proves that
identification: the Cauchy transform of the approximants along the Helly subsequence converges to
`⟪ξ, R(z)ξ⟫` for every `z` with nonzero imaginary part
(`borel_cauchy_approx_tendsto`).

## Main definitions

* `borelSubseq`: the strictly monotone subsequence of indices selected by Helly's theorem.
* `borelCauchyApprox`: the Cauchy transform `∫ (λ - z)⁻¹ dμ_k(λ)` of the `k`-th approximant's
  Poisson density, evaluated along the Helly subsequence.

## Main statements

* `borel_cauchy_approx_tendsto`: `borelCauchyApprox U_grp ξ z` tends to `⟪ξ, R(z)ξ⟫` as `k → ∞`.

## Implementation notes

The proof has two parts. First, a lower-half-plane core case (`w.im < 0`): the Cauchy kernel
`(λ - w)⁻¹` is rewritten via its Laplace representation as a one-sided Fourier integral, a Fubini
swap exposes the Fourier-transform identity `borelDensity_fourier`, and the resulting expression is
recognised as the resolvent at `w - iε k`, which tends to the resolvent at `w` as `ε k → 0`.
Second, a conjugation dichotomy transports the lower-half-plane result to the upper half-plane:
for `z.im > 0`, `borelCauchyApprox U_grp ξ z` is the complex conjugate of the (already-proved)
lower-half-plane value at `conj z`.

## References

* Reed, Simon, *Methods of Modern Mathematical Physics I*, Section VII (Stieltjes–Perron
  inversion and the Cauchy/Poisson representation of the resolvent).

## Tags

Cauchy transform, resolvent, Herglotz representation, Helly selection
-/

open Complex MeasureTheory Filter Topology
open Spectra.Resolvent
open Spectra.OneParameterUnitaryGroup
open scoped InnerProductSpace ComplexConjugate
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Borel
variable (U_grp : OneParameterUnitaryGroup (H := H))

/-- The subsequence selected by Helly — the same witness underlying `borelLimitCDF`. -/
noncomputable def borelSubseq (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) : ℕ → ℕ :=
  (borelHelly U_grp ξ).choose_spec.choose

/-- The approximant's Cauchy transform, indexed along the Helly subsequence. -/
noncomputable def borelCauchyApprox
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) (z : ℂ) (k : ℕ) : ℂ :=
  ∫ lambda : ℝ, ((lambda : ℂ) - z)⁻¹ *
    (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) lambda : ℂ)

private lemma borelSubseq_eps_tendsto (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) :
    Tendsto (fun k => (1 : ℝ) / ((borelSubseq U_grp ξ k : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat.comp
    (borelHelly U_grp ξ).choose_spec.choose_spec.1.tendsto_atTop

/-- `borelSubseq` is strictly monotone, as guaranteed by Helly's selection theorem. -/
lemma borelSubseq_strictMono (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) :
    StrictMono (borelSubseq U_grp ξ) :=
  (borelHelly U_grp ξ).choose_spec.choose_spec.1

/-- Convergence at rationals, along the selected subsequence. -/
lemma borelApproxCDF_tendsto_rat (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) (q : ℚ) :
    Tendsto (fun k => borelApproxCDF U_grp ξ (borelSubseq U_grp ξ k) (q : ℝ)) atTop
      (𝓝 (borelLimitCDF U_grp ξ (q : ℝ))) :=
  borelLimitCDF_tendsto_rat U_grp ξ q

/-- Convergence at continuity points of the limit CDF — the input to vague convergence (a). -/
lemma borelApproxCDF_tendsto_continuousAt (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H)
    {x : ℝ} (hx : ContinuousAt (borelLimitCDF U_grp ξ) x) :
    Tendsto (fun k => borelApproxCDF U_grp ξ (borelSubseq U_grp ξ k) x) atTop
      (𝓝 (borelLimitCDF U_grp ξ x)) :=
  borelLimitCDF_tendsto_continuousAt U_grp ξ x hx

/-- Cauchy transform under complex conjugation (density form): for a real-
valued density `ρ`, conjugating the Cauchy-type integral at `z` gives the
same integral at `conj z`. -/
lemma cauchy_density_integral_conj (ρ : ℝ → ℝ) (z : ℂ) :
    (starRingEnd ℂ) (∫ l, ((l : ℝ) - z)⁻¹ * (ρ l : ℝ))
      = ∫ l, ((l : ℝ) - starRingEnd ℂ z)⁻¹ * (ρ l : ℂ) := by
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only [map_mul, map_inv₀, map_sub, Complex.conj_ofReal]

/-- The approximant's Cauchy transform tends to the diagonal resolvent matrix element
`⟪ξ, R(z)ξ⟫`. -/
lemma borel_cauchy_approx_tendsto
    (U_grp : OneParameterUnitaryGroup (H := H)) (ξ : H) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (borelCauchyApprox U_grp ξ z) atTop
      (𝓝 ⟪ξ, resolvent z hz (generator_isFormalAdjoint U_grp)
              (range_plus_i_eq_top U_grp) (range_minus_i_eq_top U_grp) ξ⟫_ℂ) := by
  have hsym  := generator_isFormalAdjoint U_grp
  have hplus := range_plus_i_eq_top  U_grp
  have hmin  := range_minus_i_eq_top U_grp
  -- The lower-half-plane core case: `w.im < 0`.
  have core : ∀ (w : ℂ) (hw : w.im < 0),
      Tendsto (borelCauchyApprox U_grp ξ w) atTop
        (𝓝 ⟪ξ, resolvent w (ne_of_lt hw) hsym hplus hmin ξ⟫_ℂ) := by
    intro w hw
    set ε : ℕ → ℝ := fun k => 1 / ((borelSubseq U_grp ξ k : ℝ) + 1) with _ε_def
    have hε  : ∀ k, 0 < ε k := fun k => borelEps_pos _
    have hε0 : Tendsto ε atTop (𝓝 0) := borelSubseq_eps_tendsto U_grp ξ
    have hwk_im : ∀ k, (w - I * (ε k : ℂ)).im = w.im - ε k := by
      intro k; simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                     Complex.ofReal_re, Complex.ofReal_im]
    have hwk : ∀ k, (w - I * (ε k : ℂ)).im < 0 := fun k => by
      rw [hwk_im k]; linarith [hε k]
    -- Step A: the approximant's Cauchy transform equals the resolvent at the shifted point
    -- `w - iε k`, via the Laplace representation of the Cauchy kernel and `borelDensity_fourier`.
    have stepA : ∀ k,
        borelCauchyApprox U_grp ξ w k
          = ⟪ξ, resolvent (w - I*(ε k:ℂ)) (ne_of_lt (hwk k)) hsym hplus hmin ξ⟫_ℂ := by
      intro k
      -- (i) Laplace rep of the Cauchy kernel; (λ-w).im = -w.im > 0:
      have hker : ∀ lam : ℝ, ((lam:ℂ) - w)⁻¹
          = -I * ∫ t in Set.Ici (0:ℝ), cexp (-(I*w*(t:ℂ))) * cexp (I*(lam:ℂ)*(t:ℂ)) :=
        fun lam => cauchy_kernel_laplace_neg_im hw lam
      have hD_int := (borelDensity_mass U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k))).1
      have hswap_int : Integrable (Function.uncurry (fun (lam t : ℝ) =>
            cexp (-(I*w*(t:ℂ))) * cexp (I*(lam:ℂ)*(t:ℂ))
              * (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) lam : ℂ)))
          (volume.prod (volume.restrict (Set.Ici 0))) := by
        -- AE strongly measurable via joint continuity.
        have h_meas : AEStronglyMeasurable
            (Function.uncurry (fun (lam t : ℝ) =>
              cexp (-(I*w*(t:ℂ))) * cexp (I*(lam:ℂ)*(t:ℂ))
                * (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) lam : ℂ)))
            (volume.prod (volume.restrict (Set.Ici 0))) := by
          apply Continuous.aestronglyMeasurable
          change Continuous (fun p : ℝ × ℝ =>
            cexp (-(I * w * (p.2 : ℂ))) * cexp (I * (p.1 : ℂ) * (p.2 : ℂ))
              * (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) p.1 : ℂ))
          refine Continuous.mul (Continuous.mul ?_ ?_) ?_
          · exact Complex.continuous_exp.comp (by fun_prop)
          · exact Complex.continuous_exp.comp (by fun_prop)
          · exact Complex.continuous_ofReal.comp
              ((borelDensity_continuous U_grp ξ _).comp continuous_fst)
        -- Dominator t-factor: ∫_{t≥0} exp(w.im · t) dt < ∞ since w.im < 0.
        have hexp_int : Integrable (fun t : ℝ => Real.exp (w.im * t))
            (volume.restrict (Set.Ici 0)) :=
          Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_mul_Ioi hw 0)
        -- Product dominator: borelDensity(lam) · exp(w.im · t).
        have h_dom : Integrable
            (fun p : ℝ × ℝ =>
              borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) p.1
                * Real.exp (w.im * p.2))
            (volume.prod (volume.restrict (Set.Ici 0))) :=
          hD_int.mul_prod hexp_int
        refine h_dom.mono' h_meas ?_
        filter_upwards with p
        change ‖cexp (-(I * w * (p.2 : ℂ))) * cexp (I * (p.1 : ℂ) * (p.2 : ℂ))
              * (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) p.1 : ℂ)‖ ≤ _
        have h1 : (-(I * w * (p.2 : ℂ))).re = w.im * p.2 := by
          simp [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
        have h2 : (I * (p.1 : ℂ) * (p.2 : ℂ)).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
        rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
            Complex.norm_of_nonneg
              (borelDensity_nonneg U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) p.1),
            h1, h2, Real.exp_zero, mul_one]
        exact (mul_comm _ _).le
      -- (iii) unfold, substitute kernel, pull constants, swap, apply borelDensity_fourier:
      unfold borelCauchyApprox
      simp_rw [hker]
      -- Pull the constant `-I` out of the outer λ-integral, past the inner t-integral.
      have hpull_neg_I :
          (∫ lambda : ℝ, (-I * ∫ t in Set.Ici (0:ℝ),
                cexp (-(I*w*(t:ℂ))) * cexp (I*(lambda:ℂ)*(t:ℂ)))
                * (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) lambda : ℂ))
            = -I * ∫ lambda : ℝ, ∫ t in Set.Ici (0:ℝ),
                cexp (-(I*w*(t:ℂ))) * cexp (I*(lambda:ℂ)*(t:ℂ))
                * (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) lambda : ℂ) := by
        rw [← integral_const_mul]
        congr 1
        funext lambda
        field_simp
        rw [← integral_mul_const]
        congr 1
        grind
      rw [hpull_neg_I, integral_integral_swap hswap_int]
      -- inner λ-integral: pull e^{-iwt} out, fold by borelDensity_fourier
      have hinner : ∀ t : ℝ,
          (∫ lambda : ℝ, cexp (-(I*w*(t:ℂ))) * cexp (I*(lambda:ℂ)*(t:ℂ))
              * (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) lambda : ℂ))
            = cexp (-(I*w*(t:ℂ))) * (cexp (-(↑(ε k) * ↑|t|)) * ⟪ξ, U_grp.U t ξ⟫_ℂ) := by
        intro t
        have eqi :
            (∫ lambda : ℝ, cexp (-(I*w*(t:ℂ))) * cexp (I*(lambda:ℂ)*(t:ℂ))
                * (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) lambda : ℂ))
          = ∫ lambda : ℝ, cexp (-(I*w*(t:ℂ))) *
              (cexp (I*(lambda:ℂ)*(t:ℂ)) *
                (borelDensity U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) lambda : ℂ)) := by
          congr 1; funext lambda; ring
        rw [eqi, integral_const_mul,
            borelDensity_fourier U_grp ξ (borelEps_pos (borelSubseq U_grp ξ k)) t]
      simp_rw [hinner, eq_comm]
      -- (iv) on Ici 0, |t| = t and split e^{-iwt}e^{-εt} = e^{-iRe(w)t}·e^{-(ε-Im w)t}
      rw [resolvent_diag_laplace U_grp ξ (hwk k)]
      rw [show (w - I*(ε k:ℂ)) = (⟨w.re, -(ε k - w.im)⟩ : ℂ) from by
            apply Complex.ext <;>
              simp [Complex.I_re, Complex.I_im,
                    Complex.ofReal_re, Complex.ofReal_im, hwk_im]] at *
      -- Reduce to pointwise integrand-equality on Ici 0:
      congr 1
      refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
      -- via I² = -1 as -(I·w·t) + -(↑(ε k)·t), so the two cexp factors combine via exp_add.
      have h_abs : |t| = t := abs_of_nonneg ht
      simp_rw [h_abs]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 1
      apply congrArg Complex.exp
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
              Complex.add_re, Complex.add_im]; ring
    -- Step B: the shifted resolvent tends to the resolvent at `w` as `ε k → 0`.
    have stepB :
        Tendsto (fun k => ⟪ξ, resolvent (w - I*(ε k:ℂ)) (ne_of_lt (hwk k)) hsym hplus hmin ξ⟫_ℂ)
          atTop (𝓝 ⟪ξ, resolvent w (ne_of_lt hw) hsym hplus hmin ξ⟫_ℂ) := by
      have h_lim : Tendsto (fun k => w - I * (ε k : ℂ)) atTop (𝓝 w) := by
        have : Tendsto (fun k => I * (ε k : ℂ)) atTop (𝓝 0) := by
          simpa using tendsto_const_nhds.mul
            ((Complex.continuous_ofReal.tendsto _).comp hε0)
        simpa using tendsto_const_nhds.sub this
      exact tendsto_const_nhds.inner
        (resolvent_tendsto hsym hplus hmin (ne_of_lt hw)
          (fun k => ne_of_lt (hwk k)) h_lim ξ)
    exact stepB.congr (fun k => (stepA k).symm)
  -- Dichotomy: the lower-half-plane case is `core`; the upper-half-plane case transports it
  -- through the conjugation identity `cauchy_density_integral_conj`.
  rcases hz.lt_or_gt with hneg | hpos
  · exact core z hneg
  · have hcz_lt : (starRingEnd ℂ z).im < 0 := by
      rw [Complex.conj_im]; exact neg_lt_zero.mpr hpos
    have hcz : (starRingEnd ℂ z).im ≠ 0 := ne_of_lt hcz_lt
    have hconj : ∀ k, borelCauchyApprox U_grp ξ z k
                  = (starRingEnd ℂ) (borelCauchyApprox U_grp ξ (starRingEnd ℂ z) k) := fun k => by
      unfold borelCauchyApprox
      rw [cauchy_density_integral_conj _ (starRingEnd ℂ z), Complex.conj_conj]
    have hlim := ((Complex.continuous_conj.tendsto _).comp (core _ hcz_lt)).congr
                  (fun k => (hconj k).symm)
    rwa [resolvent_inner_diag_conj hsym hplus hmin hz hcz] at hlim

end Spectra.Borel

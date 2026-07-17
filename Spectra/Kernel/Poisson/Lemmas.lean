/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.PositiveDefinite.Unitary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
/-!
# Fourier Uniqueness for Finite Measures

A finite positive Borel measure on ℝ is uniquely determined by its
characteristic function (Fourier–Stieltjes transform).

## References

* Lévy, P. "Calcul des Probabilités" (1925), §24 (inversion formula)
* Rudin, *Real and Complex Analysis*, 3rd ed., §9.5
* Connects to `lorentzian` already defined in `Routes.lean`

## Tags

Fourier uniqueness, characteristic function, Lévy inversion, Poisson kernel
-/
open Complex MeasureTheory Filter Topology Set TopologicalSpace
namespace Spectra.Fourier

/-! ## §1: The Lorentzian/Poisson kernel -/

/-- The Poisson kernel (normalized Lorentzian): `P_ε(x) = (1/π) · ε/(x² + ε²)`.
This is a probability density on ℝ for each ε > 0. -/
noncomputable def poissonKernel (ε : ℝ) (x : ℝ) : ℝ :=
  (1 / Real.pi) * (ε / (x ^ 2 + ε ^ 2))

/-- The Poisson kernel is non-negative for ε > 0. -/
lemma poissonKernel_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ poissonKernel ε x := by
  unfold poissonKernel; positivity

/-- The denominator `x² + ε²` is strictly positive for ε > 0. -/
lemma sq_add_sq_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 < x ^ 2 + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos hε)

/-- The Poisson kernel is continuous. -/
lemma poissonKernel_continuous {ε : ℝ} (hε : 0 < ε) :
       Continuous (poissonKernel ε) := by
     unfold poissonKernel
     have hne : ∀ x : ℝ, x ^ 2 + ε ^ 2 ≠ 0 :=
       fun x => (sq_add_sq_pos hε x).ne'
     fun_prop (disch := exact hne _)

/-- The Poisson kernel is measurable. (Currently unused.) -/
lemma poissonKernel_measurable {ε : ℝ} (hε : 0 < ε) :
       Measurable (poissonKernel ε) :=
     (poissonKernel_continuous hε).measurable

/-- `x ↦ (1 + x²)⁻¹` is continuous on ℝ. (Currently unused.) -/
lemma continuous_inv_one_add_sq :
    Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply Continuous.inv₀
  · exact continuous_const.add (continuous_pow 2)
  · intro x; positivity

/-- The Poisson kernel is integrable on ℝ. Proved by showing that
    ∫_{-n}^{n} P_ε converges (to 1) via the arctan antiderivative. -/
lemma poissonKernel_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (poissonKernel ε) volume := by
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have h_deriv : ∀ x : ℝ, HasDerivAt (fun x => (1 / Real.pi) * Real.arctan (x / ε))
      (poissonKernel ε x) x := by
    intro x
    have h := ((Real.hasDerivAt_arctan (x / ε)).comp x
      ((hasDerivAt_id x).div_const ε)).const_mul (1 / Real.pi)
    rw [show poissonKernel ε x =
        (1 / Real.pi) * ((1 / (1 + (x / ε) ^ 2)) * (1 / ε)) by
      unfold poissonKernel
      field_simp [hε_ne, (sq_add_sq_pos hε x).ne']
      ring]
    exact h
  have h_FTC : ∀ a b : ℝ, ∫ x in a..b, poissonKernel ε x =
      (1 / Real.pi) * Real.arctan (b / ε) -
      (1 / Real.pi) * Real.arctan (a / ε) :=
    fun a b => intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => h_deriv x)
      (poissonKernel_continuous hε).continuousOn.intervalIntegrable
  have h_nat_div : Tendsto (fun n : ℕ => (n : ℝ) / ε) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b; exact ⟨⌈b * ε⌉₊ + 1, fun n hn => by
      rw [le_div_iff₀ hε]
      exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (by omega))⟩
  apply integrable_of_intervalIntegral_norm_tendsto (l := atTop) (μ := volume)
    (a := fun n : ℕ => -(n : ℝ)) (b := fun n : ℕ => (n : ℝ))
  · intro n
    exact ((poissonKernel_continuous hε).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  · exact tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  · exact tendsto_natCast_atTop_atTop
  · have h_eq : ∀ n : ℕ,
        ∫ x in (-(n:ℝ))..(n:ℝ), ‖poissonKernel ε x‖ =
        (1 / Real.pi) * Real.arctan ((n:ℝ) / ε) -
        (1 / Real.pi) * Real.arctan (-(n:ℝ) / ε) := by
      intro n
      have h_norm : ∫ x in (-(n:ℝ))..(n:ℝ), ‖poissonKernel ε x‖ =
          ∫ x in (-(n:ℝ))..(n:ℝ), poissonKernel ε x := by
        apply intervalIntegral.integral_congr
        intro x _
        simp only [Real.norm_eq_abs, abs_eq_self]
        exact poissonKernel_nonneg hε x
      rw [h_norm, h_FTC]
    simp_rw [h_eq]
    have h_top := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((Real.tendsto_arctan_atTop.comp h_nat_div).mono_right nhdsWithin_le_nhds)
    have _h_bot := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((Real.tendsto_arctan_atBot.comp
        ((tendsto_neg_atTop_atBot.comp h_nat_div).congr
          (fun _ => (neg_div _ _).symm))).mono_right nhdsWithin_le_nhds)
    have h_bot := (tendsto_const_nhds (x := 1 / Real.pi)).mul
      ((Real.tendsto_arctan_atBot.comp
        ((tendsto_neg_atTop_atBot.comp h_nat_div).congr
          (fun _ => (neg_div _ _).symm))).mono_right nhdsWithin_le_nhds)
    simpa only [Function.comp_apply] using h_top.sub h_bot

/-- **Poisson kernel integrates to 1**: `∫ P_ε(x) dx = 1`.

Strategy: rewrite `(1/π) · ε/(x²+ε²) = (1/(πε)) · (1+(x/ε)²)⁻¹`,
substitute `u = x/ε`, use `∫ (1+u²)⁻¹ = π`, cancel. -/
lemma poissonKernel_integral_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∫ x, poissonKernel ε x = 1 := by
  have h_int : Integrable (poissonKernel ε) volume := poissonKernel_integrable hε
  have h_lim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poissonKernel ε x)
      atTop (𝓝 (∫ x, poissonKernel ε x)) :=
    intervalIntegral_tendsto_integral h_int tendsto_neg_atTop_atBot tendsto_id
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have h_deriv : ∀ x : ℝ, HasDerivAt (fun x => (1 / Real.pi) * Real.arctan (x / ε))
      (poissonKernel ε x) x := by
    intro x
    have h1 : HasDerivAt (· / ε) (1 / ε) x := (hasDerivAt_id x).div_const ε
    have h2 : HasDerivAt Real.arctan ((1 + (x / ε) ^ 2)⁻¹) (x / ε) :=
      Real.hasDerivAt_arctan' (x / ε)
    have h3 := h2.comp x h1
    have h4 : HasDerivAt (fun x => (1 / Real.pi) * Real.arctan (x / ε))
        ((1 / Real.pi) * ((1 + (x / ε) ^ 2)⁻¹ * (1 / ε))) x :=
      h3.const_mul (1 / Real.pi)
    convert h4 using 1
    unfold poissonKernel
    have _h_pos := sq_add_sq_pos hε x
    field_simp; ring
  have h_interval : ∀ R : ℝ, ∫ x in (-R)..R, poissonKernel ε x =
      (1 / Real.pi) * Real.arctan (R / ε) -
      (1 / Real.pi) * Real.arctan (-R / ε) := by
    intro R
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => h_deriv x)
      (poissonKernel_continuous hε).continuousOn.intervalIntegrable
  have h_val_lim : Tendsto (fun R : ℝ =>
      (1 / Real.pi) * Real.arctan (R / ε) -
      (1 / Real.pi) * Real.arctan (-R / ε))
      atTop (𝓝 1) := by
    have h_div_atTop : Tendsto (fun R : ℝ => R / ε) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b; exact ⟨b * ε, fun x hx => (le_div_iff₀ hε).mpr hx⟩
    have h_div_atBot : Tendsto (fun R : ℝ => -R / ε) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp h_div_atTop).congr (fun R => by grind)
    have h_arctan_top := (Real.tendsto_arctan_atTop.comp h_div_atTop).mono_right
      nhdsWithin_le_nhds
    have h_top : Tendsto (fun R : ℝ => (1 / Real.pi) * Real.arctan (R / ε))
        atTop (𝓝 ((1 / Real.pi) * (Real.pi / 2))) :=
      tendsto_const_nhds.mul h_arctan_top
    have h_arctan_bot := (Real.tendsto_arctan_atBot.comp h_div_atBot).mono_right
      nhdsWithin_le_nhds
    have h_bot : Tendsto (fun R : ℝ => (1 / Real.pi) * Real.arctan (-R / ε))
        atTop (𝓝 ((1 / Real.pi) * -(Real.pi / 2))) :=
      tendsto_const_nhds.mul h_arctan_bot
    have h_sub := h_top.sub h_bot
    rw [show (1 / Real.pi) * (Real.pi / 2) - (1 / Real.pi) * -(Real.pi / 2) = 1 from by
      field_simp; ring] at h_sub; exact tendsto_ofReal_iff'.mp h_sub
  -- ── Step 5: Uniqueness of limits ──
  have h_lim2 : Tendsto (fun R : ℝ => ∫ x in (-R)..R, poissonKernel ε x)
      atTop (𝓝 1) := by
    simp_rw [h_interval]; exact h_val_lim
  exact tendsto_nhds_unique h_lim h_lim2

/-- `I * a * b` is purely imaginary for real `a`, `b` — the real part of the exponent in
`cexp (I * a * b)` vanishes, which is what makes such an exponential have norm 1. -/
lemma re_I_mul_ofReal_mul_ofReal (a b : ℝ) : (I * (a : ℂ) * (b : ℂ)).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

/-! ## Phase 1: Half-line exponential integral (engine for Route C) -/

/-- Norm of `cexp(-(a * t))` for real `t`. -/
private lemma norm_cexp_neg_mul_ofReal (a : ℂ) (t : ℝ) :
    ‖cexp (-(a * ↑t))‖ = Real.exp (-a.re * t) := by
  rw [Complex.norm_exp]
  simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- `cexp(-(a * t)) → 0` as `t → +∞` when `0 < a.re`. (Currently unused.) -/
private lemma tendsto_cexp_neg_mul_ofReal_atTop {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => cexp (-(a * ↑t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_cexp_neg_mul_ofReal]
  have h_atBot : Tendsto (fun t : ℝ => -a.re * t) atTop atBot := by
    have h1 : Tendsto (fun t : ℝ => a.re * t) atTop atTop :=
      tendsto_atTop_atTop_of_monotone (fun _ _ h => mul_le_mul_of_nonneg_left h ha.le)
        (fun b => ⟨b / a.re, by rw [mul_div_cancel₀ _ (ne_of_gt ha)]⟩)
    exact (tendsto_neg_atTop_atBot.comp h1).congr (fun t => by ring_nf; rfl)
  exact Real.tendsto_exp_atBot.comp h_atBot

/-- Derivative of the antiderivative `-a⁻¹ * cexp(-(a * t))`. (Currently unused.) -/
private lemma hasDerivAt_antideriv_cexp {a : ℂ} (ha_ne : a ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -a⁻¹ * cexp (-(a * ↑t)))
               (cexp (-(a * ↑t))) t := by
  have h1 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 t := ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (-(fun t : ℝ => a * (t : ℂ))) (-a) t := by
    simpa only [mul_one] using (h1.const_mul a).neg
  have hcoef : (-a⁻¹) * (cexp (-(a * ↑t)) * (-a)) = cexp (-(a * ↑t)) := by
    field_simp [ha_ne]
  exact HasDerivAt.congr_deriv ((h2.cexp).const_mul (-a⁻¹)) hcoef

/-! ## Phase 2: Fourier transform of the two-sided exponential -/

/-- Algebraic identity: `(ε - ξi)⁻¹ + (ε + ξi)⁻¹ = 2ε/(ξ² + ε²)` in ℂ. -/
private lemma inv_add_conj_inv {ε ξ : ℝ} (hε : 0 < ε) :
    (↑ε - ↑ξ * I)⁻¹ + (↑ε + ↑ξ * I)⁻¹ =
    ((2 * ε / (ξ ^ 2 + ε ^ 2) : ℝ) : ℂ) := by
  have h1 : (↑ε - ↑ξ * I : ℂ) ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have h2 : (↑ε + ↑ξ * I : ℂ) ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp at this; linarith
  have _h3 : (ξ ^ 2 + ε ^ 2 : ℝ) ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ξ) (sq_pos_of_pos hε))
  rw [inv_eq_one_div, inv_eq_one_div, div_add_div _ _ h1 h2]
  rw [show (↑ε - ↑ξ * I) * (↑ε + ↑ξ * I) = ↑(ξ ^ 2 + ε ^ 2) from by
    push_cast; ring_nf; simp only [I_sq, mul_neg, mul_one, sub_neg_eq_add]]
  rw [show 1 * (↑ε + ↑ξ * I) + (↑ε - ↑ξ * I) * 1 = ↑(2 * ε) from by push_cast; ring]
  rw [← ofReal_div]

/-- Substitution: `∫_{Iic 0} f(t) dt = ∫_{Ioi 0} f(-u) du` for integrable `f`.
    Uses measure-preserving negation on ℝ. (Currently unused.) -/
private lemma setIntegral_Iic_comp_neg (f : ℝ → ℂ) :
    ∫ t in Set.Iic (0 : ℝ), f t = ∫ u in Set.Ioi (0 : ℝ), f (-u) := by
  rw [integral_comp_neg_Ioi (0 : ℝ) f, neg_zero]

/-- The two-sided exponential integrand `e^{-ε|t|} · e^{iξt}` is integrable on ℝ. -/
lemma integrable_two_sided_exp {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    Integrable (fun t : ℝ => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t)) volume := by
  rw [← integrableOn_univ,
      show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ioi 0 from Set.Iic_union_Ioi.symm]
  refine IntegrableOn.union ?_ ?_
  · -- On Iic 0: |t| = -t, so the integrand is cexp((ε + ξI) · t), Re = ε > 0
    have hre : 0 < (↑ε + ↑ξ * I : ℂ).re := by simpa using hε
    refine (integrableOn_exp_mul_complex_Iic hre 0).congr_fun
      (fun t ht => ?_) measurableSet_Iic
    rw [abs_of_nonpos ht, ← Complex.exp_add]
    push_cast; ring_nf
  · -- On Ioi 0: |t| = t, so the integrand is cexp((-ε + ξI) · t), Re = -ε < 0
    have hre : (-↑ε + ↑ξ * I : ℂ).re < 0 := by simpa using hε
    refine (integrableOn_exp_mul_complex_Ioi hre 0).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos ht, ← Complex.exp_add]
    push_cast; ring_nf

/-- The one-sided real exponential `e^{-c|t|}` is integrable, as the norm of the two-sided
complex exponential `integrable_two_sided_exp` at frequency `ξ = 0`. -/
lemma integrable_exp_neg_abs_mul {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => Real.exp (-(c * |t|))) volume := by
  refine ((integrable_two_sided_exp hc 0).norm).congr ?_
  filter_upwards with t
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, Complex.norm_exp]
  congr 1; simp [Complex.mul_re]

/-- **Fourier transform of the two-sided exponential**:
    `∫ e^{-ε|t|} · e^{iξt} dt = 2ε/(ξ² + ε²)` for `ε > 0`. -/
lemma fourier_two_sided_exp {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    ∫ t : ℝ, cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t) =
    ((2 * ε / (ξ ^ 2 + ε ^ 2) : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun t => cexp (-(↑ε * ↑|t|)) * cexp (I * ↑ξ * ↑t)
  have hf_int : Integrable f := integrable_two_sided_exp hε ξ
  have h_re_pos : 0 < (↑ε + ↑ξ * I : ℂ).re := by simpa using hε
  have h_re_neg : (-↑ε + ↑ξ * I : ℂ).re < 0 := by simpa using hε
  -- Split ∫_ℝ = ∫_{Ioi 0} + ∫_{Iic 0}
  have h_split : (∫ t, f t) = (∫ t in Set.Ioi 0, f t) + (∫ t in Set.Iic 0, f t) := by
    rw [← integral_add_compl measurableSet_Ioi hf_int, Set.compl_Ioi]
  -- Positive half: |t| = t makes f(t) = cexp((-ε + ξI)·t); integrates to (ε - ξI)⁻¹
  have h_pos : ∫ t in Set.Ioi 0, f t = (↑ε - ↑ξ * I : ℂ)⁻¹ := by
    have hne₁ : (-↑ε + ↑ξ * I : ℂ) ≠ 0 := fun h => by
      have := congr_arg Complex.re h; simp at this; linarith
    have hne₂ : (↑ε - ↑ξ * I : ℂ) ≠ 0 := fun h => by
      have := congr_arg Complex.re h; simp at this; linarith
    have h_eq : ∫ t in Set.Ioi 0, f t =
        ∫ t in Set.Ioi (0 : ℝ), cexp ((-↑ε + ↑ξ * I) * ↑t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      show f t = _
      simp only [f, abs_of_pos (Set.mem_Ioi.mp ht), ← Complex.exp_add]
      congr 1; ring
    rw [h_eq, integral_exp_mul_complex_Ioi h_re_neg]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
    ring
  -- Negative half: |t| = -t makes f(t) = cexp((ε + ξI)·t); integrates to (ε + ξI)⁻¹
  have h_neg : ∫ t in Set.Iic 0, f t = (↑ε + ↑ξ * I : ℂ)⁻¹ := by
    have h_eq : ∫ t in Set.Iic 0, f t =
        ∫ t in Set.Iic (0 : ℝ), cexp ((↑ε + ↑ξ * I) * ↑t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      show f t = _
      simp only [f, abs_of_nonpos (Set.mem_Iic.mp ht), ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [h_eq, integral_exp_mul_complex_Iic h_re_pos]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_div]
  -- Combine via the algebraic identity
  rw [h_split, h_pos, h_neg, inv_add_conj_inv hε]

end Spectra.Fourier

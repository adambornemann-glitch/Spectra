/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Orthogonality
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
/-!
# Associated Laguerre Polynomials

The associated Laguerre polynomials L_n^α(x), which form the radial
eigenfunctions of the hydrogen atom after appropriate substitutions.

## Main statements
* `laguerre_complete` — completeness of `{Lₙ^{(α)}}` in `L²(ℝ⁺, xᵅ e⁻ˣ dx)`: any
  `L²(μ_α)` function orthogonal to every `Lₙ^{(α)}` is a.e. zero.
* `laguerre_norm_sq` — the squared norm
  `∫₀^∞ xᵅ e⁻ˣ (Lₙ^{(α)})² dx = Γ(n+α+1) / n!`.
* `laguerre_x_norm_sq` — the first moment `∫₀^∞ x · xᵅ e⁻ˣ (Lₙ^{(α)})² dx
  = (2n+α+1) · Γ(n+α+1) / n!`.

## Implementation notes

Completeness is proved as a moment problem. Given `f ∈ L²(μ_α)` orthogonal to every
`Lₙ^{(α)}`, orthogonality to the polynomials upgrades to orthogonality to every monomial `xᵏ`
(`laguerre_ortho_monomial`), so all weighted moments of `g := w · f` vanish (`g_moments_zero`).
The two-sided Laplace transform `laplaceTr α f z = ∫ w·f·e^{zx}` is holomorphic on the strip
`{Re z < 1/2}` (`laplaceTr_differentiableOn`, via a dominated parametric-integral argument with an
exponential tilt) and vanishes near `0` because its Taylor coefficients are the moments
(`laplaceTr_eventuallyEq_zero`); the identity theorem then kills it on the whole strip
(`laplaceTr_eqOn_zero`). Restricting to the imaginary axis gives a vanishing Fourier transform of
the integrable function `g`, whence `g = 0` a.e. by characteristic-function uniqueness on the
positive/negative parts (`ae_zero_of_fourier_zero`), and finally `f = 0` a.e. `[μ_α]` since
`w > 0` on `(0,∞)` (`ae_zero_laguerreMeasure_of_g_ae_zero`). The norm and first-moment formulas
are proved separately from the three-term recurrence and orthogonality.

## References

* [Szegő, *Orthogonal Polynomials*][szego1975]
* [Abramowitz, Stegun, *Handbook of Mathematical Functions*][abramowitz1965], Ch. 22.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
-/
open MeasureTheory Complex Filter Real Polynomial
open scoped Topology NNReal ENNReal Nat
namespace Spectra.QuantumMechanics.Hydrogen.Radial

/-- The weighted moment: ∫₀^∞ xᵃ e⁻ˣ · xᵏ dx = Γ(α+k+1). -/
lemma laguerreWeight_mul_pow_moment (α : ℝ) (hα : -1 < α) (k : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * x ^ k = Real.Gamma (α + k + 1) := by
  have hs : (0 : ℝ) < α + k + 1 := by
    have _hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [Real.Gamma_eq_integral hs]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [Set.mem_Ioi] at hx
  simp only [laguerreWeight, if_pos hx]
  rw [show α + (k : ℝ) + 1 - 1 = α + (k : ℝ) by ring, Real.rpow_add hx, Real.rpow_natCast]
  ring

/-- Base case n = 0:  ∫₀^∞ w · L₀² = Γ(α+1)  (since L₀ = 1). -/
lemma laguerre_norm_sq_zero (α : ℝ) (hα : -1 < α) :
    ∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial 0 α x) ^ 2
      = Real.Gamma (α + 1) := by
  have hL0 : ∀ x : ℝ, laguerrePolynomial 0 α x = 1 := by
    intro x
    simp [laguerrePolynomial, realBinom]
  simp only [hL0, one_pow, mul_one]
  simpa using laguerreWeight_mul_pow_moment α hα 0

/-- Base case n = 1:  ∫₀^∞ w · L₁² = Γ(α+2)  (since L₁ = 1+α-x). -/
lemma laguerre_norm_sq_one (α : ℝ) (hα : -1 < α) :
    ∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial 1 α x) ^ 2
      = Real.Gamma (α + 2) := by
  have hL1 : ∀ x : ℝ, laguerrePolynomial 1 α x = 1 + α - x := by
    intro x
    simp only [laguerrePolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, realBinom, Finset.prod_range_one, Finset.prod_range_zero,
      Nat.sub_zero, Nat.sub_self, Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero,
      Nat.cast_one, pow_zero, pow_one, sub_zero, div_one, one_mul, mul_one]
    ring
  have hα1 : (α : ℝ) + 1 ≠ 0 := (show (0 : ℝ) < α + 1 by linarith).ne'
  have hα2 : (α : ℝ) + 2 ≠ 0 := (show (0 : ℝ) < α + 2 by linarith).ne'
  have hG2 : Real.Gamma (α + 2) = (α + 1) * Real.Gamma (α + 1) := by
    rw [show (α + 2 : ℝ) = α + 1 + 1 by ring, Real.Gamma_add_one hα1]
  have hA : IntegrableOn (fun x => (1 + α) ^ 2 * (laguerreWeight α x * x ^ 0)) (Set.Ioi 0) :=
    Integrable.const_mul (laguerreWeight_mul_pow_integrable α hα 0) _
  have hB : IntegrableOn (fun x => 2 * (1 + α) * (laguerreWeight α x * x ^ 1)) (Set.Ioi 0) :=
    Integrable.const_mul (laguerreWeight_mul_pow_integrable α hα 1) _
  have hC : IntegrableOn (fun x => laguerreWeight α x * x ^ 2) (Set.Ioi 0) :=
    laguerreWeight_mul_pow_integrable α hα 2
  erw [show (∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial 1 α x) ^ 2)
        = ∫ x in Set.Ioi (0 : ℝ),
            ((1 + α) ^ 2 * (laguerreWeight α x * x ^ 0)
              - 2 * (1 + α) * (laguerreWeight α x * x ^ 1)) + laguerreWeight α x * x ^ 2
      from setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [hL1]; ring),
    integral_add (Integrable.sub hA hB) hC, integral_sub hA hB,
    integral_const_mul, integral_const_mul,
    laguerreWeight_mul_pow_moment α hα 0, laguerreWeight_mul_pow_moment α hα 1,
    laguerreWeight_mul_pow_moment α hα 2]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero]
  rw [Real.Gamma_add_one hα1, Real.Gamma_add_one hα2, hG2]
  ring

/-- Norm recurrence: for `n ≥ 1`,  `(n+1)·hₙ₊₁ = (n+1+α)·hₙ`. -/
lemma laguerre_norm_sq_step (α : ℝ) (hα : -1 < α) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) *
        (∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial (n + 1) α x) ^ 2)
    = ((n : ℝ) + 1 + α) *
        (∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial n α x) ^ 2) := by
  -- (★) the weighted pointwise identity; RHS is a sum of cross terms
  have key2 : ∀ x : ℝ,
      ((n : ℝ) + 1) * (laguerreWeight α x * (laguerrePolynomial (n + 1) α x) ^ 2)
        - ((n : ℝ) + 1 + α) * (laguerreWeight α x * (laguerrePolynomial n α x) ^ 2)
      = -2 * (laguerreWeight α x * laguerrePolynomial (n + 1) α x * laguerrePolynomial n α x)
        + ((n : ℝ) + 2) *
            (laguerreWeight α x * laguerrePolynomial (n + 2) α x * laguerrePolynomial n α x)
        - ((n : ℝ) + α) *
            (laguerreWeight α x * laguerrePolynomial (n + 1) α x *
              laguerrePolynomial (n - 1) α x) := by
    intro x
    have hR1 := laguerre_recurrence n α hn x
    have hR2 := laguerre_recurrence (n + 1) α (by omega) x
    rw [(by omega : n + 1 + 1 = n + 2), Nat.add_sub_cancel] at hR2
    push_cast at hR2
    linear_combination (laguerreWeight α x * laguerrePolynomial (n + 1) α x) * hR1
      - (laguerreWeight α x * laguerrePolynomial n α x) * hR2
  -- integrability of the five pieces (squares via Brick 1 at i = j)
  have iSq1 : IntegrableOn
      (fun x => laguerreWeight α x * (laguerrePolynomial (n + 1) α x) ^ 2) (Set.Ioi 0) := by
    simpa only [pow_two, mul_assoc] using
      laguerreWeight_mul_laguerre_mul_laguerre_integrable (n + 1) (n + 1) α hα
  have iSqn : IntegrableOn
      (fun x => laguerreWeight α x * (laguerrePolynomial n α x) ^ 2) (Set.Ioi 0) := by
    simpa only [pow_two, mul_assoc] using
      laguerreWeight_mul_laguerre_mul_laguerre_integrable n n α hα
  have iC1 := laguerreWeight_mul_laguerre_mul_laguerre_integrable (n + 1) n α hα
  have iC2 := laguerreWeight_mul_laguerre_mul_laguerre_integrable (n + 2) n α hα
  have iC3 := laguerreWeight_mul_laguerre_mul_laguerre_integrable (n + 1) (n - 1) α hα
  -- integrate the LHS of (★) by linearity
  have eLHS : (∫ x in Set.Ioi (0 : ℝ),
        (((n : ℝ) + 1) * (laguerreWeight α x * (laguerrePolynomial (n + 1) α x) ^ 2)
          - ((n : ℝ) + 1 + α) * (laguerreWeight α x * (laguerrePolynomial n α x) ^ 2)))
      = ((n : ℝ) + 1) *
          (∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial (n + 1) α x) ^ 2)
        - ((n : ℝ) + 1 + α) *
          (∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial n α x) ^ 2) := by
    rw [integral_sub (Integrable.const_mul iSq1 ((n : ℝ) + 1))
        (Integrable.const_mul iSqn ((n : ℝ) + 1 + α)),
      integral_const_mul, integral_const_mul]
  -- integrate the RHS of (★): every term is orthogonal ⇒ 0
  have eRHS : (∫ x in Set.Ioi (0 : ℝ),
        (-2 * (laguerreWeight α x * laguerrePolynomial (n + 1) α x * laguerrePolynomial n α x)
          + ((n : ℝ) + 2) *
              (laguerreWeight α x * laguerrePolynomial (n + 2) α x * laguerrePolynomial n α x)
          - ((n : ℝ) + α) *
              (laguerreWeight α x * laguerrePolynomial (n + 1) α x
                * laguerrePolynomial (n - 1) α x))) = 0 := by
    erw [integral_sub
        (Integrable.add (Integrable.const_mul iC1 (-2 : ℝ))
          (Integrable.const_mul iC2 ((n : ℝ) + 2)))
        (Integrable.const_mul iC3 ((n : ℝ) + α)),
      integral_add (Integrable.const_mul iC1 (-2 : ℝ)) (Integrable.const_mul iC2 ((n : ℝ) + 2)),
      integral_const_mul, integral_const_mul, integral_const_mul,
      laguerre_orthogonality (n + 1) n α hα (by omega),
      laguerre_orthogonality (n + 2) n α hα (by omega),
      laguerre_orthogonality (n + 1) (n - 1) α hα (by omega)]
    ring
  -- the two integrals agree, so the LHS combination is 0
  have main : (∫ x in Set.Ioi (0 : ℝ),
        (((n : ℝ) + 1) * (laguerreWeight α x * (laguerrePolynomial (n + 1) α x) ^ 2)
          - ((n : ℝ) + 1 + α) * (laguerreWeight α x * (laguerrePolynomial n α x) ^ 2)))
      = ∫ x in Set.Ioi (0 : ℝ),
        (-2 * (laguerreWeight α x * laguerrePolynomial (n + 1) α x * laguerrePolynomial n α x)
          + ((n : ℝ) + 2) *
              (laguerreWeight α x * laguerrePolynomial (n + 2) α x * laguerrePolynomial n α x)
          - ((n : ℝ) + α) *
              (laguerreWeight α x * laguerrePolynomial (n + 1) α x
                * laguerrePolynomial (n - 1) α x)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x _ => key2 x)
  rw [eLHS, eRHS] at main
  linear_combination main

/-- **Squared norm of the associated Laguerre polynomials.**
For `α > -1`,  `∫₀^∞ xᵅ e⁻ˣ (Lₙ^{(α)}(x))² dx = Γ(n+α+1) / n!`. -/
theorem laguerre_norm_sq (α : ℝ) (hα : -1 < α) (n : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial n α x) ^ 2
    = Real.Gamma ((n : ℝ) + α + 1) / (Nat.factorial n : ℝ) := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · -- n = 0
    rw [laguerre_norm_sq_zero α hα, Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, zero_add,
      div_one]
  · -- n ≥ 1 : induct from the base case n = 1
    replace hn : 1 ≤ n := hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [laguerre_norm_sq_one α hα, Nat.factorial_one, Nat.cast_one, div_one,
        show (1 : ℝ) + α + 1 = α + 2 by ring]
    | succ m hm ih =>
      have hstep := laguerre_norm_sq_step α hα m hm
      have hc : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hF0 : (Nat.factorial m : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have hGpos : (0 : ℝ) < (m : ℝ) + α + 1 := by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hG : Real.Gamma ((↑(m + 1) : ℝ) + α + 1)
          = ((m : ℝ) + α + 1) * Real.Gamma ((m : ℝ) + α + 1) := by
        rw [show (↑(m + 1) : ℝ) + α + 1 = ((m : ℝ) + α + 1) + 1 by push_cast; ring,
          Real.Gamma_add_one hGpos.ne']
      have hF : (Nat.factorial (m + 1) : ℝ) = ((m : ℝ) + 1) * (Nat.factorial m : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
      rw [hG, hF]
      rw [ih] at hstep
      field_simp at hstep ⊢
      linear_combination hstep

/-- **First moment of the squared norm.**
For `α > -1`,  `∫₀^∞ x · xᵅ e⁻ˣ (Lₙ^{(α)}(x))² dx = (2n+α+1) · Γ(n+α+1) / n!`.

This is the `x`-weighted normalisation integral; it follows from the three-term
recurrence (which expresses `x·Lₙ` as a combination of `Lₙ₋₁, Lₙ, Lₙ₊₁`),
orthogonality (killing the off-diagonal terms) and `laguerre_norm_sq`. -/
theorem laguerre_x_norm_sq (α : ℝ) (hα : -1 < α) (n : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * x * (laguerrePolynomial n α x) ^ 2
    = (2 * (n : ℝ) + α + 1) * Real.Gamma ((n : ℝ) + α + 1) / (Nat.factorial n : ℝ) := by
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · -- n = 0 : L₀ = 1, so the integral is the first moment Γ(α+2) = (α+1)Γ(α+1).
    have hL0 : ∀ x : ℝ, laguerrePolynomial 0 α x = 1 := by
      intro x; simp [laguerrePolynomial, realBinom]
    rw [show (∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * x * (laguerrePolynomial 0 α x) ^ 2)
          = ∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * x ^ 1 from
        setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [hL0]; ring),
      laguerreWeight_mul_pow_moment α hα 1]
    simp only [Nat.cast_zero, Nat.factorial_zero, Nat.cast_one]
    rw [show (α + (1 : ℝ) + 1) = (α + 1) + 1 by ring,
      Real.Gamma_add_one (show (0 : ℝ) < α + 1 by linarith).ne']
    ring_nf
  · -- n ≥ 1 : use x·Lₙ = (2n+α+1)Lₙ − (n+1)Lₙ₊₁ − (n+α)Lₙ₋₁.
    replace hn : 1 ≤ n := hn
    have hA := (laguerreWeight_mul_laguerre_mul_laguerre_integrable n n α hα).const_mul
      (2 * (n : ℝ) + α + 1)
    have hB := (laguerreWeight_mul_laguerre_mul_laguerre_integrable (n + 1) n α hα).const_mul
      ((n : ℝ) + 1)
    have hC := (laguerreWeight_mul_laguerre_mul_laguerre_integrable (n - 1) n α hα).const_mul
      ((n : ℝ) + α)
    rw [show (∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * x * (laguerrePolynomial n α x) ^ 2)
          = ∫ x in Set.Ioi (0 : ℝ),
              ((2 * (n : ℝ) + α + 1) *
                  (laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial n α x)
                - ((n : ℝ) + 1) *
                  (laguerreWeight α x * laguerrePolynomial (n + 1) α x * laguerrePolynomial n α x))
              - ((n : ℝ) + α) *
                  (laguerreWeight α x * laguerrePolynomial (n - 1) α x * laguerrePolynomial n α x)
        from setIntegral_congr_fun measurableSet_Ioi (fun x _ => by
          linear_combination
            (laguerreWeight α x * laguerrePolynomial n α x) * laguerre_recurrence n α hn x)]
    erw [integral_sub (hA.sub hB) hC, integral_sub hA hB,
      integral_const_mul, integral_const_mul, integral_const_mul]
    rw [laguerre_orthogonality (n + 1) n α hα (by omega),
      laguerre_orthogonality (n - 1) n α hα (by omega),
      show (∫ x in Set.Ioi (0 : ℝ),
              laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial n α x)
          = ∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial n α x) ^ 2 from
        setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring),
      laguerre_norm_sq α hα n]
    ring

/-! ## Completeness -/

/-- The associated-Laguerre weighting measure `dμ_α = xᵅ e⁻ˣ · 𝟙_{(0,∞)} dx` on ℝ.
    (`laguerreWeight α` already vanishes off `(0,∞)`, so this is supported there.) -/
noncomputable def laguerreMeasure (α : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (laguerreWeight α x))

/-! ### Weight facts

`laguerreWeight_nonneg` carries a redundant `0 ≤ α` hypothesis; the facts below are
restated without it, since `laguerre_complete` only assumes `-1 < α`. -/

/-- The weight `laguerreWeight α` is nonnegative everywhere (no `0 ≤ α` hypothesis needed). -/
lemma laguerreWeight_nonneg' (α : ℝ) (x : ℝ) : 0 ≤ laguerreWeight α x := by
  simp only [laguerreWeight]
  split_ifs with h
  · exact mul_nonneg (Real.rpow_nonneg h.le _) (Real.exp_nonneg _)
  · exact le_refl 0

/-- The weight `laguerreWeight α` is measurable. -/
lemma measurable_laguerreWeight (α : ℝ) : Measurable (laguerreWeight α) := by
  unfold laguerreWeight
  -- `x ↦ x^α * exp (-x)` is measurable; the `if 0 < x` guard is on a measurable set
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/-! ### Finiteness of `laguerreMeasure α` and integration against the Lebesgue weight `w` -/

/-- For `α > -1` the weighting measure `μ_α = xᵅ e⁻ˣ 𝟙_{(0,∞)} dx` is finite
(total mass `Γ(α+1) < ∞`). -/
lemma isFiniteMeasure_laguerreMeasure (α : ℝ) (hα : -1 < α) :
    IsFiniteMeasure (laguerreMeasure α) := by
  rw [laguerreMeasure]
  refine isFiniteMeasure_withDensity_ofReal ?_
  have hsupp : laguerreWeight α = (Set.Ioi 0).indicator (laguerreWeight α) := by
    ext x
    rw [Set.indicator_apply]
    split_ifs with hx
    · rfl
    · rw [Set.mem_Ioi] at hx
      simp only [laguerreWeight, if_neg hx]
  have hint : Integrable (laguerreWeight α) volume := by
    have h := (integrable_indicator_iff measurableSet_Ioi).mpr (laguerreWeight_integrable α hα)
    rwa [← hsupp] at h
  exact hint.hasFiniteIntegral

/-- The defining bridge: `∫ h ∂μ_α = ∫ w · h ∂volume`. -/
lemma integral_laguerreMeasure_eq (α : ℝ) (h : ℝ → ℝ) :
    ∫ x, h x ∂(laguerreMeasure α) = ∫ x, laguerreWeight α x * h x := by
  rw [laguerreMeasure,
      integral_withDensity_eq_integral_toReal_smul₀
        (measurable_laguerreWeight α).ennreal_ofReal.aemeasurable
        (.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (laguerreWeight_nonneg' α x)]

/-! ### Monomials lie in `L²(μ_α)` (so that `f · xᵏ ∈ L¹`) -/

/-- Every monomial `x ↦ xᵏ` lies in `L²(μ_α)` for `α > -1`
(so that `f · xᵏ ∈ L¹(μ_α)` whenever `f ∈ L²(μ_α)`). -/
lemma memLp_two_pow (α : ℝ) (hα : -1 < α) (k : ℕ) :
    MemLp (fun x => x ^ k) 2 (laguerreMeasure α) := by
  -- MemLp (x^k) 2 μ_α  ⟺  Integrable |x^k|² = x^{2k} wrt μ_α
  --                    ⟺  Integrable (w · x^{2k}) wrt volume  (translate withDensity),
  -- and the latter is `laguerreWeight_mul_pow_integrable α hα (2*k)` (vanishing off Ioi 0).
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ k) (laguerreMeasure α) :=
    (continuous_pow k).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas, laguerreMeasure,
      integrable_withDensity_iff_integrable_smul₀'
        (measurable_laguerreWeight α).ennreal_ofReal.aemeasurable
        (.of_forall fun x => ENNReal.ofReal_lt_top)]
  -- The brick: `w · x^{2k}` is integrable on (0,∞); it vanishes off (0,∞), so on all of ℝ.
  have hbrick : IntegrableOn
      (fun x : ℝ => laguerreWeight α x * x ^ (2 * k)) (Set.Ioi 0) volume :=
    laguerreWeight_mul_pow_integrable α hα (2 * k)
  have hsupp : (fun x : ℝ => laguerreWeight α x * x ^ (2 * k))
      = (Set.Ioi 0).indicator (fun x : ℝ => laguerreWeight α x * x ^ (2 * k)) := by
    funext x
    rw [Set.indicator_apply]
    split_ifs with hx
    · rfl
    · rw [Set.mem_Ioi] at hx
      simp only [laguerreWeight, if_neg hx, zero_mul]
  have hInt : Integrable (fun x : ℝ => laguerreWeight α x * x ^ (2 * k)) volume := by
    rw [hsupp]
    exact (integrable_indicator_iff measurableSet_Ioi).2 hbrick
  refine hInt.congr (.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (laguerreWeight_nonneg' α x)]
  rw [← pow_mul, Nat.mul_comm k 2]

/-! ### From orthogonality to every `Lₙ` to orthogonality to every monomial -/

/-- If `f ∈ L²(μ_α)` is orthogonal to every associated Laguerre polynomial `Lₙ^{(α)}`,
then it is orthogonal to every monomial `xᵏ` (by strong induction on `k`, since `Lₖ^{(α)}` has a
nonzero leading coefficient). -/
lemma laguerre_ortho_monomial (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α))
    (hortho : ∀ n : ℕ, ∫ x, f x * laguerrePolynomial n α x ∂(laguerreMeasure α) = 0) :
    ∀ k : ℕ, ∫ x, f x * x ^ k ∂(laguerreMeasure α) = 0 := by
  -- Every `f · xʲ` is in `L¹(μ_α)` (Hölder: `f ∈ L²`, `xʲ ∈ L²`).
  have hInt : ∀ j : ℕ, Integrable (fun x => f x * x ^ j) (laguerreMeasure α) := fun j =>
    memLp_one_iff_integrable.1 ((memLp_two_pow α hα j).mul' hf)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    -- Coefficients of `L_k`:  `L_k(x) = ∑_{j≤k} c j · xʲ`, with `c k = (-1)^k / k! ≠ 0`.
    set c : ℕ → ℝ := fun j => (-1 : ℝ) ^ j * realBinom (k + α) (k - j) / (j.factorial : ℝ)
      with hc
    -- `∫ f·L_k = ∑_{j≤k} c j · ∫ f·xʲ`, by expanding `L_k` and integral linearity.
    have hexpand : ∫ x, f x * laguerrePolynomial k α x ∂(laguerreMeasure α)
        = ∑ j ∈ Finset.range (k + 1), c j * ∫ x, f x * x ^ j ∂(laguerreMeasure α) := by
      have hpoint : (fun x => f x * laguerrePolynomial k α x)
          = fun x => ∑ j ∈ Finset.range (k + 1), c j * (f x * x ^ j) := by
        funext x
        simp only [laguerrePolynomial, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [hc]; ring
      rw [hpoint, integral_finsetSum _ (fun j _ => (hInt j).const_mul (c j))]
      exact Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
    -- The orthogonality hypothesis, in expanded form.
    have hsum : ∑ j ∈ Finset.range (k + 1), c j * ∫ x, f x * x ^ j ∂(laguerreMeasure α) = 0 := by
      rw [← hexpand]; exact hortho k
    -- Split off the top term; the lower terms vanish by the induction hypothesis.
    rw [Finset.sum_range_succ] at hsum
    have hlow : ∑ j ∈ Finset.range k, c j * ∫ x, f x * x ^ j ∂(laguerreMeasure α) = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [ih j (Finset.mem_range.1 hj), mul_zero])
    rw [hlow, zero_add] at hsum
    -- `c k = (-1)^k / k! ≠ 0`, so the surviving factor `∫ f·x^k` must vanish.
    have hck : c k = (-1 : ℝ) ^ k / (k.factorial : ℝ) := by
      simp only [hc, Nat.sub_self, realBinom_zero, mul_one]
    have hck_ne : c k ≠ 0 := by
      rw [hck]
      exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero k)
    exact (mul_eq_zero.1 hsum).resolve_left hck_ne

/-! ### The working function `g := w · f` and its weighted moments

These are stated as plain Lebesgue integrals. -/

/-- `g = w · f`, supported on `(0,∞)`. -/
local notation "g[" α ", " f "]" => fun x : ℝ => laguerreWeight α x * f x

/-- If `f ∈ L²(μ_α)` is orthogonal to every `Lₙ^{(α)}`, then every Lebesgue moment of the weighted
function `g = w · f` vanishes: `∫ (w·f)·xᵏ = 0` for all `k`. -/
lemma g_moments_zero (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α))
    (hortho : ∀ n : ℕ, ∫ x, f x * laguerrePolynomial n α x ∂(laguerreMeasure α) = 0) :
    ∀ k : ℕ, ∫ x, (laguerreWeight α x * f x) * x ^ k = 0 := by
  intro k
  have := laguerre_ortho_monomial α hα f hf hortho k
  rw [integral_laguerreMeasure_eq] at this
  -- `w x * (f x * x^k) = (w x * f x) * x^k`
  simpa [mul_assoc] using this

/-! ### Exponential-tilt integrability: `g · e^{c·} ∈ L¹` for `c < 1/2`

The key fact is `e^{c·} ∈ L²(μ_α)`, since `∫ e^{2cx} dμ_α = ∫_{Ioi 0} xᵃ e^{(2c-1)x} < ∞`. -/

/-- For `c < 1/2` the exponential `x ↦ e^{cx}` lies in `L²(μ_α)`, because
`∫ e^{2cx} dμ_α = ∫_{Ioi 0} xᵅ e^{-(1-2c)x} dx < ∞` (a scaled Γ-integrand with positive rate). -/
lemma memLp_two_exp (α : ℝ) (hα : -1 < α) {c : ℝ} (hc : c < 1 / 2) :
    MemLp (fun x => Real.exp (c * x)) 2 (laguerreMeasure α) := by
  -- MemLp (e^{cx}) 2 μ_α  ⟺  Integrable |e^{cx}|² = e^{2cx} wrt μ_α
  --                       ⟺  Integrable (w · e^{2cx}) wrt volume,
  -- and on (0,∞) this is `xᵃ e^{-x} · e^{2cx} = xᵃ e^{-(1-2c)x}`, the scaled Γ-integrand
  -- (`integrableOn_rpow_mul_exp_neg_mul_rpow`, exponent `b = 1-2c > 0`), vanishing off (0,∞).
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (c * x)) (laguerreMeasure α) :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (c * x)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas, laguerreMeasure,
      integrable_withDensity_iff_integrable_smul₀'
        (measurable_laguerreWeight α).ennreal_ofReal.aemeasurable
        (.of_forall fun x => ENNReal.ofReal_lt_top)]
  set b : ℝ := 1 - 2 * c with hb
  have hb_pos : 0 < b := by rw [hb]; linarith
  -- Scaled Γ-integrand: `xᵃ · e^{-b·x}` is integrable on (0,∞).
  have hbrick : IntegrableOn
      (fun x : ℝ => x ^ α * Real.exp (-b * x ^ (1 : ℝ))) (Set.Ioi 0) volume :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hα (le_refl (1 : ℝ)) hb_pos
  -- `w·e^{2cx}` agrees with the Γ-integrand on (0,∞) and vanishes off it.
  have hexp : ∀ x : ℝ, Real.exp (-x) * Real.exp (c * x) ^ 2 = Real.exp (-b * x) := by
    intro x
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hb]; ring
  have hsupp : (fun x : ℝ => laguerreWeight α x * Real.exp (c * x) ^ 2)
      = (Set.Ioi 0).indicator (fun x : ℝ => x ^ α * Real.exp (-b * x ^ (1 : ℝ))) := by
    funext x
    rw [Set.indicator_apply]
    split_ifs with hx
    · rw [Set.mem_Ioi] at hx
      simp only [laguerreWeight, if_pos hx, Real.rpow_one]
      rw [mul_assoc, hexp]
    · rw [Set.mem_Ioi] at hx
      simp only [laguerreWeight, if_neg hx, zero_mul]
  have hInt : Integrable (fun x : ℝ => laguerreWeight α x * Real.exp (c * x) ^ 2) volume := by
    rw [hsupp]
    exact (integrable_indicator_iff measurableSet_Ioi).2 hbrick
  refine hInt.congr (.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (laguerreWeight_nonneg' α x)]

/-- The exponentially tilted function `w · f · e^{c·}` is integrable for `c < 1/2`,
where `w = laguerreWeight α`. In particular (`c = 0`) `w · f` is integrable. -/
lemma g_tilt_integrable (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α)) {c : ℝ} (hc : c < 1 / 2) :
    Integrable (fun x => (laguerreWeight α x * f x) * Real.exp (c * x)) := by
  -- f · e^{c·} ∈ L¹(μ_α) by Hölder (both in L²(μ_α)); convert to volume.
  have hL1 : MemLp (fun x => f x * Real.exp (c * x)) 1 (laguerreMeasure α) :=
    (memLp_two_exp α hα hc).mul' hf        -- HolderTriple 2 2 1; `.mul'` puts the receiver second
  have hInt : Integrable (fun x => f x * Real.exp (c * x)) (laguerreMeasure α) :=
    (memLp_one_iff_integrable).1 hL1
  -- Integrable wrt withDensity ⟺ Integrable of the `toReal`-smul wrt volume:
  rw [laguerreMeasure,
      integrable_withDensity_iff_integrable_smul₀'
        (measurable_laguerreWeight α).ennreal_ofReal.aemeasurable
        (.of_forall fun x => ENNReal.ofReal_lt_top)] at hInt
  refine hInt.congr (.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (laguerreWeight_nonneg' α x)]
  ring

/-- The weighted function `w · f` is Lebesgue-integrable whenever `f ∈ L²(μ_α)`
(the `c = 0` case of `g_tilt_integrable`). -/
lemma g_integrable (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α)) :
    Integrable (fun x => laguerreWeight α x * f x) := by
  have h := g_tilt_integrable α hα f hf (c := 0) (by norm_num)
  simpa using h

/-! ### The complex Laplace/Fourier transform and its analytic properties -/

/-- The open strip `{Re z < 1/2}`; convex hence preconnected, open, contains `0`. -/
def strip : Set ℂ := {z : ℂ | z.re < 1 / 2}

/-- The strip `{Re z < 1/2}` is open. -/
lemma isOpen_strip : IsOpen strip := isOpen_lt Complex.continuous_re continuous_const

/-- The strip `{Re z < 1/2}` is convex (an open half-space for the linear map `Re`). -/
lemma convex_strip : Convex ℝ strip :=
  -- `strip = {z | z.re < 1/2}` is a half-space for the ℝ-linear map `Complex.re`.
  convex_halfSpace_lt Complex.reLm.isLinear (1 / 2)
/-- `0` lies in the strip `{Re z < 1/2}`. -/
lemma zero_mem_strip : (0 : ℂ) ∈ strip := by simp [strip]

/-- The two-sided Laplace transform `∫ w(x) · f(x) · e^{z x} dx` of the weighted
function `w · f`, where `w = laguerreWeight α`. -/
noncomputable def laplaceTr (α : ℝ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, ((laguerreWeight α x : ℂ) * (f x : ℂ)) * Complex.exp (z * (x : ℂ))

/-- The transform `laplaceTr α f` is holomorphic on the strip `{Re z < 1/2}`. -/
lemma laplaceTr_differentiableOn (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α)) :
    DifferentiableOn ℂ (laplaceTr α f) strip := by
  -- Work with `g = w·f`, which is genuinely integrable, and `g·e^{c·}` for every `c < 1/2`.
  have hgint : Integrable (fun x => laguerreWeight α x * f x) := g_integrable α hα f hf
  have hgC : AEStronglyMeasurable (fun x : ℝ => ((laguerreWeight α x * f x : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hgint.aestronglyMeasurable
  -- `g` vanishes off `(0,∞)`.
  have hg_zero : ∀ x : ℝ, x ≤ 0 → laguerreWeight α x * f x = 0 := by
    intro x hx
    simp only [laguerreWeight, if_neg (not_lt.2 hx), zero_mul]
  -- Norm of the coefficient `(w·f : ℂ)`.
  have hnorm_coef : ∀ x : ℝ,
      ‖(laguerreWeight α x : ℂ) * (f x : ℂ)‖ = |laguerreWeight α x * f x| := by
    intro x
    rw [show (laguerreWeight α x : ℂ) * (f x : ℂ) = ((laguerreWeight α x * f x : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
  -- Norms of the integrand `F` and its `z`-derivative `F'`.
  have hnormF : ∀ (z : ℂ) (x : ℝ),
      ‖(laguerreWeight α x : ℂ) * (f x : ℂ) * Complex.exp (z * x)‖
        = |laguerreWeight α x * f x| * Real.exp (z.re * x) := by
    intro z x
    rw [norm_mul, hnorm_coef x, Complex.norm_exp,
        show (z * (x : ℂ)).re = z.re * x by simp [Complex.mul_re]]
  have hnormF' : ∀ (z : ℂ) (x : ℝ),
      ‖(laguerreWeight α x : ℂ) * (f x : ℂ) * (Complex.exp (z * x) * (x : ℂ))‖
        = |laguerreWeight α x * f x| * Real.exp (z.re * x) * |x| := by
    intro z x
    rw [norm_mul, hnorm_coef x, norm_mul, Complex.norm_exp,
        show (z * (x : ℂ)).re = z.re * x by simp [Complex.mul_re],
        Complex.norm_real, Real.norm_eq_abs]
    ring
  -- The cast `(w x : ℂ)(f x : ℂ) = ((w x * f x : ℝ) : ℂ)`, threaded through the integrand.
  have hcoefC : ∀ z : ℂ,
      (fun x : ℝ => (laguerreWeight α x : ℂ) * (f x : ℂ) * Complex.exp (z * x))
        = (fun x : ℝ => ((laguerreWeight α x * f x : ℝ) : ℂ) * Complex.exp (z * x)) := by
    intro z; funext x; push_cast; ring
  have hFaesm : ∀ z : ℂ, AEStronglyMeasurable
      (fun x : ℝ => (laguerreWeight α x : ℂ) * (f x : ℂ) * Complex.exp (z * x)) volume := by
    intro z
    rw [hcoefC z]
    exact hgC.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  -- Monotonicity of the majorant in the exponent (using that `g` vanishes for `x ≤ 0`).
  have hbnd_le : ∀ (x : ℝ) {a b : ℝ}, a ≤ b →
      |laguerreWeight α x * f x| * Real.exp (a * x)
        ≤ |laguerreWeight α x * f x| * Real.exp (b * x) := by
    intro x a b hab
    rcases le_or_gt x 0 with hx | hx
    · simp [hg_zero x hx]
    · exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hab hx.le)) (abs_nonneg _)
  -- Now fix a point of the (open) strip and prove differentiability there.
  intro z₀ hz₀
  apply DifferentiableAt.differentiableWithinAt
  have hz0 : z₀.re < 1 / 2 := hz₀
  obtain ⟨c₁, hz0c1, hc1half⟩ : ∃ c, z₀.re < c ∧ c < 1 / 2 :=
    ⟨(z₀.re + 1 / 2) / 2, by linarith, by linarith⟩
  obtain ⟨c₂, hc1c2, hc2half⟩ : ∃ c, c₁ < c ∧ c < 1 / 2 :=
    ⟨(c₁ + 1 / 2) / 2, by linarith, by linarith⟩
  have hd_pos : 0 < c₂ - c₁ := by linarith
  -- tilt integrability of the real majorants `|g| e^{c·}`.
  have htilt : ∀ c : ℝ, c < 1 / 2 →
      Integrable (fun x => |laguerreWeight α x * f x| * Real.exp (c * x)) := by
    intro c hc
    refine (g_tilt_integrable α hα f hf hc).norm.congr (.of_forall fun x => ?_)
    simp [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  have htilt1 : Integrable (fun x => |laguerreWeight α x * f x| * Real.exp (c₁ * x)) :=
    htilt c₁ hc1half
  have htilt2 : Integrable (fun x => |laguerreWeight α x * f x| * Real.exp (c₂ * x)) :=
    htilt c₂ hc2half
  -- The data for the parametric-integral theorem.
  set s : Set ℂ := {z : ℂ | z.re < c₁} with hs_def
  set bound : ℝ → ℝ :=
    fun x => (1 / (c₂ - c₁)) * (|laguerreWeight α x * f x| * Real.exp (c₂ * x)) with hbound_def
  set F : ℂ → ℝ → ℂ :=
    fun z x => (laguerreWeight α x : ℂ) * (f x : ℂ) * Complex.exp (z * x) with hF_def
  set F' : ℂ → ℝ → ℂ :=
    fun z x => (laguerreWeight α x : ℂ) * (f x : ℂ) * (Complex.exp (z * x) * (x : ℂ)) with hF'_def
  have hs_nhds : s ∈ 𝓝 z₀ := by
    rw [hs_def]; exact (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz0c1
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) volume :=
    Filter.Eventually.of_forall (fun z => by rw [hF_def]; exact hFaesm z)
  have hF_int : Integrable (F z₀) volume := by
    simp only [hF_def]
    refine Integrable.mono' htilt1 (hFaesm z₀) (Filter.Eventually.of_forall fun x => ?_)
    simp only [hnormF]; exact hbnd_le x hz0c1.le
  have hF'aesm : AEStronglyMeasurable (F' z₀) volume := by
    simp only [hF'_def,
        show (fun x : ℝ => (laguerreWeight α x : ℂ) * (f x : ℂ) * (Complex.exp (z₀ * x) * (x : ℂ)))
            = (fun x : ℝ => ((laguerreWeight α x * f x : ℝ) : ℂ) * (Complex.exp (z₀ * x) * (x : ℂ)))
          from by funext x; push_cast; ring]
    exact hgC.mul (by fun_prop : Continuous
      (fun x : ℝ => Complex.exp (z₀ * x) * (x : ℂ))).aestronglyMeasurable
  have hF'_bound : ∀ᵐ a ∂(volume : Measure ℝ), ∀ z ∈ s, ‖F' z a‖ ≤ bound a := by
    refine Filter.Eventually.of_forall (fun x z hz => ?_)
    rw [hs_def, Set.mem_setOf_eq] at hz
    simp only [hF'_def, hbound_def, hnormF']
    rcases le_or_gt x 0 with hx | hx
    · simp [hg_zero x hx]
    · rw [abs_of_pos hx]
      have hxexp : x * Real.exp (c₁ * x) ≤ (1 / (c₂ - c₁)) * Real.exp (c₂ * x) := by
        have hdx : (c₂ - c₁) * x ≤ Real.exp ((c₂ - c₁) * x) := by
          have := Real.add_one_le_exp ((c₂ - c₁) * x); linarith
        have h1 : x * Real.exp (c₁ * x) * (c₂ - c₁) ≤ Real.exp (c₂ * x) :=
          calc x * Real.exp (c₁ * x) * (c₂ - c₁)
              = (c₂ - c₁) * x * Real.exp (c₁ * x) := by ring
            _ ≤ Real.exp ((c₂ - c₁) * x) * Real.exp (c₁ * x) :=
                mul_le_mul_of_nonneg_right hdx (Real.exp_pos _).le
            _ = Real.exp (c₂ * x) := by rw [← Real.exp_add]; congr 1; ring
        rw [show (1 / (c₂ - c₁)) * Real.exp (c₂ * x) = Real.exp (c₂ * x) / (c₂ - c₁) by ring,
            le_div_iff₀ hd_pos]
        exact h1
      calc |laguerreWeight α x * f x| * Real.exp (z.re * x) * x
          ≤ |laguerreWeight α x * f x| * Real.exp (c₁ * x) * x := by
            apply mul_le_mul_of_nonneg_right _ hx.le
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hz.le hx.le)) (abs_nonneg _)
        _ = |laguerreWeight α x * f x| * (x * Real.exp (c₁ * x)) := by ring
        _ ≤ |laguerreWeight α x * f x| * ((1 / (c₂ - c₁)) * Real.exp (c₂ * x)) :=
            mul_le_mul_of_nonneg_left hxexp (abs_nonneg _)
        _ = (1 / (c₂ - c₁)) * (|laguerreWeight α x * f x| * Real.exp (c₂ * x)) := by ring
  have hbound_int : Integrable bound := by
    rw [hbound_def]; exact htilt2.const_mul (1 / (c₂ - c₁))
  have h_diff : ∀ᵐ a ∂(volume : Measure ℝ), ∀ z ∈ s,
      HasDerivAt (fun z => F z a) (F' z a) z := by
    refine Filter.Eventually.of_forall (fun a z _ => ?_)
    simp only [hF_def, hF'_def]
    have hlin : HasDerivAt (fun w : ℂ => w * (a : ℂ)) (a : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (a : ℂ)
    exact hlin.cexp.const_mul ((laguerreWeight α a : ℂ) * (f a : ℂ))
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs_nhds hF_meas hF_int hF'aesm hF'_bound hbound_int h_diff
  have hlap : laplaceTr α f = fun n => ∫ a, F n a := by
    funext n; simp only [hF_def, laplaceTr]
  rw [hlap]
  exact hderiv.differentiableAt

/-- If all weighted moments of `f` vanish, then `laplaceTr α f` is eventually `0` near `0`. -/
lemma laplaceTr_eventuallyEq_zero (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α))
    (hmom : ∀ k : ℕ, ∫ x, (laguerreWeight α x * f x) * x ^ k = 0) :
    laplaceTr α f =ᶠ[𝓝 0] 0 := by
  -- It suffices to show `laplaceTr α f z = 0` for `‖z‖ < 1/2` (a nbhd of 0):
  -- `g = w·f` complexified is a.e.-strongly measurable, and `g` vanishes off `(0,∞)`.
  have hgC : AEStronglyMeasurable (fun x : ℝ => ((laguerreWeight α x * f x : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (g_integrable α hα f hf).aestronglyMeasurable
  have hgz : ∀ x : ℝ, x ≤ 0 → laguerreWeight α x * f x = 0 := by
    intro x hx; simp only [laguerreWeight, if_neg (not_lt.2 hx), zero_mul]
  have key : ∀ z : ℂ, ‖z‖ < 1 / 2 → laplaceTr α f z = 0 := by
    intro z hz
    -- `e^{zx} = Σ_n (zx)ⁿ/n!`, so the integrand is the `HasSum` of `Fₙ`.
    set F : ℕ → ℝ → ℂ :=
      fun n x => (laguerreWeight α x : ℂ) * (f x : ℂ) * ((z * x) ^ n / (n.factorial : ℂ))
      with hF_def
    set bound : ℕ → ℝ → ℝ :=
      fun n x => |laguerreWeight α x * f x| * ((‖z‖ * |x|) ^ n / (n.factorial : ℝ)) with hb_def
    -- pointwise series expansion of the integrand
    have hlim : ∀ x : ℝ,
        HasSum (fun n => F n x) ((laguerreWeight α x : ℂ) * (f x : ℂ) * Complex.exp (z * x)) := by
      intro x
      have hexp : HasSum (fun n => (z * (x : ℂ)) ^ n / (n.factorial : ℂ))
          (Complex.exp (z * x)) := by
        rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp (z * (x : ℂ))
      simpa only [hF_def, mul_assoc] using hexp.mul_left ((laguerreWeight α x : ℂ) * (f x : ℂ))
    -- norm of `Fₙ` is exactly `boundₙ`
    have hnormFn : ∀ n x, ‖F n x‖ = bound n x := by
      intro n x
      have hreal : F n x
          = ((laguerreWeight α x * f x : ℝ) : ℂ) * ((z * x) ^ n / (n.factorial : ℂ)) := by
        simp only [hF_def]; push_cast; ring
      rw [hreal, hb_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_pow,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_natCast]
    have hsummable : ∀ x : ℝ, Summable (fun n => bound n x) := by
      intro x; simp only [hb_def]
      exact (Real.summable_pow_div_factorial (‖z‖ * |x|)).mul_left _
    -- the dominating series sums to `|g| · e^{‖z‖|x|}`
    have hexpR : ∀ t : ℝ, ∑' n : ℕ, t ^ n / (n.factorial : ℝ) = Real.exp t := by
      intro t; rw [Real.exp_eq_exp_ℝ]; exact (NormedSpace.expSeries_div_hasSum_exp t).tsum_eq
    have htsum : ∀ x : ℝ,
        ∑' n, bound n x = |laguerreWeight α x * f x| * Real.exp (‖z‖ * |x|) := by
      intro x; simp only [hb_def]; rw [tsum_mul_left, hexpR]
    have hbi : Integrable (fun x => ∑' n, bound n x) volume := by
      have heq : (fun x => ∑' n, bound n x)
          = (fun x => |laguerreWeight α x * f x| * Real.exp (‖z‖ * x)) := by
        funext x; rw [htsum x]
        rcases le_or_gt x 0 with hx | hx
        · rw [hgz x hx]; simp
        · rw [abs_of_pos hx]
      rw [heq]
      refine (g_tilt_integrable α hα f hf hz).norm.congr (.of_forall fun x => ?_)
      simp only [norm_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg (‖z‖ * x))]
    have hFmeas : ∀ n, AEStronglyMeasurable (F n) volume := by
      intro n
      simp only [hF_def]
      rw [show (fun x : ℝ =>
            (laguerreWeight α x : ℂ) * (f x : ℂ) * ((z * x) ^ n / (n.factorial : ℂ)))
          = (fun x : ℝ =>
            ((laguerreWeight α x * f x : ℝ) : ℂ) * ((z * x) ^ n / (n.factorial : ℂ)))
          from by funext x; push_cast; ring]
      exact hgC.mul (by fun_prop)
    -- each `∫ Fₙ` vanishes by the moment hypothesis
    have hintFn : ∀ n, ∫ x, F n x = 0 := by
      intro n
      have hcong : ∀ x, F n x
          = (z ^ n / (n.factorial : ℂ)) * (((laguerreWeight α x * f x) * x ^ n : ℝ) : ℂ) := by
        intro x; simp only [hF_def]; push_cast; ring
      calc ∫ x, F n x
          = ∫ x, (z ^ n / (n.factorial : ℂ)) * (((laguerreWeight α x * f x) * x ^ n : ℝ) : ℂ) :=
            integral_congr_ae (.of_forall hcong)
        _ = (z ^ n / (n.factorial : ℂ)) * ∫ x, (((laguerreWeight α x * f x) * x ^ n : ℝ) : ℂ) :=
            integral_const_mul _ _
        _ = (z ^ n / (n.factorial : ℂ)) * ((∫ x, (laguerreWeight α x * f x) * x ^ n : ℝ) : ℂ) := by
            rw [integral_complex_ofReal]
        _ = 0 := by rw [hmom n]; simp
    -- assemble: the transform is the sum of vanishing terms
    have hHS : HasSum (fun n => ∫ x, F n x)
        (∫ x, (laguerreWeight α x : ℂ) * (f x : ℂ) * Complex.exp (z * x)) :=
      hasSum_integral_of_dominated_convergence bound hFmeas
        (fun n => Filter.Eventually.of_forall (fun x => (hnormFn n x).le))
        (Filter.Eventually.of_forall hsummable) hbi (Filter.Eventually.of_forall hlim)
    have h0 : HasSum (fun _ : ℕ => (0 : ℂ))
        (∫ x, (laguerreWeight α x : ℂ) * (f x : ℂ) * Complex.exp (z * x)) := by
      simpa only [hintFn] using hHS
    exact h0.unique hasSum_zero
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0:ℝ) < 1/2)] with z hz
  exact key z (by simpa [Metric.mem_ball, dist_eq_norm] using hz)

/-- By the identity theorem, `laplaceTr α f` vanishes on the whole strip `{Re z < 1/2}`. -/
lemma laplaceTr_eqOn_zero (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α))
    (hmom : ∀ k : ℕ, ∫ x, (laguerreWeight α x * f x) * x ^ k = 0) :
    Set.EqOn (laplaceTr α f) 0 strip := by
  have hAna : AnalyticOnNhd ℂ (laplaceTr α f) strip :=
    (laplaceTr_differentiableOn α hα f hf).analyticOnNhd isOpen_strip
  exact hAna.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    convex_strip.isPreconnected zero_mem_strip
    (laplaceTr_eventuallyEq_zero α hα f hf hmom)

/-! ### An `L¹` function with vanishing Fourier transform is a.e. zero

Proved via characteristic-function extensionality on the positive and negative parts `g⁺, g⁻`. -/

/-- An integrable real function whose Fourier transform vanishes identically is a.e. zero.
Proved by characteristic-function extensionality applied to the positive and negative parts. -/
lemma ae_zero_of_fourier_zero (g : ℝ → ℝ) (hg : Integrable g)
    (h : ∀ t : ℝ, ∫ x : ℝ, (g x : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) = 0) :
    g =ᵐ[volume] 0 := by
  -- Split g = g⁺ - g⁻, build finite measures μ± = volume.withDensity (ofReal ∘ g±).
  set gp : ℝ → ℝ := fun x => max (g x) 0
  set gn : ℝ → ℝ := fun x => max (-g x) 0
  have hgp : Integrable gp := hg.pos_part
  have hgn : Integrable gn := hg.neg.pos_part
  set μp : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (gp x))
  set μn : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (gn x))
  haveI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hgp.hasFiniteIntegral
  haveI : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hgn.hasFiniteIntegral
  -- charFun μ± t = ∫ exp(⟪x,t⟫ I) dμ± = ∫ g±(x) exp(x t I) dx   (toReal-smul + ⟪x,t⟫_ℝ = x*t).
  have hμ : μp = μn := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    -- `g·e^{itx} ∈ L¹` for any integrable `g`, since `‖e^{itx}‖ = 1`.
    have hI : ∀ w : ℝ → ℝ, Integrable w →
        Integrable (fun x => (w x : ℂ) * Complex.exp (↑t * ↑x * Complex.I)) := by
      intro w hw
      refine Integrable.mono' hw.norm
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul
          (by fun_prop)) (.of_forall fun x => le_of_eq ?_)
      rw [norm_mul, Complex.norm_exp, Complex.norm_real,
          show (↑t * ↑x * Complex.I).re = 0 from by simp [Complex.mul_re, Complex.mul_im],
          Real.exp_zero, mul_one]
    -- `charFun` of a `withDensity` measure as a weighted Lebesgue integral.
    have hp : charFun μp t = ∫ x, (gp x : ℂ) * Complex.exp (↑t * ↑x * Complex.I) := by
      rw [charFun_apply_real]; simp only [μp]
      rw [integral_withDensity_eq_integral_toReal_smul₀ hgp.aemeasurable.ennreal_ofReal
            (.of_forall fun x => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp only [gp]
      rw [Complex.real_smul, ENNReal.toReal_ofReal (le_max_right _ _)]
    have hn : charFun μn t = ∫ x, (gn x : ℂ) * Complex.exp (↑t * ↑x * Complex.I) := by
      rw [charFun_apply_real]; simp only [μn]
      rw [integral_withDensity_eq_integral_toReal_smul₀ hgn.aemeasurable.ennreal_ofReal
            (.of_forall fun x => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp only [gn]
      rw [Complex.real_smul, ENNReal.toReal_ofReal (le_max_right _ _)]
    rw [hp, hn]
    -- `gp = gn + g`, so the `gp`-integral splits; the `g`-piece is `0` by `h`.
    have hcombine : (fun x => (gp x : ℂ) * Complex.exp (↑t * ↑x * Complex.I))
        = (fun x => (gn x : ℂ) * Complex.exp (↑t * ↑x * Complex.I)
                    + (g x : ℂ) * Complex.exp (↑t * ↑x * Complex.I)) := by
      funext x
      have hr : gp x = gn x + g x := by
        simp only [gp, gn]
        rcases le_total 0 (g x) with hx | hx
        · rw [max_eq_left hx, max_eq_right (by linarith : -g x ≤ 0)]; ring
        · rw [max_eq_right hx, max_eq_left (by linarith : (0 : ℝ) ≤ -g x)]; ring
      rw [show (gp x : ℂ) = (gn x : ℂ) + (g x : ℂ) by rw [hr]; push_cast; ring]; ring
    have hg0 : (∫ x, (g x : ℂ) * Complex.exp (↑t * ↑x * Complex.I)) = 0 := by
      rw [← h t]
      refine integral_congr_ae (.of_forall fun x => ?_)
      have hcomm : (↑t * ↑x * Complex.I) = Complex.I * ↑t * ↑x := by ring
      simp only [hcomm]
    rw [hcombine, integral_add (hI gn hgn) (hI g hg), hg0, add_zero]
  -- equal withDensity ⟹ equal densities a.e. ⟹ gp =ᵐ gn ⟹ g =ᵐ 0.
  have hden : (fun x => ENNReal.ofReal (gp x)) =ᵐ[volume] (fun x => ENNReal.ofReal (gn x)) :=
    -- `volume` on ℝ is σ-finite, so equal `withDensity` measures have a.e.-equal densities.
    (withDensity_eq_iff_of_sigmaFinite
      hgp.aemeasurable.ennreal_ofReal hgn.aemeasurable.ennreal_ofReal).1 hμ
  -- ofReal gp = ofReal gn a.e.  ⟹  gp = gn a.e. (both ≥ 0)  ⟹  g = gp - gn = 0 a.e.
  filter_upwards [hden] with x hx
  have : gp x = gn x := by
    have := (ENNReal.ofReal_eq_ofReal_iff (le_max_right _ _) (le_max_right _ _)).1 hx
    simpa using this
  -- g x = gp x - gn x = 0
  simp only [gp, gn] at this ⊢
  have : max (g x) 0 = max (-g x) 0 := this
  -- max(a,0) = max(-a,0) ⟹ a = 0
  rcases le_or_gt 0 (g x) with hpos | hneg
  · have : g x = 0 := by
      have h1 : max (g x) 0 = g x := max_eq_left hpos
      have h2 : max (-g x) 0 = 0 := max_eq_right (by linarith)
      rw [h1, h2] at this; exact this
    simpa using this
  · exfalso
    have h1 : max (g x) 0 = 0 := max_eq_right hneg.le
    have h2 : max (-g x) 0 = -g x := max_eq_left (by linarith)
    rw [h1, h2] at this; linarith

/-! ### Transfer back to `μ_α`: `w · f = 0` a.e.`[volume]` ⟹ `f = 0` a.e.`[μ_α]`

This uses that `w > 0` on `(0, ∞)`. -/

/-- If the weighted function `w · f` vanishes a.e. `[volume]`, then `f` vanishes a.e. `[μ_α]`,
since `w > 0` on the support `(0,∞)` of `μ_α`. -/
lemma ae_zero_laguerreMeasure_of_g_ae_zero (α : ℝ) (f : ℝ → ℝ)
    (hg : (fun x => laguerreWeight α x * f x) =ᵐ[volume] 0) :
    f =ᵐ[laguerreMeasure α] 0 := by
  -- μ_α = withDensity (ofReal w).  `f =ᵐ[μ_α] 0` ⟺ ∀ᵐ x ∂volume, ofReal(w x) ≠ 0 → f x = 0.
  rw [laguerreMeasure, EventuallyEq,
      ae_withDensity_iff (measurable_laguerreWeight α).ennreal_ofReal]
  filter_upwards [hg] with x hx hwpos
  -- ofReal (w x) ≠ 0 ⟹ w x > 0 ⟹ (on supp) w x * f x = 0 forces f x = 0
  have hw : 0 < laguerreWeight α x := by
    rw [ENNReal.ofReal_ne_zero_iff] at hwpos
    exact hwpos
  have : laguerreWeight α x * f x = 0 := hx
  exact (mul_eq_zero.1 this).resolve_left hw.ne'

/-! ### Completeness: assembling the main theorem -/

/-- **Completeness of the associated Laguerre polynomials in `L²(μ_α)`.**
For `α > -1`, any `f ∈ L²(ℝ⁺, xᵅ e⁻ˣ dx)` orthogonal to every `Lₙ^{(α)}` is a.e. zero;
equivalently, `{Lₙ^{(α)}}ₙ` is a complete orthogonal system. Proved via the moment problem:
vanishing moments make the two-sided Laplace transform of `w · f` vanish on the strip
`{Re z < 1/2}`, hence its Fourier transform vanishes on the imaginary axis, forcing `w · f = 0`
a.e. and thus `f = 0` a.e. `[μ_α]`. -/
theorem laguerre_complete (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α))
    (hortho : ∀ n : ℕ, ∫ x, f x * laguerrePolynomial n α x ∂(laguerreMeasure α) = 0) :
    f =ᵐ[laguerreMeasure α] 0 := by
  -- moments of g := w·f all vanish
  have hmom := g_moments_zero α hα f hf hortho
  -- G ≡ 0 on the strip ⟹ on the imaginary axis
  have hEq := laplaceTr_eqOn_zero α hα f hf hmom
  have hfourier : ∀ t : ℝ,
      ∫ x : ℝ, ((laguerreWeight α x : ℂ) * (f x : ℂ)) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) = 0 := by
    intro t
    have hmem : (Complex.I * (t : ℂ)) ∈ strip := by
      simp [strip]      -- (I * t).re = 0 < 1/2
    have := hEq hmem
    -- `laplaceTr α f (I*t) = ∫ g(x) exp((I*t)·x)`; match exp argument with `I*t*x`
    simpa [laplaceTr, mul_assoc] using this
  -- Fourier transform ≡ 0 ⟹ g = 0 a.e.
  have hg0 : (fun x => laguerreWeight α x * f x) =ᵐ[volume] 0 :=
    ae_zero_of_fourier_zero _ (g_integrable α hα f hf)
      (by
        intro t
        have := hfourier t
        -- reconcile `(↑(w x) * ↑(f x))` with `↑(w x * f x)`
        simpa [Complex.ofReal_mul] using this)
  -- transfer to μ_α
  exact ae_zero_laguerreMeasure_of_g_ae_zero α f hg0

end Spectra.QuantumMechanics.Hydrogen.Radial

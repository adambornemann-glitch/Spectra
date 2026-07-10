/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Reduced

/-!
# Radial Bound-State Uniqueness

The tail asymptotics and Wronskian argument identifying every negative-energy
classical radial bound state with a scalar multiple of the explicit Laguerre eigenfunction.

## Main definitions

This file introduces only private auxiliary functions for the uniqueness proof.

## Main statements

* `bound_state_eq_smul_eigenfunction` — fixed-energy radial eigenspaces are one-dimensional.
* `radial_bound_state_unique` — negative-energy bound states are zero or explicit eigenfunctions.
* `radialWavefunction_1s`, `radialWavefunction_2s`, `radialWavefunction_2p` — small-state formulas.

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I*][schrodinger1926]
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957]
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

open MeasureTheory Complex Filter Real
open scoped Topology NNReal ENNReal Nat
open Spectra.QuantumMechanics.Hydrogen.Radial
open Spectra.Kummer

namespace QuantumMechanics.Hydrogen.RadialEq

/-! ## One-dimensionality of the radial eigenspace (analytic core) -/

/-! ## Laguerre at-∞ two-sided asymptotic bound -/

/-- Coefficient of `x^k` in `laguerrePolynomial p α`. -/
private noncomputable def lagCoeff (p : ℕ) (α : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * realBinom (p + α) (p - k) / (k.factorial : ℝ)

/-- Expansion of the Laguerre polynomial as a power series with coefficients `lagCoeff`. -/
private lemma laguerre_eq_sum_coeff (p : ℕ) (α : ℝ) (x : ℝ) :
    laguerrePolynomial p α x = ∑ k ∈ Finset.range (p + 1), lagCoeff p α k * x ^ k := by
  rw [laguerrePolynomial]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lagCoeff]; ring

/-- The top (degree-`p`) coefficient of `laguerrePolynomial p α` is `(-1)^p / p!`. -/
private lemma lagCoeff_leading (p : ℕ) (α : ℝ) :
    lagCoeff p α p = (-1 : ℝ) ^ p / (p.factorial : ℝ) := by
  rw [lagCoeff, Nat.sub_self, realBinom_zero, mul_one]

/-- Two-sided asymptotic: `(|cL|/2)·x^p ≤ |L_p^α(x)| ≤ (|cL|+M)·x^p` for `x` large,
where `cL = (-1)^p/p!` is the leading coefficient. -/
private lemma laguerre_asymptotic (p : ℕ) (α : ℝ) :
    ∃ x₀ c C : ℝ, 1 ≤ x₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ x, x₀ ≤ x → c * x ^ p ≤ |laguerrePolynomial p α x|
        ∧ |laguerrePolynomial p α x| ≤ C * x ^ p := by
  set cL := (-1 : ℝ) ^ p / (p.factorial : ℝ) with hcL
  have hcLpos : 0 < |cL| := by
    rw [hcL, abs_div, abs_pow, abs_neg, abs_one, one_pow]
    positivity
  set M := ∑ k ∈ Finset.range p, |lagCoeff p α k| with hM
  have hMnn : 0 ≤ M := Finset.sum_nonneg (fun k _ => abs_nonneg _)
  -- decomposition into tail + leading term
  have hrw : ∀ x : ℝ, laguerrePolynomial p α x
      = (∑ k ∈ Finset.range p, lagCoeff p α k * x ^ k) + cL * x ^ p := by
    intro x
    rw [laguerre_eq_sum_coeff, Finset.sum_range_succ, lagCoeff_leading]
  -- tail bound
  have htail : ∀ x : ℝ, 1 ≤ x →
      |∑ k ∈ Finset.range p, lagCoeff p α k * x ^ k| ≤ M * x ^ (p - 1) := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
    calc |∑ k ∈ Finset.range p, lagCoeff p α k * x ^ k|
        ≤ ∑ k ∈ Finset.range p, |lagCoeff p α k * x ^ k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range p, |lagCoeff p α k| * x ^ k := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 k)]
      _ ≤ ∑ k ∈ Finset.range p, |lagCoeff p α k| * x ^ (p - 1) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hkp : k ≤ p - 1 := by
            rw [Finset.mem_range] at hk; omega
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hkp) (abs_nonneg _)
      _ = M * x ^ (p - 1) := by rw [hM, Finset.sum_mul]
  refine ⟨max 1 (2 * M / |cL|), |cL| / 2, |cL| + M, le_max_left _ _, by positivity,
    by positivity, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx1
  have hx2M : 2 * M / |cL| ≤ x := le_trans (le_max_right _ _) hx
  have hpowmono : x ^ (p - 1) ≤ x ^ p := pow_le_pow_right₀ hx1 (Nat.sub_le p 1)
  have htx := htail x hx1
  have hL := hrw x
  have hkey : M * x ^ (p - 1) ≤ (|cL| / 2) * x ^ p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      have hM0 : M = 0 := by rw [hM]; simp
      rw [hM0, zero_mul]; positivity
    · have hxp : x ^ p = x ^ (p - 1) * x := by rw [← pow_succ]; congr 1; omega
      rw [hxp]
      have hMx : M ≤ |cL| / 2 * x := by
        rw [div_le_iff₀ hcLpos] at hx2M
        nlinarith [hx2M, hcLpos]
      nlinarith [hMx, pow_nonneg hx0 (p - 1), hMnn]
  constructor
  · -- lower bound
    have htri := abs_add_le (laguerrePolynomial p α x)
      (-(∑ k ∈ Finset.range p, lagCoeff p α k * x ^ k))
    rw [abs_neg, show laguerrePolynomial p α x +
        -(∑ k ∈ Finset.range p, lagCoeff p α k * x ^ k) = cL * x ^ p from by rw [hL]; ring,
      abs_mul, abs_of_nonneg (pow_nonneg hx0 p)] at htri
    nlinarith [htri, htx, hkey]
  · -- upper bound
    calc |laguerrePolynomial p α x|
        = |(∑ k ∈ Finset.range p, lagCoeff p α k * x ^ k) + cL * x ^ p| := by rw [hL]
      _ ≤ |∑ k ∈ Finset.range p, lagCoeff p α k * x ^ k| + |cL * x ^ p| := abs_add_le _ _
      _ ≤ M * x ^ (p - 1) + |cL| * x ^ p := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 p)]; linarith [htx]
      _ ≤ M * x ^ p + |cL| * x ^ p := by
          have : M * x ^ (p - 1) ≤ M * x ^ p := mul_le_mul_of_nonneg_left hpowmono hMnn
          linarith
      _ = (|cL| + M) * x ^ p := by ring



/-! ## χ_R = r·R_{nℓ} two-sided tail bound -/

/-- Two-sided tail bound for the reduced eigenfunction: for `r` large,
`c·rⁿe^{-r/n} ≤ |r·R_{nℓ}(r)| ≤ C·rⁿe^{-r/n}` and `r·R_{nℓ}(r) ≠ 0`. The estimate comes
from the leading-term Laguerre asymptotics (`laguerre_asymptotic`). -/
private lemma chiR_tail_bounds (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ∃ r₂ c C : ℝ, 0 < r₂ ∧ 0 < c ∧ 0 < C ∧ ∀ r, r₂ ≤ r →
      c * (r ^ n * Real.exp (-r / n)) ≤ |r * hydrogenRadialWavefunction n ℓ hn r| ∧
      |r * hydrogenRadialWavefunction n ℓ hn r| ≤ C * (r ^ n * Real.exp (-r / n)) ∧
      r * hydrogenRadialWavefunction n ℓ hn r ≠ 0 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have _hf1 : (0:ℝ) < ((n - ℓ - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have _hf2 : (0:ℝ) < ((n + ℓ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hNpos : 0 < radialNormalization n ℓ hn := by
    rw [radialNormalization, Real.sqrt_pos]; positivity
  obtain ⟨x₀, cl, Cl, _hx₀1, hclpos, hClpos, hbnd⟩ :=
    laguerre_asymptotic (n - ℓ - 1) (2 * (ℓ:ℝ) + 1)
  set N := radialNormalization n ℓ hn with _hNdef
  set c : ℝ := N * cl * (2 / (n:ℝ)) ^ (n - 1) with hcdef
  set C : ℝ := N * Cl * (2 / (n:ℝ)) ^ (n - 1) with hCdef
  refine ⟨max 1 (n * x₀ / 2), c, C, lt_of_lt_of_le one_pos (le_max_left _ _),
    by positivity, by positivity, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have _hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
  have hge : n * x₀ / 2 ≤ r := le_trans (le_max_right _ _) hr
  have h2rn : x₀ ≤ 2 * r / n := by
    rw [le_div_iff₀ hn0]; nlinarith [hge, hn0]
  obtain ⟨hLlb, hLub⟩ := hbnd (2 * r / n) h2rn
  -- exponent bookkeeping
  have hrn : r ^ n = r ^ (ℓ + 1) * r ^ (n - ℓ - 1) := by rw [← pow_add]; congr 1; omega
  have hbn : ((2:ℝ) / n) ^ (n - 1) = (2 / n) ^ ℓ * (2 / n) ^ (n - ℓ - 1) := by
    rw [← pow_add]; congr 1; omega
  have h2rp : (2 * r / (n:ℝ)) ^ (n - ℓ - 1) = (2 / n) ^ (n - ℓ - 1) * r ^ (n - ℓ - 1) := by
    rw [← mul_pow]; congr 1; ring
  -- |χ_R r| = P * |L(2r/n)| with P > 0
  set P : ℝ := N * (2 / (n:ℝ)) ^ ℓ * r ^ (ℓ + 1) * Real.exp (-r / n) with hPdef
  have hPpos : 0 < P := by rw [hPdef]; positivity
  have hχ_eq : r * hydrogenRadialWavefunction n ℓ hn r
      = P * laguerrePolynomial (n - ℓ - 1) (2 * (ℓ:ℝ) + 1) (2 * r / n) := by
    rw [hydrogenRadialWavefunction, hPdef,
      show (2 * r / (n:ℝ)) ^ ℓ = (2 / n) ^ ℓ * r ^ ℓ from by rw [← mul_pow]; congr 1; ring]
    ring
  have hχ_abs : |r * hydrogenRadialWavefunction n ℓ hn r|
      = P * |laguerrePolynomial (n - ℓ - 1) (2 * (ℓ:ℝ) + 1) (2 * r / n)| := by
    rw [hχ_eq, abs_mul, abs_of_pos hPpos]
  -- algebraic identities tying c,C to P
  have hceq : c * (r ^ n * Real.exp (-r / n)) = P * (cl * (2 * r / n) ^ (n - ℓ - 1)) := by
    rw [hcdef, hrn, hbn, h2rp, hPdef]; ring
  have hCeq : C * (r ^ n * Real.exp (-r / n)) = P * (Cl * (2 * r / n) ^ (n - ℓ - 1)) := by
    rw [hCdef, hrn, hbn, h2rp, hPdef]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hχ_abs, hceq]
    exact mul_le_mul_of_nonneg_left hLlb (le_of_lt hPpos)
  · rw [hχ_abs, hCeq]
    exact mul_le_mul_of_nonneg_left hLub (le_of_lt hPpos)
  · have hposbound : 0 < c * (r ^ n * Real.exp (-r / n)) := by rw [hcdef]; positivity
    rw [← abs_pos, hχ_abs]
    calc (0:ℝ) < c * (r ^ n * Real.exp (-r / n)) := hposbound
      _ = P * (cl * (2 * r / n) ^ (n - ℓ - 1)) := hceq
      _ ≤ P * |laguerrePolynomial (n - ℓ - 1) (2 * (ℓ:ℝ) + 1) (2 * r / n)| :=
          mul_le_mul_of_nonneg_left hLlb (le_of_lt hPpos)

/-! ## χ_R as reference solution: Wronskian + forward identification -/

/-- The reduced eigenfunction `χ_R = r·R_{nℓ}` as the reference regular solution. -/
private noncomputable def chiR (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ℝ → ℝ :=
  fun s => s * hydrogenRadialWavefunction n ℓ hn s

/-- The reference reduced eigenfunction `χ_R = r·R_{nℓ}` is differentiable on all of `ℝ`. -/
private lemma chiR_differentiable (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Differentiable ℝ (chiR n ℓ hn) := by
  unfold chiR
  exact differentiable_id.mul (differentiable_hydrogenRadial n ℓ hn)

/-- The reference reduced eigenfunction `χ_R = r·R_{nℓ}` is continuous on all of `ℝ`. -/
private lemma chiR_continuous (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : Continuous (chiR n ℓ hn) :=
  (chiR_differentiable n ℓ hn).continuous

/-- Product-rule formula for the derivative of `χ_R = r·R_{nℓ}`:
`(r·R_{nℓ})' = R_{nℓ} + r·R_{nℓ}'`. -/
private lemma chiR_deriv_eq (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (chiR n ℓ hn) = fun s =>
      hydrogenRadialWavefunction n ℓ hn s + s * deriv (hydrogenRadialWavefunction n ℓ hn) s := by
  funext s
  change deriv (fun t => t * hydrogenRadialWavefunction n ℓ hn t) s = _
  exact deriv_reducedMul _ ((differentiable_hydrogenRadial n ℓ hn s).hasDerivAt)

/-- The derivative of `χ_R = r·R_{nℓ}` is itself differentiable, so `χ_R` is `C²`. -/
private lemma chiR_deriv_differentiable (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Differentiable ℝ (deriv (chiR n ℓ hn)) := by
  rw [chiR_deriv_eq]
  exact (differentiable_hydrogenRadial n ℓ hn).add
    (differentiable_id.mul (differentiable_deriv_hydrogenRadial n ℓ hn))

/-- The reference `χ_R = r·R_{nℓ}` solves the reduced Schrödinger-form ODE
`χ'' = (ℓ(ℓ+1)/r² − 2/r + (1/n)²)·χ` on `(0,∞)`. -/
private lemma chiR_solves (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    deriv^[2] (chiR n ℓ hn) r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (n : ℝ)) ^ 2) * chiR n ℓ hn r := by
  unfold chiR
  exact reduced_eigenfunction_solves n ℓ hn hr

/-- The Wronskian `χ·χ_R' − χ'·χ_R` of any solution `χ` of the reduced ODE with the
reference `χ_R` has vanishing derivative at every `r > 0`: since both solve the same
second-order equation, the second-order terms cancel. -/
private lemma wronskian_R_hasDerivAt_zero (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (n : ℝ)) ^ 2) * χ r)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => χ s * deriv (chiR n ℓ hn) s - deriv χ s * chiR n ℓ hn s) 0 r := by
  have hχd : HasDerivAt χ (deriv χ r) r := hχ1 r hr
  have hχd2 : HasDerivAt (deriv χ) (deriv^[2] χ r) r := hχ2 r hr
  have hφd : HasDerivAt (chiR n ℓ hn) (deriv (chiR n ℓ hn) r) r :=
    (chiR_differentiable n ℓ hn r).hasDerivAt
  have hφd2 : HasDerivAt (deriv (chiR n ℓ hn)) (deriv^[2] (chiR n ℓ hn) r) r :=
    (chiR_deriv_differentiable n ℓ hn r).hasDerivAt
  have h1 : HasDerivAt (fun s => χ s * deriv (chiR n ℓ hn) s)
      (deriv χ r * deriv (chiR n ℓ hn) r + χ r * deriv^[2] (chiR n ℓ hn) r) r :=
    hχd.mul hφd2
  have h2 : HasDerivAt (fun s => deriv χ s * chiR n ℓ hn s)
      (deriv^[2] χ r * chiR n ℓ hn r + deriv χ r * deriv (chiR n ℓ hn) r) r :=
    hχd2.mul hφd
  convert h1.sub h2 using 1
  rw [hode r hr, chiR_solves n ℓ hn hr]
  ring

/-- The Wronskian `χ·χ_R' − χ'·χ_R` of any solution `χ` of the reduced ODE with the
reference `χ_R` is constant on `(0,∞)`: it takes the same value at any two positive
points `s` and `r₀`. This is the crux enabling the uniqueness argument. -/
private lemma wronskian_R_const (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (n : ℝ)) ^ 2) * χ r)
    {r₀ s : ℝ} (hr₀ : 0 < r₀) (hs : 0 < s) :
    χ s * deriv (chiR n ℓ hn) s - deriv χ s * chiR n ℓ hn s
      = χ r₀ * deriv (chiR n ℓ hn) r₀ - deriv χ r₀ * chiR n ℓ hn r₀ := by
  set W : ℝ → ℝ := fun s => χ s * deriv (chiR n ℓ hn) s - deriv χ s * chiR n ℓ hn s with hWdef
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := W) (f' := fun _ => (0 : ℝ)) (s := Set.Ioi 0) (C := 0)
    (fun x hx => (wronskian_R_hasDerivAt_zero n ℓ hn χ hχ1 hχ2 hode hx).hasDerivWithinAt)
    (fun x _ => by simp) (convex_Ioi 0) hr₀ (Set.mem_Ioi.2 hs)
  simpa [hWdef, sub_eq_zero] using hb

/-- Forward identification against the χ_R reference. -/
private lemma forward_identification_R (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (n : ℝ)) ^ 2) * χ r)
    (c₀ : ℝ) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (h0 : χ r₁ - c₀ * chiR n ℓ hn r₁ = 0)
    (h0' : deriv χ r₁ - c₀ * deriv (chiR n ℓ hn) r₁ = 0) :
    ∀ r, r₁ ≤ r → χ r = c₀ * chiR n ℓ hn r := by
  intro r hr
  set V : ℝ → ℝ := fun x => (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 - 2 / x + (1 / (n : ℝ)) ^ 2 with hVdef
  set u : ℝ → ℝ := fun s => χ s - c₀ * chiR n ℓ hn s with hudef
  set du : ℝ → ℝ := fun s => deriv χ s - c₀ * deriv (chiR n ℓ hn) s with hdudef
  set F : ℝ → ℝ × ℝ := fun t => (u t, du t) with hFdef
  set M : ℝ := (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r₁ ^ 2 + 2 / r₁ + (1 / (n : ℝ)) ^ 2 with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  set K : ℝ := M + 1 with hKdef
  have hxpos : ∀ x ∈ Set.Icc r₁ r, 0 < x := fun x hx => lt_of_lt_of_le hr₁ hx.1
  have hχcont : ContinuousOn χ (Set.Icc r₁ r) :=
    fun x hx => (hχ1 x (hxpos x hx)).continuousAt.continuousWithinAt
  have hdχcont : ContinuousOn (deriv χ) (Set.Icc r₁ r) :=
    fun x hx => (hχ2 x (hxpos x hx)).continuousAt.continuousWithinAt
  have hφcont : ContinuousOn (chiR n ℓ hn) (Set.Icc r₁ r) :=
    (chiR_continuous n ℓ hn).continuousOn
  have hdφcont : ContinuousOn (deriv (chiR n ℓ hn)) (Set.Icc r₁ r) :=
    (chiR_deriv_differentiable n ℓ hn).continuous.continuousOn
  have hcont : ContinuousOn F (Set.Icc r₁ r) :=
    (hχcont.sub (continuousOn_const.mul hφcont)).prodMk
      (hdχcont.sub (continuousOn_const.mul hdφcont))
  have hderiv : ∀ x ∈ Set.Ico r₁ r, HasDerivWithinAt F (du x, V x * u x) (Set.Ici x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₁ hx.1
    have hud : HasDerivAt u (du x) x :=
      (hχ1 x hx0).sub ((chiR_differentiable n ℓ hn x).hasDerivAt.const_mul c₀)
    have hdud : HasDerivAt du (V x * u x) x := by
      have hb := (hχ2 x hx0).sub
        ((chiR_deriv_differentiable n ℓ hn x).hasDerivAt.const_mul c₀)
      convert hb using 1
      rw [show deriv (deriv (chiR n ℓ hn)) x = deriv^[2] (chiR n ℓ hn) x from rfl,
        hode x hx0, chiR_solves n ℓ hn hx0]
      simp only [hVdef, hudef]
      ring
    exact (hud.prodMk hdud).hasDerivWithinAt
  have hinit : F r₁ = 0 := by
    simp only [hFdef, hudef, hdudef, Prod.mk_eq_zero]
    exact ⟨h0, h0'⟩
  have hbound : ∀ x ∈ Set.Ico r₁ r, ‖(du x, V x * u x)‖ ≤ K * ‖F x‖ := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₁ hx.1
    have hxr₁ : r₁ ≤ x := hx.1
    have hVbound : |V x| ≤ M := by
      have hb1 : 1 / x ^ 2 ≤ 1 / r₁ ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [hxr₁, hr₁])
      have hb2 : 1 / x ≤ 1 / r₁ := one_div_le_one_div_of_le hr₁ hxr₁
      have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) := by positivity
      have h1 : (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r₁ ^ 2 := by
        rw [div_eq_mul_one_div, div_eq_mul_one_div ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) (r₁ ^ 2)]
        exact mul_le_mul_of_nonneg_left hb1 hℓ
      have h2 : (2 : ℝ) / x ≤ 2 / r₁ := by
        rw [div_eq_mul_one_div, div_eq_mul_one_div (2 : ℝ) r₁]
        exact mul_le_mul_of_nonneg_left hb2 (by norm_num)
      have hx2nn : 0 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 := by positivity
      have hr1nn : 0 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r₁ ^ 2 := by positivity
      have h2xpos : 0 < (2 : ℝ) / x := by positivity
      have h2r1pos : 0 < (2 : ℝ) / r₁ := by positivity
      simp only [hVdef, hMdef]
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · linarith [h1, h2, hx2nn, hr1nn, h2xpos, h2r1pos, sq_nonneg (1 / (n : ℝ))]
      · linarith [h1, h2, hx2nn, hr1nn, h2xpos, h2r1pos, sq_nonneg (1 / (n : ℝ))]
    have hFnorm : ‖F x‖ = max |u x| |du x| := by
      rw [hFdef]; simp only [Prod.norm_def, Real.norm_eq_abs]
    have hF'norm : ‖(du x, V x * u x)‖ = max |du x| |V x * u x| := by
      simp only [Prod.norm_def, Real.norm_eq_abs]
    have hmax_nn : 0 ≤ max |u x| |du x| := le_trans (abs_nonneg _) (le_max_left _ _)
    rw [hF'norm, hFnorm]
    apply max_le
    · calc |du x| ≤ max |u x| |du x| := le_max_right _ _
        _ ≤ K * max |u x| |du x| := by rw [hKdef]; nlinarith [mul_nonneg hMnn hmax_nn]
    · rw [abs_mul]
      calc |V x| * |u x| ≤ M * |u x| := mul_le_mul_of_nonneg_right hVbound (abs_nonneg _)
        _ ≤ M * max |u x| |du x| := mul_le_mul_of_nonneg_left (le_max_left _ _) hMnn
        _ ≤ K * max |u x| |du x| := by rw [hKdef]; nlinarith [hmax_nn]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hderiv hinit hbound
  have hFr : F r = 0 := hzero r (Set.right_mem_Icc.2 hr)
  have hur : u r = 0 := by
    have := congrArg Prod.fst hFr
    simpa [hFdef] using this
  rw [hudef] at hur
  linarith

/-! ## At-∞ reduction-of-order integral window -/

/-- Reduction-of-order FTC identity against the χ_R reference (nonzero on the interval). -/
private lemma reduction_order_ftc_R (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    {d : ℝ} (W₀ : ℝ)
    (hW₀ : ∀ s, 0 < s →
      χ s * deriv (chiR n ℓ hn) s - deriv χ s * chiR n ℓ hn s = W₀)
    {r : ℝ} (hr : 0 < r) (hrd : r < d)
    (hne : ∀ x ∈ Set.uIcc r d, chiR n ℓ hn x ≠ 0) :
    χ r - chiR n ℓ hn r * (χ d / chiR n ℓ hn d)
      = W₀ * (chiR n ℓ hn r * ∫ s in r..d, 1 / (chiR n ℓ hn s) ^ 2) := by
  have hrd' : r ≤ d := le_of_lt hrd
  have hxpos : ∀ x ∈ Set.uIcc r d, 0 < x := by
    intro x hx; rw [Set.uIcc_of_le hrd'] at hx; exact lt_of_lt_of_le hr hx.1
  have hφrne : chiR n ℓ hn r ≠ 0 := hne r Set.left_mem_uIcc
  have hφdne : chiR n ℓ hn d ≠ 0 := hne d Set.right_mem_uIcc
  set rawf := fun x => (deriv χ x * chiR n ℓ hn x - χ x * deriv (chiR n ℓ hn) x) /
    (chiR n ℓ hn x) ^ 2 with hrawf
  have hderiv : ∀ x ∈ Set.uIcc r d, HasDerivAt (fun s => χ s / chiR n ℓ hn s) (rawf x) x := by
    intro x hx
    exact (hχ1 x (hxpos x hx)).div ((chiR_differentiable n ℓ hn x).hasDerivAt) (hne x hx)
  have hint : IntervalIntegrable rawf volume r d := by
    rw [hrawf]
    have hχc : ContinuousOn χ (Set.uIcc r d) :=
      fun x hx => (hχ1 x (hxpos x hx)).continuousAt.continuousWithinAt
    have hdχc : ContinuousOn (deriv χ) (Set.uIcc r d) :=
      fun x hx => (hχ2 x (hxpos x hx)).continuousAt.continuousWithinAt
    have hφc : ContinuousOn (chiR n ℓ hn) (Set.uIcc r d) := (chiR_continuous n ℓ hn).continuousOn
    have hdφc : ContinuousOn (deriv (chiR n ℓ hn)) (Set.uIcc r d) :=
      (chiR_deriv_differentiable n ℓ hn).continuous.continuousOn
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div ((hdχc.mul hφc).sub (hχc.mul hdφc)) ((hφc.pow 2))
    intro x hx
    exact pow_ne_zero 2 (hne x hx)
  have hFTC : ∫ s in r..d, rawf s = χ d / chiR n ℓ hn d - χ r / chiR n ℓ hn r :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr : Set.EqOn rawf (fun s => -W₀ * (1 / (chiR n ℓ hn s) ^ 2)) (Set.uIcc r d) := by
    intro s hs
    have hnum : deriv χ s * chiR n ℓ hn s - χ s * deriv (chiR n ℓ hn) s = -W₀ := by
      have := hW₀ s (hxpos s hs); linarith
    rw [hrawf]; simp only; rw [hnum]; ring
  have hΦ : ∫ s in r..d, rawf s = -W₀ * ∫ s in r..d, 1 / (chiR n ℓ hn s) ^ 2 := by
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  rw [hΦ] at hFTC
  have key : χ r - chiR n ℓ hn r * (χ d / chiR n ℓ hn d)
      = chiR n ℓ hn r * (χ r / chiR n ℓ hn r - χ d / chiR n ℓ hn d) := by field_simp
  rw [key, show χ r / chiR n ℓ hn r - χ d / chiR n ℓ hn d
    = W₀ * ∫ s in r..d, 1 / (chiR n ℓ hn s) ^ 2 from by linarith [hFTC]]
  ring

/-- Integral window lower bound: `∫_{r₂}^d 1/χ_R² ≥ 1/(C·dⁿ·e^{-(d-1)/n})²`. -/
private lemma chiR_int_window (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {r₂ C : ℝ} (hCpos : 0 < C)
    (hub : ∀ s, r₂ ≤ s → |chiR n ℓ hn s| ≤ C * (s ^ n * Real.exp (-s / n)))
    (hne : ∀ s, r₂ ≤ s → chiR n ℓ hn s ≠ 0)
    (hr₂pos : 0 < r₂) {d : ℝ} (hd : r₂ + 1 ≤ d) :
    1 / (C * d ^ n * Real.exp (-(d - 1) / n)) ^ 2 ≤ ∫ s in r₂..d, 1 / (chiR n ℓ hn s) ^ 2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdpos : 0 < d := by linarith
  have hd1 : r₂ ≤ d - 1 := by linarith
  have hd1d : d - 1 ≤ d := by linarith
  have hr₂d : r₂ ≤ d := le_trans hd1 hd1d
  set f := fun s => 1 / (chiR n ℓ hn s) ^ 2 with hf
  have hfnn : ∀ s, 0 ≤ f s := fun s => by rw [hf]; positivity
  have hcont : ContinuousOn f (Set.uIcc r₂ d) := by
    rw [hf]
    apply ContinuousOn.div continuousOn_const ((chiR_continuous n ℓ hn).pow 2).continuousOn
    intro s hs
    rw [Set.uIcc_of_le hr₂d] at hs
    exact pow_ne_zero 2 (hne s hs.1)
  have hsub1 : Set.uIcc r₂ (d - 1) ⊆ Set.uIcc r₂ d :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.uIcc_of_le hr₂d]; exact ⟨hd1, hd1d⟩)
  have hsub2 : Set.uIcc (d - 1) d ⊆ Set.uIcc r₂ d :=
    Set.uIcc_subset_uIcc (by rw [Set.uIcc_of_le hr₂d]; exact ⟨hd1, hd1d⟩) Set.right_mem_uIcc
  have hii1 : IntervalIntegrable f volume r₂ (d - 1) := (hcont.mono hsub1).intervalIntegrable
  have hii2 : IntervalIntegrable f volume (d - 1) d := (hcont.mono hsub2).intervalIntegrable
  have hsplit : (∫ s in r₂..(d - 1), f s) + ∫ s in (d - 1)..d, f s = ∫ s in r₂..d, f s :=
    intervalIntegral.integral_add_adjacent_intervals hii1 hii2
  have hhead : 0 ≤ ∫ s in r₂..(d - 1), f s :=
    intervalIntegral.integral_nonneg hd1 (fun s _ => hfnn s)
  set B := C * d ^ n * Real.exp (-(d - 1) / n) with hBdef
  have _hBpos : 0 < B := by rw [hBdef]; positivity
  have hptwise : ∀ s ∈ Set.Icc (d - 1) d, 1 / B ^ 2 ≤ f s := by
    intro s hs
    have hsr₂ : r₂ ≤ s := le_trans hd1 hs.1
    have hs0 : 0 < s := lt_of_lt_of_le hr₂pos hsr₂
    have hub_s : |chiR n ℓ hn s| ≤ B := by
      refine le_trans (hub s hsr₂) ?_
      rw [hBdef]
      have hsn : s ^ n ≤ d ^ n := pow_le_pow_left₀ (le_of_lt hs0) hs.2 n
      have hexp : Real.exp (-s / n) ≤ Real.exp (-(d - 1) / n) :=
        Real.exp_le_exp.mpr (by rw [div_le_div_iff_of_pos_right hn0]; linarith [hs.1])
      have hprod : s ^ n * Real.exp (-s / n) ≤ d ^ n * Real.exp (-(d - 1) / n) :=
        mul_le_mul hsn hexp (Real.exp_pos _).le (by positivity)
      calc C * (s ^ n * Real.exp (-s / n)) ≤ C * (d ^ n * Real.exp (-(d - 1) / n)) :=
            mul_le_mul_of_nonneg_left hprod hCpos.le
        _ = C * d ^ n * Real.exp (-(d - 1) / n) := by ring
    have hchiR2 : (chiR n ℓ hn s) ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs (chiR n ℓ hn s)]
      exact pow_le_pow_left₀ (abs_nonneg _) hub_s 2
    have hchiRpos : 0 < (chiR n ℓ hn s) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hne s hsr₂)))
    rw [hf]
    exact one_div_le_one_div_of_le hchiRpos hchiR2
  have hintc : 1 / B ^ 2 ≤ ∫ s in (d - 1)..d, f s := by
    have hmono := intervalIntegral.integral_mono_on hd1d intervalIntegrable_const hii2 hptwise
    rw [intervalIntegral.integral_const, smul_eq_mul, show d - (d - 1) = 1 from by ring,
      one_mul] at hmono
    exact hmono
  calc 1 / B ^ 2 ≤ ∫ s in (d - 1)..d, f s := hintc
    _ ≤ (∫ s in r₂..(d - 1), f s) + ∫ s in (d - 1)..d, f s := by linarith [hhead]
    _ = ∫ s in r₂..d, f s := hsplit

/-- **The Wronskian of any L² solution with the eigenfunction vanishes.** At the
eigenvalue `Eₙ`, square-integrability forces the Wronskian of `χ` with `χ_R` to be `0`,
since otherwise reduction of order makes `|χ|` bounded below at infinity (`χ ∉ L²`). -/
private lemma wronskian_R_zero_of_L2 (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (n : ℝ)) ^ 2) * χ r)
    (hL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0)) :
    ∀ s, 0 < s → χ s * deriv (chiR n ℓ hn) s - deriv χ s * chiR n ℓ hn s = 0 := by
  obtain ⟨r₂, c, C, hr₂pos, hcpos, hCpos, hbnds⟩ := chiR_tail_bounds n ℓ hn
  have hub : ∀ s, r₂ ≤ s → |chiR n ℓ hn s| ≤ C * (s ^ n * Real.exp (-s / n)) :=
    fun s hs => (hbnds s hs).2.1
  have hne : ∀ s, r₂ ≤ s → chiR n ℓ hn s ≠ 0 := fun s hs => (hbnds s hs).2.2
  have hLB : ∀ r, r₂ ≤ r → c * (r ^ n * Real.exp (-r / n)) ≤ |chiR n ℓ hn r| :=
    fun r hr => (hbnds r hr).1
  set W₀ := χ r₂ * deriv (chiR n ℓ hn) r₂ - deriv χ r₂ * chiR n ℓ hn r₂ with _hW₀def
  have hWconst : ∀ s, 0 < s →
      χ s * deriv (chiR n ℓ hn) s - deriv χ s * chiR n ℓ hn s = W₀ :=
    fun s hs => wronskian_R_const n ℓ hn χ hχ1 hχ2 hode hr₂pos hs
  suffices hW₀ : W₀ = 0 by intro s hs; rw [hWconst s hs]; exact hW₀
  by_contra hW₀ne
  have hW₀pos : 0 < |W₀| := abs_pos.mpr hW₀ne
  have hχr₂ne : chiR n ℓ hn r₂ ≠ 0 := hne r₂ le_rfl
  set c₂ := χ r₂ / chiR n ℓ hn r₂ with hc₂def
  set K := c * (Real.exp (-1 / (n : ℝ)) / C) ^ 2 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set A := |W₀| * K / 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; exact div_pos (mul_pos hW₀pos hKpos) two_pos
  have h2A : |W₀| * K = 2 * A := by rw [hAdef]; ring
  -- base(d) := dⁿ e^{-d/n} → 0
  have hbase0 : Filter.Tendsto (fun d => d ^ n * Real.exp (-d / n)) Filter.atTop (nhds 0) :=
    tendsto_pow_mul_exp_neg_div n n (by omega)
  have hbsq0 : Filter.Tendsto (fun d => |c₂| * C * (d ^ n * Real.exp (-d / n)) ^ 2)
      Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun d => (d ^ n * Real.exp (-d / n)) ^ 2)
        Filter.atTop (nhds 0) := by simpa using hbase0.pow 2
    simpa using h2.const_mul (|c₂| * C)
  have hev_sq : ∀ᶠ d in Filter.atTop, |c₂| * C * (d ^ n * Real.exp (-d / n)) ^ 2 < A := by
    filter_upwards [hbsq0.eventually (Iio_mem_nhds hApos)] with d hd using hd
  have hev_le : ∀ᶠ d in Filter.atTop, d ^ n * Real.exp (-d / n) < 1 := by
    filter_upwards [hbase0.eventually (Iio_mem_nhds one_pos)] with d hd using hd
  obtain ⟨R₀, hR₀⟩ := (hev_sq.and hev_le).exists_forall_of_atTop
  -- the eventual lower bound on |χ|
  have hlb : ∀ d, max (r₂ + 1) R₀ ≤ d → A ≤ |χ d| := by
    intro d hd_ge
    have hd1 : r₂ + 1 ≤ d := le_trans (le_max_left _ _) hd_ge
    have hdR₀ : R₀ ≤ d := le_trans (le_max_right _ _) hd_ge
    obtain ⟨hsqd, hled⟩ := hR₀ d hdR₀
    have hr₂d : r₂ < d := by linarith
    have hdpos : 0 < d := by linarith
    have hbasenn : (0:ℝ) ≤ d ^ n * Real.exp (-d / n) := by positivity
    have hbasepos : (0:ℝ) < d ^ n * Real.exp (-d / n) := by positivity
    have hχdne : chiR n ℓ hn d ≠ 0 := hne d (by linarith)
    have hne_d : ∀ x ∈ Set.uIcc r₂ d, chiR n ℓ hn x ≠ 0 := by
      intro x hx; rw [Set.uIcc_of_le (le_of_lt hr₂d)] at hx; exact hne x hx.1
    have hftc := reduction_order_ftc_R n ℓ hn χ hχ1 hχ2 W₀ hWconst hr₂pos hr₂d hne_d
    set I := ∫ s in r₂..d, 1 / (chiR n ℓ hn s) ^ 2 with hIdef
    have hInn : 0 ≤ I := by
      rw [hIdef]
      exact intervalIntegral.integral_nonneg (le_of_lt hr₂d) (fun s _ => by positivity)
    have hwin : 1 / (C * d ^ n * Real.exp (-(d - 1) / n)) ^ 2 ≤ I :=
      chiR_int_window n ℓ hn hCpos hub hne hr₂pos hd1
    -- χ d = chiR d · (c₂ − W₀ I)
    have hq : χ d / chiR n ℓ hn d
        = (χ r₂ - W₀ * (chiR n ℓ hn r₂ * I)) / chiR n ℓ hn r₂ := by
      rw [eq_div_iff hχr₂ne]; linear_combination -hftc
    have hχd_eq : χ d = chiR n ℓ hn d * (c₂ - W₀ * I) := by
      have hexpr : (χ r₂ - W₀ * (chiR n ℓ hn r₂ * I)) / chiR n ℓ hn r₂ = c₂ - W₀ * I := by
        rw [hc₂def]; field_simp
      have hχd : χ d = (χ r₂ - W₀ * (chiR n ℓ hn r₂ * I)) / chiR n ℓ hn r₂ * chiR n ℓ hn d := by
        rw [← hq, div_mul_cancel₀ _ hχdne]
      rw [hχd, hexpr]; ring
    have habs : |χ d| = |chiR n ℓ hn d| * |c₂ - W₀ * I| := by rw [hχd_eq, abs_mul]
    have hbr : |W₀| * I - |c₂| ≤ |c₂ - W₀ * I| := by
      have h1 := abs_sub_abs_le_abs_sub (W₀ * I) c₂
      rw [abs_mul W₀ I, abs_of_nonneg hInn, abs_sub_comm (W₀ * I) c₂] at h1
      exact h1
    have hmain : |chiR n ℓ hn d| * (|W₀| * I - |c₂|) ≤ |χ d| := by
      rw [habs]; exact mul_le_mul_of_nonneg_left hbr (abs_nonneg _)
    -- key constant identity: base·(c·base)·(1/B²) = K
    have hbB : (d ^ n * Real.exp (-d / n)) / (C * d ^ n * Real.exp (-(d - 1) / n))
        = Real.exp (-1 / (n : ℝ)) / C := by
      rw [div_eq_div_iff (show (0:ℝ) < C * d ^ n * Real.exp (-(d - 1) / n) by positivity).ne'
          hCpos.ne',
        show Real.exp (-1 / (n : ℝ)) * (C * d ^ n * Real.exp (-(d - 1) / n))
          = C * d ^ n * (Real.exp (-1 / (n : ℝ)) * Real.exp (-(d - 1) / n)) from by ring,
        ← Real.exp_add,
        show (-1 / (n : ℝ)) + -(d - 1) / n = -d / n from by ring]
      ring
    have hKeq : (d ^ n * Real.exp (-d / n)) *
        ((c * (d ^ n * Real.exp (-d / n))) *
          (1 / (C * d ^ n * Real.exp (-(d - 1) / n)) ^ 2)) = K := by
      have h1 : (d ^ n * Real.exp (-d / n)) *
          ((c * (d ^ n * Real.exp (-d / n))) *
            (1 / (C * d ^ n * Real.exp (-(d - 1) / n)) ^ 2))
          = c * ((d ^ n * Real.exp (-d / n)) / (C * d ^ n * Real.exp (-(d - 1) / n))) ^ 2 := by
        rw [div_pow]; ring
      rw [h1, hbB, hKdef]
    -- assemble: base·|χ d| ≥ |W₀|K − |c₂|C base²
    have hLBd : c * (d ^ n * Real.exp (-d / n)) ≤ |chiR n ℓ hn d| := hLB d (by linarith)
    have hubd : |chiR n ℓ hn d| ≤ C * (d ^ n * Real.exp (-d / n)) := hub d (by linarith)
    have hKlb : K ≤ (d ^ n * Real.exp (-d / n)) * (|chiR n ℓ hn d| * I) := by
      have step1 : (c * (d ^ n * Real.exp (-d / n))) *
          (1 / (C * d ^ n * Real.exp (-(d - 1) / n)) ^ 2) ≤ |chiR n ℓ hn d| * I :=
        mul_le_mul hLBd hwin (by positivity) (abs_nonneg _)
      calc K = (d ^ n * Real.exp (-d / n)) *
              ((c * (d ^ n * Real.exp (-d / n))) *
                (1 / (C * d ^ n * Real.exp (-(d - 1) / n)) ^ 2)) := hKeq.symm
        _ ≤ (d ^ n * Real.exp (-d / n)) * (|chiR n ℓ hn d| * I) :=
            mul_le_mul_of_nonneg_left step1 hbasenn
    have hUb : (d ^ n * Real.exp (-d / n)) * |chiR n ℓ hn d|
        ≤ C * (d ^ n * Real.exp (-d / n)) ^ 2 := by
      calc (d ^ n * Real.exp (-d / n)) * |chiR n ℓ hn d|
          ≤ (d ^ n * Real.exp (-d / n)) * (C * (d ^ n * Real.exp (-d / n))) :=
            mul_le_mul_of_nonneg_left hubd hbasenn
        _ = C * (d ^ n * Real.exp (-d / n)) ^ 2 := by ring
    have hbχ : (d ^ n * Real.exp (-d / n)) * (|chiR n ℓ hn d| * (|W₀| * I - |c₂|))
        ≤ (d ^ n * Real.exp (-d / n)) * |χ d| := mul_le_mul_of_nonneg_left hmain hbasenn
    have e1 : (d ^ n * Real.exp (-d / n)) * (|chiR n ℓ hn d| * (|W₀| * I - |c₂|))
        = |W₀| * ((d ^ n * Real.exp (-d / n)) * (|chiR n ℓ hn d| * I))
          - |c₂| * ((d ^ n * Real.exp (-d / n)) * |chiR n ℓ hn d|) := by ring
    have p1 : |W₀| * K ≤ |W₀| * ((d ^ n * Real.exp (-d / n)) * (|chiR n ℓ hn d| * I)) :=
      mul_le_mul_of_nonneg_left hKlb (abs_nonneg _)
    have p2 : |c₂| * ((d ^ n * Real.exp (-d / n)) * |chiR n ℓ hn d|)
        ≤ |c₂| * (C * (d ^ n * Real.exp (-d / n)) ^ 2) :=
      mul_le_mul_of_nonneg_left hUb (abs_nonneg _)
    have hsqd' : |c₂| * (C * (d ^ n * Real.exp (-d / n)) ^ 2) < A := by
      have : |c₂| * (C * (d ^ n * Real.exp (-d / n)) ^ 2)
          = |c₂| * C * (d ^ n * Real.exp (-d / n)) ^ 2 := by ring
      rw [this]; exact hsqd
    have hAlt : A < (d ^ n * Real.exp (-d / n)) * |χ d| := by
      have hchain : (d ^ n * Real.exp (-d / n)) * |χ d|
          ≥ |W₀| * K - |c₂| * (C * (d ^ n * Real.exp (-d / n)) ^ 2) := by
        calc (d ^ n * Real.exp (-d / n)) * |χ d|
            ≥ (d ^ n * Real.exp (-d / n)) * (|chiR n ℓ hn d| * (|W₀| * I - |c₂|)) := hbχ
          _ = |W₀| * ((d ^ n * Real.exp (-d / n)) * (|chiR n ℓ hn d| * I))
                - |c₂| * ((d ^ n * Real.exp (-d / n)) * |chiR n ℓ hn d|) := e1
          _ ≥ |W₀| * K - |c₂| * (C * (d ^ n * Real.exp (-d / n)) ^ 2) := by linarith [p1, p2]
      linarith [hchain, hsqd', h2A]
    -- finish: |χ d| ≥ base·|χ d| > A
    have hle : (d ^ n * Real.exp (-d / n)) * |χ d| ≤ |χ d| := by
      calc (d ^ n * Real.exp (-d / n)) * |χ d| ≤ 1 * |χ d| :=
            mul_le_mul_of_nonneg_right (le_of_lt hled) (abs_nonneg _)
        _ = |χ d| := one_mul _
    linarith [hAlt, hle]
  exact not_radialL2_of_eventually_ge χ hApos hlb hL2


/-! ## Completeness of discrete eigenfunctions -/

/-- **One-dimensionality of the radial eigenspace at `Eₙ`.**

    Every `C²` square-integrable solution `ψ` of the radial equation at the
    eigenvalue `Eₙ` is a scalar multiple of `R_{nℓ}`: the eigenspace of `H_ℓ` at
    `Eₙ` is (at most) one-dimensional.

    **Proof.** Pass to the reduced wavefunction `χ = r·ψ`, which solves the
    Schrödinger-form equation `χ'' = (ℓ(ℓ+1)/r² − 2/r + (1/n)²)·χ` (`reduced_ode`),
    and to the reference eigenfunction `χ_R = r·R_{nℓ}`
    (`reduced_eigenfunction_solves`). Their Wronskian `χ χ_R' − χ' χ_R` is constant
    (`wronskian_R_const`). Square-integrability forces it to vanish
    (`wronskian_R_zero_of_L2`): the terminating Kummer/Laguerre factor of `R_{nℓ}`
    makes `|χ_R| ≍ rⁿ e^{−r/n}` at infinity (`chiR_tail_bounds`, from the
    leading-term asymptotics `laguerre_asymptotic`), so a nonzero Wronskian would,
    by reduction of order (`reduction_order_ftc_R`, `chiR_int_window`), make `|χ|`
    bounded below by a positive constant at infinity — contradicting `L²`
    (`not_radialL2_of_eventually_ge`). With the Wronskian zero, linear-ODE
    uniqueness (`forward_identification_R`, Grönwall) propagates `χ = c·χ_R` from a
    base point near `0` (where `χ_R ≠ 0`, via `radial_boundary_r_zero`) to all of
    `(0,∞)`, whence `ψ = c·R_{nℓ}`. -/
theorem bound_state_eq_smul_eigenfunction (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (ψ : ℝ → ℝ)
    (hL2 : RadialL2 ψ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (heq : ∀ r, 0 < r → radialHamiltonian ℓ ψ r = hydrogenEigenvalue n (by omega) * ψ r) :
    ∃ c : ℝ, ∀ r, 0 < r → ψ r = c * hydrogenRadialWavefunction n ℓ hn r := by
  set χ : ℝ → ℝ := fun s => s * ψ s with hχdef
  have hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r := by
    intro r hr; rw [hχdef, deriv_reducedMul ψ (hψ1 r hr)]; exact hasDerivAt_reducedMul ψ (hψ1 r hr)
  have hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r := by
    intro r hr; rw [hχdef, deriv2_reducedMul ψ hψ1 hψ2 hr]
    exact hasDerivAt_deriv_reducedMul ψ hψ1 hψ2 hr
  have hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (n : ℝ)) ^ 2) * χ r := by
    intro r hr
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hEn : ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (n : ℝ)) ^ 2)
        = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * hydrogenEigenvalue n (by omega)) := by
      rw [hydrogenEigenvalue]; field_simp; ring
    rw [hEn, show deriv^[2] χ r = deriv^[2] (fun s => s * ψ s) r from rfl,
      reduced_ode ℓ (hydrogenEigenvalue n (by omega)) ψ hψ1 hψ2 heq hr]
  have hχL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0) := reduced_integrableOn_sq ψ hL2
  have hWzero := wronskian_R_zero_of_L2 n ℓ hn χ hχ1 hχ2 hode hχL2
  -- a global nonzero point of R_{nℓ}
  obtain ⟨rs, hrspos, hRrs⟩ : ∃ rs, 0 < rs ∧ hydrogenRadialWavefunction n ℓ hn rs ≠ 0 := by
    by_contra hcon
    have hz : ∀ r, 0 < r → hydrogenRadialWavefunction n ℓ hn r = 0 :=
      fun r hr => not_not.1 (fun h => hcon ⟨r, hr, h⟩)
    have hnorm := radial_wavefunction_norm n ℓ hn
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun r hr => by rw [hz r hr]; ring)] at hnorm
    simp at hnorm
  -- χ_R = r·R_{nℓ} is nonzero near 0
  have hnear0 : ∃ δ, 0 < δ ∧ ∀ s, 0 < s → s < δ → chiR n ℓ hn s ≠ 0 := by
    have hNpos : 0 < radialNormalization n ℓ hn := by
      rw [radialNormalization, Real.sqrt_pos]
      have _h1 : (0:ℝ) < ((n - ℓ - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have _h2 : (0:ℝ) < ((n + ℓ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have h3 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity
    have h3 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hL0 : 0 < laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1 : ℝ) 0 := by
      have hval : laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1 : ℝ) 0
          = realBinom (((n - ℓ - 1 : ℕ) : ℝ) + (2 * ℓ + 1)) (n - ℓ - 1) := by
        rw [laguerrePolynomial, Finset.sum_eq_single 0]
        · simp
        · intro k _ hk; rw [zero_pow hk]; ring
        · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
      rw [hval, realBinom]
      apply div_pos
      · apply Finset.prod_pos
        intro i hi
        rw [Finset.mem_range] at hi
        have hi' : (i : ℝ) < ((n - ℓ - 1 : ℕ) : ℝ) := by exact_mod_cast hi
        have h21 : (0:ℝ) < 2 * (ℓ : ℝ) + 1 := by positivity
        linarith [hi', h21]
      · exact_mod_cast Nat.factorial_pos _
    have hlimpos : 0 < radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ *
        laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) 0 := by positivity
    have hbd := radial_boundary_r_zero n ℓ hn
    have hev := hbd.eventually (lt_mem_nhds hlimpos)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    refine ⟨δ, hδpos, fun s hs0 hsδ => ?_⟩
    have hdist : dist s (0:ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hsδ
    have hpos : 0 < hydrogenReducedWavefunction n ℓ hn s / s ^ (ℓ + 1) :=
      hδ hdist (Set.mem_Ioi.mpr hs0)
    have hsp : (0:ℝ) < s ^ (ℓ + 1) := by positivity
    have hval : 0 < hydrogenReducedWavefunction n ℓ hn s := by
      have hm := mul_pos hpos hsp
      rwa [div_mul_cancel₀ _ (ne_of_gt hsp)] at hm
    change chiR n ℓ hn s ≠ 0
    rw [show chiR n ℓ hn s = hydrogenReducedWavefunction n ℓ hn s from rfl]
    exact ne_of_gt hval
  obtain ⟨δ, hδpos, hδne⟩ := hnear0
  set c₀ := ψ rs / hydrogenRadialWavefunction n ℓ hn rs with _hc₀def
  have hchiRrs : chiR n ℓ hn rs ≠ 0 := by
    rw [show chiR n ℓ hn rs = rs * hydrogenRadialWavefunction n ℓ hn rs from rfl]
    exact mul_ne_zero (ne_of_gt hrspos) hRrs
  have hc₀eq : χ rs / chiR n ℓ hn rs = c₀ := by
    change (rs * ψ rs) / (rs * hydrogenRadialWavefunction n ℓ hn rs)
      = ψ rs / hydrogenRadialWavefunction n ℓ hn rs
    rw [mul_div_mul_left _ _ (ne_of_gt hrspos)]
  -- global identification χ = c₀·χ_R
  have hident : ∀ r, 0 < r → χ r = c₀ * chiR n ℓ hn r := by
    intro r hr
    set rmin := min (min r rs) (δ / 2) with _hrmindef
    have hrminpos : 0 < rmin := lt_min (lt_min hr hrspos) (by linarith)
    have hrmin_r : rmin ≤ r := le_trans (min_le_left _ _) (min_le_left _ _)
    have hrmin_rs : rmin ≤ rs := le_trans (min_le_left _ _) (min_le_right _ _)
    have hrmin_δ : rmin < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hchiRmin : chiR n ℓ hn rmin ≠ 0 := hδne rmin hrminpos hrmin_δ
    set d₀ := χ rmin / chiR n ℓ hn rmin with hd₀def
    have h0 : χ rmin - d₀ * chiR n ℓ hn rmin = 0 := by
      rw [hd₀def, div_mul_cancel₀ _ hchiRmin, sub_self]
    have h0' : deriv χ rmin - d₀ * deriv (chiR n ℓ hn) rmin = 0 := by
      have hW := hWzero rmin hrminpos
      rw [hd₀def]; field_simp; linarith [hW]
    have hfwd := forward_identification_R n ℓ hn χ hχ1 hχ2 hode d₀ hrminpos h0 h0'
    have hd₀c₀ : d₀ = c₀ := by
      rw [← hc₀eq, eq_div_iff hchiRrs]; exact (hfwd rs hrmin_rs).symm
    rw [← hd₀c₀]; exact hfwd r hrmin_r
  -- conclude ψ = c₀·R
  refine ⟨c₀, fun r hr => ?_⟩
  have h := hident r hr
  rw [show χ r = r * ψ r from rfl,
    show chiR n ℓ hn r = r * hydrogenRadialWavefunction n ℓ hn r from rfl] at h
  have hrne : r ≠ 0 := ne_of_gt hr
  have h2 : r * ψ r = r * (c₀ * hydrogenRadialWavefunction n ℓ hn r) := by rw [h]; ring
  exact mul_left_cancel₀ hrne h2

/-- **Negative-energy radial bound states are one-dimensional and quantized.**

    A classical negative-energy bound state in angular sector `ℓ` — a function
    `ψ ∈ L²(ℝ⁺, r²dr)` that is `C²` on `(0,∞)`, regular at the origin
    (`r·ψ(r) → 0` as `r → 0⁺`), and solves `H_ℓ ψ = E ψ` for some `E < 0` — is
    forced to be either identically zero on `(0,∞)` or a *scalar multiple of a
    single* eigenfunction `R_{nℓ}`, with the energy quantized to `E = Eₙ` for some
    `n ≥ ℓ+1`. The regularity hypothesis excludes the irregular Coulomb solution at
    `ℓ = 0`; it is exactly the hypothesis package of `radial_quantization`.

    Proof: `radial_quantization` quantizes `E = Eₙ`, and then
    `bound_state_eq_smul_eigenfunction` gives `ψ = c·R_{nℓ}` (both sorry-free).

    **This is *not* Hilbert-space completeness.** It says the negative-energy
    *eigenspaces* of `H_ℓ` are one-dimensional and spanned by the `R_{nℓ}` — i.e.
    no bound state is missed. It does **not** say `{R_{nℓ}}_{n≥ℓ+1}` is total in the
    bound-state subspace of `L²(r²dr)`: that genuine completeness needs a
    self-adjoint realization of `H_ℓ` with its spectral projection (1-D singular
    Sturm–Liouville / spectral theorem) and cannot be obtained from
    `laguerre_complete`, whose fixed-scale family `e^{−r/2}·L_k^{(2ℓ+1)}` spans all
    of `L²(r²dr)` rather than the proper bound-state subspace that the
    varying-scale (`e^{−r/n}`) hydrogen states span. -/
theorem radial_bound_state_unique (ℓ : ℕ) (E : ℝ) (hE : E < 0) (ψ : ℝ → ℝ)
    (hL2 : RadialL2 ψ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (hψ0 : Filter.Tendsto (fun r => r * ψ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (heq : ∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r) :
    (∀ r, 0 < r → ψ r = 0) ∨
      ∃ (n : ℕ) (hn : ℓ + 1 ≤ n) (c : ℝ),
        E = hydrogenEigenvalue n (by omega) ∧
        ∀ r, 0 < r → ψ r = c * hydrogenRadialWavefunction n ℓ hn r := by
  by_cases hnz : ∃ r₀, 0 < r₀ ∧ ψ r₀ ≠ 0
  · -- Nondegenerate bound state: quantize `E = Eₙ`, then `ψ = c·R_{nℓ}`.
    right
    obtain ⟨n, hn, hEeq⟩ := (radial_quantization ℓ E hE).mp
      ⟨ψ, hnz, hL2, hψ1, hψ2, heq, hψ0⟩
    have heqn : ∀ r, 0 < r → radialHamiltonian ℓ ψ r = hydrogenEigenvalue n (by omega) * ψ r :=
      fun r hr => by rw [heq r hr, hEeq]
    obtain ⟨c, hc⟩ := bound_state_eq_smul_eigenfunction n ℓ hn ψ hL2 hψ1 hψ2 heqn
    exact ⟨n, hn, c, hEeq, hc⟩
  · -- `ψ` vanishes on `(0,∞)`.
    exact Or.inl fun r hr => not_not.1 fun h => hnz ⟨r, hr, h⟩

/-! ## Explicit wavefunctions for small n -/

/-- R_{1,0}(r) = 2 e^{−r} (the 1s orbital). -/
theorem radialWavefunction_1s :
    hydrogenRadialWavefunction 1 0 (by norm_num) = fun r => 2 * Real.exp (-r) := by
  have hN : radialNormalization 1 0 (by norm_num) = 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    unfold radialNormalization
    congr 1
    norm_num [Nat.factorial]
  funext r
  unfold hydrogenRadialWavefunction
  rw [hN, show (1 - 0 - 1 : ℕ) = 0 from rfl, laguerre_zero]
  simp only [Nat.cast_one, div_one, pow_zero, mul_one]

/-- R_{2,0}(r) = (1/√2)(1 − r/2) e^{−r/2} (the 2s orbital). -/
theorem radialWavefunction_2s :
    hydrogenRadialWavefunction 2 0 (by norm_num) =
    fun r => (1 / Real.sqrt 2) * (1 - r / 2) * Real.exp (-r / 2) := by
  have hN : radialNormalization 2 0 (by norm_num) = Real.sqrt (1 / 8) := by
    unfold radialNormalization; congr 1; norm_num [Nat.factorial]
  have hs : Real.sqrt (1 / 8) = 1 / (2 * Real.sqrt 2) := by
    rw [show (1 / 8 : ℝ) = (1 / (2 * Real.sqrt 2)) ^ 2 by
      rw [div_pow, one_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  funext r
  unfold hydrogenRadialWavefunction
  rw [hN, hs, show (2 - 0 - 1 : ℕ) = 1 from rfl, laguerre_one]
  push_cast
  ring

/-- R_{2,1}(r) = (1/(2√6)) r e^{−r/2} (the 2p orbital). -/
theorem radialWavefunction_2p :
    hydrogenRadialWavefunction 2 1 (by norm_num) =
    fun r => (1 / (2 * Real.sqrt 6)) * r * Real.exp (-r / 2) := by
  have hN : radialNormalization 2 1 (by norm_num) = Real.sqrt (1 / 24) := by
    unfold radialNormalization; congr 1; norm_num [Nat.factorial]
  have hs : Real.sqrt (1 / 24) = 1 / (2 * Real.sqrt 6) := by
    rw [show (1 / 24 : ℝ) = (1 / (2 * Real.sqrt 6)) ^ 2 by
      rw [div_pow, one_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]; norm_num]
    exact Real.sqrt_sq (by positivity)
  funext r
  unfold hydrogenRadialWavefunction
  rw [hN, hs, show (2 - 1 - 1 : ℕ) = 0 from rfl, laguerre_zero]
  push_cast
  ring

end QuantumMechanics.Hydrogen.RadialEq

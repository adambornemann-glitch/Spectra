/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The confluent hypergeometric (Kummer) function `₁F₁`

The confluent hypergeometric function `M(a, b, z) = ₁F₁(a; b; z) = ∑ₖ (a)ₖ/((b)ₖ k!) zᵏ`,
defined here directly through the coefficient recurrence

  `c₀ = 1`,  `c_{k+1} = c_k · (a + k) / ((b + k)(k + 1))`,

so that `M(a,b,z) = ∑' k, c_k zᵏ`.

This is the regular-at-`0` solution of **Kummer's equation**

  `z·M''(z) + (b − z)·M'(z) − a·M(z) = 0`.

It is the analytic input needed for the hydrogen radial quantization argument: writing the
reduced radial wavefunction as `χ = r^{ℓ+1} e^{−κr} w`, the factor `w` is `M(ℓ+1−1/κ, 2ℓ+2, 2κr)`
(see `QuantumMechanics.Hydrogen.RadialProblem.Equation.Reduced.Quantization`), and termination of
this series (`a = ℓ+1−1/κ` a non-positive integer ⟺ `κ = 1/m`, `m ≥ ℓ+1`) is exactly the
quantization condition.

## Main definitions / statements

* `kummerCoeff a b` — the coefficient sequence `cₖ`.
* `kummerM a b z` — the function `∑' k, cₖ zᵏ`.
* `summable_abs_kummer_mul_pow` — the master ratio-test bound `∑ |cₙ|(n+1)ʲ Rⁿ < ∞`, which
  powers both convergence and (locally uniform) term-by-term differentiation.
* `kummerM_summable` — the defining series converges for every `z` (the function is entire).
* `kummerM_hasDerivAt` / `kummerM_deriv` — `M'(z) = ∑' k, (k+1) c_{k+1} zᵏ`.
* `kummerM_hasDerivAt2` / `kummerM_deriv2` — `M''(z) = ∑' k, (k+1)(k+2) c_{k+2} zᵏ`.
* `kummerM_ode` — **Kummer's ODE** `z M''(z) + (b − z) M'(z) − a M(z) = 0`.
* `abs_kummerCoeff_geom_lower` — for non-terminating `a`, `|c_k| ≥ C·(1/2)ᵏ/k!` eventually.
* `kummerM_abs_exp_lower` — for non-terminating `a`, `|M(a,b,ρ)| ≥ C·e^{ρ/2}` for large `ρ`
  (the exponential growth that breaks square-integrability of the radial wavefunction).

The unit ball is the whole line: the coefficients decay super-geometrically (ratio `→ 0`),
because `b > 0` keeps every denominator `(b + k) > 0`. The ODE collapses, via the index shifts
`z·(∑ dₖ zᵏ) = ∑ dₖ z^{k+1}` (whose `k = 0` term vanishes through the surviving `k` factor),
to the termwise recurrence `(k+1)(b+k) c_{k+1} = (a+k) c_k` (`kummerCoeff_rec`).

## Downstream use (hydrogen quantization)

The full growth analysis of the non-terminating series is complete here — both the coefficient
bound (`abs_kummerCoeff_geom_lower`) and the **function-level exponential lower bound**
(`kummerM_abs_exp_lower`). Both `kummerM_ode` and `kummerM_abs_exp_lower` are consumed by
`QuantumMechanics.Hydrogen.RadialProblem.Equation.Reduced.Quantization`, where:
* `M(ℓ+1−1/κ, 2ℓ+2, 2κr)` is connected to the reduced radial solution `w` via
  `laguerre_ansatz_reduced_iff` and ODE-uniqueness identification of the regular-at-`0` solution;
* the resulting non-`L²`-ness unless the series terminates: with `z = 2κr`, the bound gives
  `|w(r)| ≳ e^{κr}`, so `χ ∼ r^{ℓ+1} e^{+κr}` and `∫ r^{2ℓ+2} = ∞` — the final crux of
  `reduced_radial_L2_quantized`, which then forces `a = ℓ+1−1/κ ∈ ℤ≤0`, i.e. `κ = 1/m`.
-/

open Filter
open scoped Topology

namespace Spectra.Kummer

/-- The coefficients `cₖ = (a)ₖ / ((b)ₖ k!)` of the confluent hypergeometric series, defined by the
recurrence `c₀ = 1`, `c_{k+1} = c_k · (a + k) / ((b + k)(k + 1))`. -/
noncomputable def kummerCoeff (a b : ℝ) : ℕ → ℝ
  | 0 => 1
  | (k + 1) => kummerCoeff a b k * (a + k) / ((b + k) * (k + 1))

/-- The recurrence at `k = 0`: `c₀ = 1`. -/
@[simp] lemma kummerCoeff_zero (a b : ℝ) : kummerCoeff a b 0 = 1 := rfl

/-- The recurrence at `k + 1`: `c_{k+1} = c_k · (a + k) / ((b + k)(k + 1))`. -/
lemma kummerCoeff_succ (a b : ℝ) (k : ℕ) :
    kummerCoeff a b (k + 1) = kummerCoeff a b k * (a + k) / ((b + k) * ((k : ℝ) + 1)) := rfl

/-- For `b > 0` the denominator `(b + k)(k + 1)` is strictly positive. -/
lemma kummer_den_pos (b : ℝ) (hb : 0 < b) (k : ℕ) : 0 < (b + (k : ℝ)) * ((k : ℝ) + 1) := by
  have _hbk : 0 < b + (k : ℝ) := by
    have _hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  have _hk1 : 0 < (k : ℝ) + 1 := by positivity
  positivity

/-- The recurrence cleared of denominators: `(k+1)(b+k)·c_{k+1} = (a+k)·c_k`. -/
lemma kummerCoeff_rec (a b : ℝ) (hb : 0 < b) (k : ℕ) :
    ((k : ℝ) + 1) * (b + (k : ℝ)) * kummerCoeff a b (k + 1)
      = (a + (k : ℝ)) * kummerCoeff a b k := by
  have _hden := (kummer_den_pos b hb k).ne'
  rw [kummerCoeff_succ]
  field_simp

/-- Absolute-value form of the recurrence. -/
lemma abs_kummerCoeff_succ (a b : ℝ) (hb : 0 < b) (k : ℕ) :
    |kummerCoeff a b (k + 1)|
      = |kummerCoeff a b k| * (|a + (k : ℝ)| / ((b + (k : ℝ)) * ((k : ℝ) + 1))) := by
  rw [kummerCoeff_succ, abs_div, abs_mul, abs_of_pos (kummer_den_pos b hb k), mul_div_assoc]

/-- **Master summability lemma.** For every exponent `j` and radius `R ≥ 0`, the series
`∑ₙ |cₙ| (n+1)ʲ Rⁿ` converges. This single ratio-test estimate powers both the convergence of
`kummerM` and the (locally uniform) bounds needed to differentiate it term by term.

The ratio `|c_{n+1}|(n+2)ʲ R^{n+1} / (|cₙ|(n+1)ʲ Rⁿ) = |a+n| R (n+2)ʲ / ((b+n)(n+1)^{j+1})`
behaves like `R/n → 0`, so the terms are eventually halved. -/
lemma summable_abs_kummer_mul_pow (a b : ℝ) (hb : 0 < b) (j : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun n => |kummerCoeff a b n| * ((n : ℝ) + 1) ^ j * R ^ n) := by
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_ge (2 ^ (j + 1) * R * (|a| + 1))
  filter_upwards [eventually_ge_atTop N] with n hn
  -- abbreviations and positivity facts
  set cn := |kummerCoeff a b n| with hcn
  have hcn0 : 0 ≤ cn := by rw [hcn]; positivity
  have hRn : 0 ≤ R ^ n := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have _hbk : (0 : ℝ) < b + (n : ℝ) := by linarith
  have hD : (0 : ℝ) < (b + (n : ℝ)) * ((n : ℝ) + 1) := kummer_den_pos b hb n
  have hfac : 0 ≤ cn * R ^ n := mul_nonneg hcn0 hRn
  -- The norms are the (nonnegative) values themselves.
  have hnormeq : ‖|kummerCoeff a b (n + 1)| * ((↑(n + 1) : ℝ) + 1) ^ j * R ^ (n + 1)‖
      = cn * (|a + (n : ℝ)| / ((b + (n : ℝ)) * ((n : ℝ) + 1))) * ((n : ℝ) + 2) ^ j
        * R ^ (n + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_kummerCoeff_succ a b hb n, ← hcn]
    push_cast
    ring_nf
  have hnormeq2 : ‖|kummerCoeff a b n| * ((n : ℝ) + 1) ^ j * R ^ n‖
      = cn * ((n : ℝ) + 1) ^ j * R ^ n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← hcn]
  rw [hnormeq, hnormeq2]
  -- The polynomial inequality after cancelling `cn · Rⁿ ≥ 0` and the denominator.
  have hkey : |a + (n : ℝ)| * R * ((n : ℝ) + 2) ^ j
      ≤ 1 / 2 * (((n : ℝ) + 1) ^ j * (b + (n : ℝ)) * ((n : ℝ) + 1)) := by
    have hbig : (2 : ℝ) ^ (j + 1) * R * (|a| + 1) ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
    have habs : |a + (n : ℝ)| ≤ (|a| + 1) * ((n : ℝ) + 1) := by
      have h1 : |a + (n : ℝ)| ≤ |a| + (n : ℝ) := by
        calc |a + (n : ℝ)| ≤ |a| + |(n : ℝ)| := abs_add_le _ _
          _ = |a| + (n : ℝ) := by rw [abs_of_nonneg hn0]
      nlinarith [abs_nonneg a]
    have hpow : ((n : ℝ) + 2) ^ j ≤ 2 ^ j * ((n : ℝ) + 1) ^ j := by
      rw [← mul_pow]; gcongr; linarith
    have hpos1 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (j + 1) := by positivity
    have hbig' : 2 * (2 ^ j * R * (|a| + 1)) ≤ (n : ℝ) := by
      have hrw : (2 : ℝ) * (2 ^ j * R * (|a| + 1)) = 2 ^ (j + 1) * R * (|a| + 1) := by
        rw [pow_succ]; ring
      rw [hrw]; exact hbig
    -- LHS ≤ (|a|+1)·R·2ʲ·(n+1)^{j+1} ≤ ½(b+n)·(n+1)^{j+1} = RHS
    calc |a + (n : ℝ)| * R * ((n : ℝ) + 2) ^ j
        ≤ ((|a| + 1) * ((n : ℝ) + 1)) * R * (2 ^ j * ((n : ℝ) + 1) ^ j) := by gcongr
      _ = (2 ^ j * R * (|a| + 1)) * ((n : ℝ) + 1) ^ (j + 1) := by rw [pow_succ]; ring
      _ ≤ (1 / 2 * (b + (n : ℝ))) * ((n : ℝ) + 1) ^ (j + 1) := by
            apply mul_le_mul_of_nonneg_right _ hpos1; linarith [hbig', hb]
      _ = 1 / 2 * (((n : ℝ) + 1) ^ j * (b + (n : ℝ)) * ((n : ℝ) + 1)) := by rw [pow_succ]; ring
  rw [show cn * (|a + (n : ℝ)| / ((b + (n : ℝ)) * ((n : ℝ) + 1))) * ((n : ℝ) + 2) ^ j * R ^ (n + 1)
        = (cn * R ^ n) * (|a + (n : ℝ)| * R * ((n : ℝ) + 2) ^ j) / ((b + (n : ℝ)) * ((n : ℝ) + 1))
      from by rw [pow_succ]; ring]
  rw [div_le_iff₀ hD]
  calc (cn * R ^ n) * (|a + (n : ℝ)| * R * ((n : ℝ) + 2) ^ j)
      ≤ (cn * R ^ n) * (1 / 2 * (((n : ℝ) + 1) ^ j * (b + (n : ℝ)) * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hkey hfac
    _ = 1 / 2 * (cn * ((n : ℝ) + 1) ^ j * R ^ n) * ((b + (n : ℝ)) * ((n : ℝ) + 1)) := by ring

/-- **The defining series converges for every `z`.** (The case `j = 0` of the master lemma,
compared against `|cₖ zᵏ| = |cₖ| |z|ᵏ`.) Hence `kummerM a b` is well defined and entire. -/
lemma kummerM_summable (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    Summable (fun k => kummerCoeff a b k * z ^ k) := by
  apply Summable.of_norm
  refine (summable_abs_kummer_mul_pow a b hb 0 (R := |z|) (abs_nonneg z)).congr (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, pow_zero, mul_one]

/-- The confluent hypergeometric (Kummer) function `M(a, b, z) = ₁F₁(a; b; z) = ∑' k, cₖ zᵏ`. -/
noncomputable def kummerM (a b z : ℝ) : ℝ := ∑' k, kummerCoeff a b k * z ^ k

/-- `M(a, b, 0) = 1`. -/
@[simp] lemma kummerM_zero (a b : ℝ) : kummerM a b 0 = 1 := by
  unfold kummerM
  rw [tsum_eq_single 0 (fun n hn => by rw [zero_pow hn, mul_zero])]
  simp

/-! ### First derivative -/

/-- The formal termwise derivative series of `M` is summable at every point (case `j = 1`
of the master lemma, with `|cₙ| n |z|^{n-1} ≤ |cₙ|(n+1)(|z|+1)ⁿ`). -/
lemma summable_kummerCoeff_deriv (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    Summable (fun n => kummerCoeff a b n * ((n : ℝ) * z ^ (n - 1))) := by
  refine Summable.of_norm_bounded
    (summable_abs_kummer_mul_pow a b hb 1 (R := |z| + 1) (by positivity)) (fun n => ?_)
  have hzn : |z| ^ (n - 1) ≤ (|z| + 1) ^ n := by
    calc |z| ^ (n - 1) ≤ (|z| + 1) ^ (n - 1) := by gcongr; linarith [abs_nonneg z]
      _ ≤ (|z| + 1) ^ n := by gcongr <;> [linarith [abs_nonneg z]; exact Nat.sub_le n 1]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast, pow_one]
  have hcn := abs_nonneg (kummerCoeff a b n)
  calc |kummerCoeff a b n| * ((n : ℝ) * |z| ^ (n - 1))
      ≤ |kummerCoeff a b n| * (((n : ℝ) + 1) * (|z| + 1) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ hcn
        exact mul_le_mul (by linarith) hzn (by positivity) (by linarith [abs_nonneg z])
    _ = |kummerCoeff a b n| * ((n : ℝ) + 1) * (|z| + 1) ^ n := by ring

/-- Reindexing the formal derivative series into the shifted `(k+1) c_{k+1}` form. -/
lemma kummerCoeff_deriv_reindex (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    ∑' n, kummerCoeff a b n * ((n : ℝ) * z ^ (n - 1))
      = ∑' k : ℕ, ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k := by
  rw [(summable_kummerCoeff_deriv a b hb z).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
  refine tsum_congr (fun k => ?_)
  rw [Nat.add_sub_cancel]
  push_cast
  ring

/-- **`M(a,b,·)` is differentiable with the expected (shifted) derivative series.**
`M'(z) = ∑' k, (k+1) c_{k+1} zᵏ`. Proved by locally uniform term-by-term differentiation on
balls (the master bound supplies the uniform control). -/
lemma kummerM_hasDerivAt (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    HasDerivAt (kummerM a b) (∑' k : ℕ, ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k) z := by
  have ht : IsOpen (Metric.ball (0 : ℝ) (|z| + 1)) := Metric.isOpen_ball
  have h't : IsPreconnected (Metric.ball (0 : ℝ) (|z| + 1)) :=
    (convex_ball 0 (|z| + 1)).isPreconnected
  have hz : z ∈ Metric.ball (0 : ℝ) (|z| + 1) := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) (|z| + 1) := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_zero]; linarith [abs_nonneg z]
  have hg0 : Summable (fun n => kummerCoeff a b n * (0 : ℝ) ^ n) := kummerM_summable a b hb 0
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) (|z| + 1) →
      ‖kummerCoeff a b n * ((n : ℝ) * y ^ (n - 1))‖
        ≤ |kummerCoeff a b n| * ((n : ℝ) + 1) ^ 1 * (|z| + 1) ^ n := by
    intro n y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    have _h1 : |y| ≤ |z| + 1 := le_of_lt hy
    have hyn : |y| ^ (n - 1) ≤ (|z| + 1) ^ n := by
      calc |y| ^ (n - 1) ≤ (|z| + 1) ^ (n - 1) := by gcongr
        _ ≤ (|z| + 1) ^ n := by gcongr <;> [linarith [abs_nonneg z]; exact Nat.sub_le n 1]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast, pow_one]
    have hcn := abs_nonneg (kummerCoeff a b n)
    calc |kummerCoeff a b n| * ((n : ℝ) * |y| ^ (n - 1))
        ≤ |kummerCoeff a b n| * (((n : ℝ) + 1) * (|z| + 1) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ hcn
          exact mul_le_mul (by linarith) hyn (by positivity) (by linarith [abs_nonneg z])
      _ = |kummerCoeff a b n| * ((n : ℝ) + 1) * (|z| + 1) ^ n := by ring
  rw [← kummerCoeff_deriv_reindex a b hb z]
  change HasDerivAt (fun y => ∑' n, kummerCoeff a b n * y ^ n)
    (∑' n, kummerCoeff a b n * ((n : ℝ) * z ^ (n - 1))) z
  exact hasDerivAt_tsum_of_isPreconnected
    (summable_abs_kummer_mul_pow a b hb 1 (R := |z| + 1) (by positivity)) ht h't
    (fun n y _ => (hasDerivAt_pow n y).const_mul (kummerCoeff a b n)) hbound h0 hg0 hz

/-- The derivative of `M` in value form: `M'(z) = ∑' k, (k+1) c_{k+1} zᵏ`. -/
lemma kummerM_deriv (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    deriv (kummerM a b) z = ∑' k : ℕ, ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k :=
  (kummerM_hasDerivAt a b hb z).deriv

/-! ### Second derivative -/

/-- `deriv (kummerM a b)`, as a function, is the (un-shifted) termwise derivative series. -/
lemma kummerM_deriv_eq_tsum (a b : ℝ) (hb : 0 < b) :
    deriv (kummerM a b) = fun z => ∑' n, kummerCoeff a b n * ((n : ℝ) * z ^ (n - 1)) := by
  funext w
  rw [kummerM_deriv a b hb w]
  exact (kummerCoeff_deriv_reindex a b hb w).symm

/-- The formal second-derivative series is summable at every point (case `j = 2` of the master
lemma, with `|cₙ| n(n-1) |z|^{n-2} ≤ |cₙ|(n+1)²(|z|+1)ⁿ`). -/
lemma summable_kummerCoeff_deriv2 (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    Summable (fun n => kummerCoeff a b n *
      ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * z ^ (n - 1 - 1)))) := by
  refine Summable.of_norm_bounded
    (summable_abs_kummer_mul_pow a b hb 2 (R := |z| + 1) (by positivity)) (fun n => ?_)
  have hzn : |z| ^ (n - 1 - 1) ≤ (|z| + 1) ^ n := by
    calc |z| ^ (n - 1 - 1) ≤ (|z| + 1) ^ (n - 1 - 1) := by gcongr; linarith [abs_nonneg z]
      _ ≤ (|z| + 1) ^ n := by gcongr <;> [linarith [abs_nonneg z]; omega]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast, Nat.abs_cast]
  have hcn := abs_nonneg (kummerCoeff a b n)
  have hnn1 : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc |kummerCoeff a b n| * ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * |z| ^ (n - 1 - 1)))
      ≤ |kummerCoeff a b n| * (((n : ℝ) + 1) ^ 2 * (|z| + 1) ^ n) := by
        apply mul_le_mul_of_nonneg_left _ hcn
        calc (n : ℝ) * (((n - 1 : ℕ) : ℝ) * |z| ^ (n - 1 - 1))
            = ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) * |z| ^ (n - 1 - 1) := by ring
          _ ≤ ((n : ℝ) + 1) ^ 2 * (|z| + 1) ^ n :=
              mul_le_mul hnn1 hzn (by positivity) (by positivity)
    _ = |kummerCoeff a b n| * ((n : ℝ) + 1) ^ 2 * (|z| + 1) ^ n := by ring

/-- **The second derivative of `M`** as a differentiation fact, with the (un-shifted)
second-derivative series as its value. -/
lemma kummerM_hasDerivAt2 (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    HasDerivAt (deriv (kummerM a b))
      (∑' n, kummerCoeff a b n * ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * z ^ (n - 1 - 1)))) z := by
  rw [kummerM_deriv_eq_tsum a b hb]
  have ht : IsOpen (Metric.ball (0 : ℝ) (|z| + 1)) := Metric.isOpen_ball
  have h't : IsPreconnected (Metric.ball (0 : ℝ) (|z| + 1)) :=
    (convex_ball 0 (|z| + 1)).isPreconnected
  have hz : z ∈ Metric.ball (0 : ℝ) (|z| + 1) := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) (|z| + 1) := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_zero]; linarith [abs_nonneg z]
  have hg0 : Summable (fun n => kummerCoeff a b n * ((n : ℝ) * (0 : ℝ) ^ (n - 1))) :=
    summable_kummerCoeff_deriv a b hb 0
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) (|z| + 1) →
      ‖kummerCoeff a b n * ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * y ^ (n - 1 - 1)))‖
        ≤ |kummerCoeff a b n| * ((n : ℝ) + 1) ^ 2 * (|z| + 1) ^ n := by
    intro n y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    have _h1 : |y| ≤ |z| + 1 := le_of_lt hy
    have hyn : |y| ^ (n - 1 - 1) ≤ (|z| + 1) ^ n := by
      calc |y| ^ (n - 1 - 1) ≤ (|z| + 1) ^ (n - 1 - 1) := by gcongr
        _ ≤ (|z| + 1) ^ n := by gcongr <;> [linarith [abs_nonneg z]; omega]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast, Nat.abs_cast]
    have hcn := abs_nonneg (kummerCoeff a b n)
    have hnn1 : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
      have h : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    calc |kummerCoeff a b n| * ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * |y| ^ (n - 1 - 1)))
        ≤ |kummerCoeff a b n| * (((n : ℝ) + 1) ^ 2 * (|z| + 1) ^ n) := by
          apply mul_le_mul_of_nonneg_left _ hcn
          calc (n : ℝ) * (((n - 1 : ℕ) : ℝ) * |y| ^ (n - 1 - 1))
              = ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) * |y| ^ (n - 1 - 1) := by ring
            _ ≤ ((n : ℝ) + 1) ^ 2 * (|z| + 1) ^ n :=
                mul_le_mul hnn1 hyn (by positivity) (by positivity)
      _ = |kummerCoeff a b n| * ((n : ℝ) + 1) ^ 2 * (|z| + 1) ^ n := by ring
  exact hasDerivAt_tsum_of_isPreconnected
    (summable_abs_kummer_mul_pow a b hb 2 (R := |z| + 1) (by positivity)) ht h't
    (fun n y _ =>
      ((hasDerivAt_pow (n - 1) y).const_mul ((n : ℝ))).const_mul (kummerCoeff a b n))
    hbound h0 hg0 hz

/-- Reindex the (un-shifted) second-derivative series into the clean shifted-twice form. -/
lemma kummerCoeff_deriv2_reindex (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    ∑' n, kummerCoeff a b n * ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * z ^ (n - 1 - 1)))
      = ∑' k : ℕ, ((k : ℝ) + 1) * ((k : ℝ) + 2) * kummerCoeff a b (k + 2) * z ^ k := by
  have hsum := summable_kummerCoeff_deriv2 a b hb z
  rw [← hsum.sum_add_tsum_nat_add 2, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.cast_zero, zero_mul, mul_zero, Nat.sub_self, zero_add]
  refine tsum_congr (fun k => ?_)
  change kummerCoeff a b (k + 2) * ((((k + 2 : ℕ)) : ℝ) * ((((k + 1 : ℕ)) : ℝ) * z ^ k))
      = ((k : ℝ) + 1) * ((k : ℝ) + 2) * kummerCoeff a b (k + 2) * z ^ k
  push_cast
  ring

/-- The second derivative of `M` in value form: `M''(z) = ∑' k, (k+1)(k+2) c_{k+2} zᵏ`. -/
lemma kummerM_deriv2 (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    deriv (deriv (kummerM a b)) z
      = ∑' k : ℕ, ((k : ℝ) + 1) * ((k : ℝ) + 2) * kummerCoeff a b (k + 2) * z ^ k := by
  rw [(kummerM_hasDerivAt2 a b hb z).deriv, kummerCoeff_deriv2_reindex a b hb z]

/-! ### Kummer's ODE -/

/-- Shifted master bound: `∑ₖ |c_{k+1}| (k+1)² (|z|+1)ᵏ < ∞`. Dominates both `M'` and `z·M''`. -/
lemma summable_abs_kummer_succ_sq (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    Summable (fun k => |kummerCoeff a b (k + 1)| * ((k : ℝ) + 1) ^ 2 * (|z| + 1) ^ k) := by
  have hmaster := summable_abs_kummer_mul_pow a b hb 2 (R := |z| + 1) (by positivity)
  refine Summable.of_norm_bounded ((summable_nat_add_iff 1).2 hmaster) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hpw : (|z| + 1) ^ k ≤ (|z| + 1) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ |z| + 1 by linarith [abs_nonneg z]) k, abs_nonneg z]
  calc |kummerCoeff a b (k + 1)| * ((k : ℝ) + 1) ^ 2 * (|z| + 1) ^ k
      = |kummerCoeff a b (k + 1)| * (((k : ℝ) + 1) ^ 2 * (|z| + 1) ^ k) := by ring
    _ ≤ |kummerCoeff a b (k + 1)| * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2 * (|z| + 1) ^ (k + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact mul_le_mul hsq hpw (by positivity) (by positivity)
    _ = |kummerCoeff a b (k + 1)| * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 * (|z| + 1) ^ (k + 1) := by ring

/-- Summability of the `M'` series. -/
lemma summable_kummer_M' (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k) := by
  refine Summable.of_norm_bounded (summable_abs_kummer_succ_sq a b hb z) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg (show (0:ℝ) ≤ (k:ℝ) + 1 by positivity)]
  have hc := abs_nonneg (kummerCoeff a b (k + 1))
  have hzk : |z| ^ k ≤ (|z| + 1) ^ k := by gcongr; linarith [abs_nonneg z]
  have hkk : (k : ℝ) + 1 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  calc ((k : ℝ) + 1) * |kummerCoeff a b (k + 1)| * |z| ^ k
      = |kummerCoeff a b (k + 1)| * (((k : ℝ) + 1) * |z| ^ k) := by ring
    _ ≤ |kummerCoeff a b (k + 1)| * (((k : ℝ) + 1) ^ 2 * (|z| + 1) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact mul_le_mul hkk hzk (by positivity) (by positivity)
    _ = |kummerCoeff a b (k + 1)| * ((k : ℝ) + 1) ^ 2 * (|z| + 1) ^ k := by ring

/-- Summability of the `z·M'` series `∑ₖ k c_k zᵏ`. -/
lemma summable_kummer_zM' (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    Summable (fun k : ℕ => (k : ℝ) * kummerCoeff a b k * z ^ k) := by
  refine Summable.of_norm_bounded
    (summable_abs_kummer_mul_pow a b hb 1 (R := |z|) (abs_nonneg z)) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
  have hc := abs_nonneg (kummerCoeff a b k)
  calc (k : ℝ) * |kummerCoeff a b k| * |z| ^ k
      = |kummerCoeff a b k| * ((k : ℝ) * |z| ^ k) := by ring
    _ ≤ |kummerCoeff a b k| * (((k : ℝ) + 1) ^ 1 * |z| ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [pow_one]; linarith
    _ = |kummerCoeff a b k| * ((k : ℝ) + 1) ^ 1 * |z| ^ k := by ring

/-- Summability of the `z·M''` series `∑ₖ k(k+1) c_{k+1} zᵏ`. -/
lemma summable_kummer_zM'' (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    Summable (fun k : ℕ => (k : ℝ) * ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k) := by
  refine Summable.of_norm_bounded (summable_abs_kummer_succ_sq a b hb z) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
    abs_of_nonneg (show (0:ℝ) ≤ (k:ℝ) + 1 by positivity)]
  have hc := abs_nonneg (kummerCoeff a b (k + 1))
  have hzk : |z| ^ k ≤ (|z| + 1) ^ k := by gcongr; linarith [abs_nonneg z]
  have hkk : (k : ℝ) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  calc (k : ℝ) * ((k : ℝ) + 1) * |kummerCoeff a b (k + 1)| * |z| ^ k
      = |kummerCoeff a b (k + 1)| * (((k : ℝ) * ((k : ℝ) + 1)) * |z| ^ k) := by ring
    _ ≤ |kummerCoeff a b (k + 1)| * (((k : ℝ) + 1) ^ 2 * (|z| + 1) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact mul_le_mul hkk hzk (by positivity) (by positivity)
    _ = |kummerCoeff a b (k + 1)| * ((k : ℝ) + 1) ^ 2 * (|z| + 1) ^ k := by ring

/-- Index shift `z·M' = ∑ₖ k c_k zᵏ` (the `k=0` term vanishes through the surviving `k`). -/
lemma kummer_zM'_eq (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    ∑' k : ℕ, (k : ℝ) * kummerCoeff a b k * z ^ k
      = z * ∑' k : ℕ, ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k := by
  have hpull : z * ∑' k : ℕ, ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k
      = ∑' k : ℕ, z * (((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k) := tsum_mul_left.symm
  rw [hpull, (summable_kummer_zM' a b hb z).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  refine tsum_congr (fun k => ?_)
  push_cast
  ring

/-- Index shift `z·M'' = ∑ₖ k(k+1) c_{k+1} zᵏ`. -/
lemma kummer_zM''_eq (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    ∑' k : ℕ, (k : ℝ) * ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k
      = z * ∑' k : ℕ, ((k : ℝ) + 1) * ((k : ℝ) + 2) * kummerCoeff a b (k + 2) * z ^ k := by
  have hpull : z * ∑' k : ℕ, ((k : ℝ) + 1) * ((k : ℝ) + 2) * kummerCoeff a b (k + 2) * z ^ k
      = ∑' k : ℕ, z * (((k : ℝ) + 1) * ((k : ℝ) + 2) * kummerCoeff a b (k + 2) * z ^ k) :=
    tsum_mul_left.symm
  rw [hpull, (summable_kummer_zM'' a b hb z).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  refine tsum_congr (fun k => ?_)
  push_cast
  ring

/-- **Kummer's confluent hypergeometric ODE.** `M(a,b,·)` solves
`z M''(z) + (b − z) M'(z) − a M(z) = 0`. The series reductions collapse, via the index shifts
and `kummerCoeff_rec`, to the termwise identity `(k+1)(b+k) c_{k+1} − (a+k) c_k = 0`. -/
theorem kummerM_ode (a b : ℝ) (hb : 0 < b) (z : ℝ) :
    z * deriv (deriv (kummerM a b)) z + (b - z) * deriv (kummerM a b) z
      - a * kummerM a b z = 0 := by
  have hbM' : b * ∑' k : ℕ, ((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k
      = ∑' k : ℕ, b * (((k : ℝ) + 1) * kummerCoeff a b (k + 1) * z ^ k) := tsum_mul_left.symm
  have haM : a * ∑' k : ℕ, kummerCoeff a b k * z ^ k
      = ∑' k : ℕ, a * (kummerCoeff a b k * z ^ k) := tsum_mul_left.symm
  rw [kummerM_deriv2 a b hb z, kummerM_deriv a b hb z,
    show kummerM a b z = ∑' k, kummerCoeff a b k * z ^ k from rfl,
    ← kummer_zM''_eq a b hb z, sub_mul, ← kummer_zM'_eq a b hb z, hbM', haM]
  -- The four series share the index k; combine them into a single, termwise-zero series.
  have sA := summable_kummer_zM'' a b hb z
  have sB := (summable_kummer_M' a b hb z).mul_left b
  have sC := summable_kummer_zM' a b hb z
  have sD := (kummerM_summable a b hb z).mul_left a
  rw [← Summable.tsum_sub sB sC, ← Summable.tsum_add sA (sB.sub sC),
    ← Summable.tsum_sub (sA.add (sB.sub sC)) sD,
    show (0 : ℝ) = ∑' _k : ℕ, (0 : ℝ) from tsum_zero.symm]
  refine tsum_congr (fun k => ?_)
  have hrec := kummerCoeff_rec a b hb k
  linear_combination (z ^ k) * hrec

/-! ### Growth of the non-terminating series

If `a` is not a non-positive integer (so the series does not reduce to a Laguerre polynomial),
the coefficients eventually grow at least as fast as those of `e^{ρ/2}`, forcing `|M(a,b,ρ)|` to
grow at least like `e^{ρ/2}`. This is the analytic input that breaks square-integrability in the
hydrogen radial problem. -/

/-- If `a` is not a non-positive integer, no coefficient vanishes. -/
lemma kummerCoeff_ne_zero (a b : ℝ) (hb : 0 < b) (ha : ∀ p : ℕ, a ≠ -(p : ℝ)) (k : ℕ) :
    kummerCoeff a b k ≠ 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [kummerCoeff_succ]
    have hank : a + (n : ℝ) ≠ 0 := fun h => ha n (by linarith)
    exact div_ne_zero (mul_ne_zero ih hank) (kummer_den_pos b hb n).ne'

/-- Beyond some index, `a + k > 0` and `(a+k)/(b+k) ≥ 1/2`. -/
lemma kummerCoeff_ratio_eventually (a b : ℝ) (_hb : 0 < b) :
    ∃ K : ℕ, ∀ k ≥ K, 0 < a + (k : ℝ) ∧ (1 / 2) * (b + (k : ℝ)) ≤ a + (k : ℝ) := by
  obtain ⟨K, hK⟩ := exists_nat_ge (max (1 - a) (b - 2 * a))
  refine ⟨K, fun k hk => ?_⟩
  have hKk : max (1 - a) (b - 2 * a) ≤ (k : ℝ) := le_trans hK (by exact_mod_cast hk)
  exact ⟨by linarith [le_trans (le_max_left _ _) hKk],
    by linarith [le_trans (le_max_right _ _) hKk]⟩

/-- The absolute coefficients eventually beat the `e^{ρ/2}` ratio: `(k+1)|c_{k+1}| ≥ (1/2)|c_k|`. -/
lemma abs_kummerCoeff_ratio_lower (a b : ℝ) (hb : 0 < b) :
    ∃ K : ℕ, ∀ k ≥ K,
      (1 / 2) * |kummerCoeff a b k| ≤ ((k : ℝ) + 1) * |kummerCoeff a b (k + 1)| := by
  obtain ⟨K, hK⟩ := kummerCoeff_ratio_eventually a b hb
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨hpos, hhalf⟩ := hK k hk
  rw [abs_kummerCoeff_succ a b hb k, abs_of_pos hpos]
  have hbk : (0 : ℝ) < b + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have _hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hratio : (1 : ℝ) / 2 ≤ (a + (k : ℝ)) / (b + (k : ℝ)) := by rw [le_div_iff₀ hbk]; linarith
  calc (1 / 2) * |kummerCoeff a b k|
      ≤ (a + (k : ℝ)) / (b + (k : ℝ)) * |kummerCoeff a b k| :=
        mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    _ = ((k : ℝ) + 1) *
        (|kummerCoeff a b k| * ((a + (k : ℝ)) / ((b + (k : ℝ)) * ((k : ℝ) + 1)))) := by
        field_simp

/-- **Geometric lower bound on the coefficients of a non-terminating series.**
There are `K` and `C > 0` with `|c_k| ≥ C · (1/2)ᵏ / k!` for all `k ≥ K` — i.e. eventually the
coefficients dominate those of `C · e^{ρ/2}`. -/
lemma abs_kummerCoeff_geom_lower (a b : ℝ) (hb : 0 < b) (ha : ∀ p : ℕ, a ≠ -(p : ℝ)) :
    ∃ (K : ℕ) (C : ℝ), 0 < C ∧
      ∀ k ≥ K, C * (1 / 2) ^ k / (k.factorial : ℝ) ≤ |kummerCoeff a b k| := by
  obtain ⟨K, hK⟩ := abs_kummerCoeff_ratio_lower a b hb
  -- `D k = |c_k| · k! / (1/2)^k` is monotone for `k ≥ K`, so `D k ≥ D K = C`.
  set D : ℕ → ℝ := fun k => |kummerCoeff a b k| * (k.factorial : ℝ) / (1 / 2) ^ k with _hD
  have hDpos : ∀ k, 0 < D k := fun k =>
    div_pos (mul_pos (abs_pos.2 (kummerCoeff_ne_zero a b hb ha k)) (by positivity)) (by positivity)
  have hmono : ∀ k, K ≤ k → D K ≤ D k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      refine le_trans ih ?_
      have hr := hK n hn
      change |kummerCoeff a b n| * (n.factorial : ℝ) / (1 / 2) ^ n
        ≤ |kummerCoeff a b (n + 1)| * ((n + 1).factorial : ℝ) / (1 / 2) ^ (n + 1)
      rw [div_le_div_iff₀ (by positivity) (by positivity), Nat.factorial_succ, pow_succ]
      push_cast
      nlinarith [hr, mul_pos (show (0 : ℝ) < (n.factorial : ℝ) by positivity)
        (show (0 : ℝ) < (1 / 2 : ℝ) ^ n by positivity)]
  refine ⟨K, D K, hDpos K, fun k hk => ?_⟩
  have hmk := hmono k hk
  change D K * (1 / 2) ^ k / (k.factorial : ℝ) ≤ |kummerCoeff a b k|
  rw [div_le_iff₀ (by positivity)]
  have hmk' : D K * (1 / 2) ^ k ≤ |kummerCoeff a b k| * (k.factorial : ℝ) := by
    rw [← le_div_iff₀ (show (0 : ℝ) < (1 / 2) ^ k by positivity)]
    exact hmk
  linarith [hmk']

/-- For a non-terminating series the coefficients eventually have a constant sign `σ ∈ {±1}`,
so `σ · c_k = |c_k|` from some `K` on. -/
lemma kummerCoeff_eventually_signed (a b : ℝ) (hb : 0 < b) (ha : ∀ p : ℕ, a ≠ -(p : ℝ)) :
    ∃ (K : ℕ) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧ ∀ k ≥ K, 0 < σ * kummerCoeff a b k := by
  obtain ⟨K, hK⟩ := kummerCoeff_ratio_eventually a b hb
  have hstep : ∀ σ : ℝ, 0 < σ * kummerCoeff a b K → ∀ k ≥ K, 0 < σ * kummerCoeff a b k := by
    intro σ hσK k hk
    induction k, hk using Nat.le_induction with
    | base => exact hσK
    | succ n hn ih =>
      rw [kummerCoeff_succ]
      obtain ⟨hpos, _⟩ := hK n hn
      rw [show σ * (kummerCoeff a b n * (a + (n : ℝ)) / ((b + (n : ℝ)) * ((n : ℝ) + 1)))
          = σ * kummerCoeff a b n * (a + (n : ℝ)) / ((b + (n : ℝ)) * ((n : ℝ) + 1)) from by ring]
      exact div_pos (mul_pos ih hpos) (kummer_den_pos b hb n)
  rcases lt_trichotomy (kummerCoeff a b K) 0 with h | h | h
  · exact ⟨K, -1, Or.inr rfl, hstep (-1) (by simp only [neg_one_mul]; linarith)⟩
  · exact absurd h (kummerCoeff_ne_zero a b hb ha K)
  · exact ⟨K, 1, Or.inl rfl, hstep 1 (by rwa [one_mul])⟩

/-- The scaled exponential series: `∑ₖ (1/2)ᵏ ρᵏ / k! = e^{ρ/2}`. -/
lemma kummer_exp_series_eq (ρ : ℝ) :
    ∑' k : ℕ, (1 / 2 : ℝ) ^ k * ρ ^ k / (k.factorial : ℝ) = Real.exp (ρ / 2) := by
  have h1 : Real.exp (ρ / 2) = ∑' k : ℕ, (ρ / 2) ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    refine tsum_congr (fun k => ?_)
    rw [smul_eq_mul]; ring
  rw [h1]
  refine tsum_congr (fun k => ?_)
  rw [show (1 / 2 : ℝ) ^ k * ρ ^ k = (ρ / 2) ^ k from by rw [← mul_pow]; congr 1; ring]

/-- A power is eventually dominated by `C·e^{ρ/2}` (exponential beats polynomial). -/
lemma kummer_poly_le_exp (M C : ℝ) (hC : 0 < C) (K : ℕ) :
    ∀ᶠ ρ : ℝ in Filter.atTop, M * ρ ^ K ≤ C * Real.exp (ρ / 2) := by
  have htend : Filter.Tendsto (fun ρ : ℝ => M * (ρ ^ K * Real.exp (-(1 / 2) * ρ)))
      Filter.atTop (𝓝 0) := by
    have h0 : Filter.Tendsto (fun ρ : ℝ => ρ ^ K * Real.exp (-(1 / 2) * ρ))
        Filter.atTop (𝓝 0) := by
      refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (K : ℝ) (1 / 2) (by norm_num)).congr' ?_
      filter_upwards with ρ
      rw [Real.rpow_natCast]
    simpa using h0.const_mul M
  filter_upwards [htend.eventually (Iio_mem_nhds hC)] with ρ hρ
  have he : (0 : ℝ) < Real.exp (ρ / 2) := Real.exp_pos _
  rw [show Real.exp (-(1 / 2) * ρ) = (Real.exp (ρ / 2))⁻¹ from by
      rw [← Real.exp_neg]; congr 1; ring,
    show M * (ρ ^ K * (Real.exp (ρ / 2))⁻¹) = M * ρ ^ K / Real.exp (ρ / 2) from by ring,
    div_lt_iff₀ he] at hρ
  linarith

/-- **Function-level exponential lower bound for the non-terminating Kummer function.**
If `a` is not a non-positive integer, then `|M(a,b,ρ)| ≥ C · e^{ρ/2}` for all large `ρ`
(some `C > 0`). This is the growth that breaks square-integrability of the radial wavefunction
unless the Kummer series terminates (i.e. unless `κ = 1/m`). -/
theorem kummerM_abs_exp_lower (a b : ℝ) (hb : 0 < b) (ha : ∀ p : ℕ, a ≠ -(p : ℝ)) :
    ∃ (C R : ℝ), 0 < C ∧ ∀ ρ, R ≤ ρ → C * Real.exp (ρ / 2) ≤ |kummerM a b ρ| := by
  obtain ⟨K₁, C, hC, hgeom⟩ := abs_kummerCoeff_geom_lower a b hb ha
  obtain ⟨K₂, σ, hσval, hsign⟩ := kummerCoeff_eventually_signed a b hb ha
  set K := max K₁ K₂ with _hKdef
  have hσabs : |σ| = 1 := by rcases hσval with h | h <;> rw [h] <;> norm_num
  -- `σ c_k = |c_k| ≥ C (1/2)^k/k!` for `k ≥ K`.
  have hge : ∀ k, K ≤ k → C * (1 / 2) ^ k / (k.factorial : ℝ) ≤ σ * kummerCoeff a b k := by
    intro k hk
    have h2 : 0 < σ * kummerCoeff a b k := hsign k (le_trans (le_max_right _ _) hk)
    have h3 : σ * kummerCoeff a b k = |kummerCoeff a b k| := by
      rw [← abs_of_pos h2, abs_mul, hσabs, one_mul]
    rw [h3]; exact hgeom k (le_trans (le_max_left _ _) hk)
  set d : ℕ → ℝ := fun k => σ * kummerCoeff a b k - C * (1 / 2) ^ k / (k.factorial : ℝ) with hd
  -- Core: `σ M(ρ) ≥ C e^{ρ/2} + P(ρ)`, `P(ρ) = ∑_{k<K} d_k ρ^k`, for `ρ ≥ 0`.
  have hlb : ∀ ρ : ℝ, 0 ≤ ρ →
      C * Real.exp (ρ / 2) + (∑ k ∈ Finset.range K, d k * ρ ^ k) ≤ σ * kummerM a b ρ := by
    intro ρ hρ
    have sf : Summable (fun k => σ * kummerCoeff a b k * ρ ^ k) :=
      ((kummerM_summable a b hb ρ).mul_left σ).congr (fun k => by ring)
    have sg : Summable (fun k => C * (1 / 2) ^ k / (k.factorial : ℝ) * ρ ^ k) :=
      ((Real.summable_pow_div_factorial (ρ / 2)).mul_left C).congr (fun k => by
        rw [show (ρ / 2 : ℝ) ^ k = (1 / 2) ^ k * ρ ^ k from by rw [← mul_pow]; congr 1; ring]; ring)
    have hsumf : ∑' k, σ * kummerCoeff a b k * ρ ^ k = σ * kummerM a b ρ := by
      rw [show kummerM a b ρ = ∑' k, kummerCoeff a b k * ρ ^ k from rfl, ← tsum_mul_left]
      exact tsum_congr (fun k => by ring)
    have hsumg : ∑' k, C * (1 / 2) ^ k / (k.factorial : ℝ) * ρ ^ k = C * Real.exp (ρ / 2) := by
      rw [← kummer_exp_series_eq ρ, ← tsum_mul_left]
      exact tsum_congr (fun k => by ring)
    have hdiff : σ * kummerM a b ρ - C * Real.exp (ρ / 2)
        = ∑' k, (σ * kummerCoeff a b k * ρ ^ k
            - C * (1 / 2) ^ k / (k.factorial : ℝ) * ρ ^ k) := by
      rw [← hsumf, ← hsumg, ← Summable.tsum_sub sf sg]
    have hsplit := (sf.sub sg).sum_add_tsum_nat_add K
    have htail : 0 ≤ ∑' k, (σ * kummerCoeff a b (k + K) * ρ ^ (k + K)
        - C * (1 / 2) ^ (k + K) / ((k + K).factorial : ℝ) * ρ ^ (k + K)) :=
      tsum_nonneg (fun k => by
        rw [sub_nonneg]
        exact mul_le_mul_of_nonneg_right (hge (k + K) (Nat.le_add_left K k))
          (pow_nonneg hρ (k + K)))
    have hheadeq : (∑ k ∈ Finset.range K,
        (σ * kummerCoeff a b k * ρ ^ k - C * (1 / 2) ^ k / (k.factorial : ℝ) * ρ ^ k))
        = ∑ k ∈ Finset.range K, d k * ρ ^ k :=
      Finset.sum_congr rfl (fun k _ => by rw [hd]; ring)
    have hassemble : σ * kummerM a b ρ - C * Real.exp (ρ / 2)
        = (∑ k ∈ Finset.range K, d k * ρ ^ k)
          + ∑' k, (σ * kummerCoeff a b (k + K) * ρ ^ (k + K)
            - C * (1 / 2) ^ (k + K) / ((k + K).factorial : ℝ) * ρ ^ (k + K)) := by
      rw [hdiff, ← hsplit, hheadeq]
    linarith [hassemble, htail]
  -- `|P(ρ)| ≤ M ρ^K` for `ρ ≥ 1`.
  set Mc : ℝ := ∑ k ∈ Finset.range K, |d k| with hMc
  have hPbound : ∀ ρ : ℝ, 1 ≤ ρ → |∑ k ∈ Finset.range K, d k * ρ ^ k| ≤ Mc * ρ ^ K := by
    intro ρ hρ
    calc |∑ k ∈ Finset.range K, d k * ρ ^ k|
        ≤ ∑ k ∈ Finset.range K, |d k * ρ ^ k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range K, |d k| * ρ ^ k :=
          Finset.sum_congr rfl (fun k _ => by
            rw [abs_mul, abs_of_nonneg (pow_nonneg (zero_le_one.trans hρ) k)])
      _ ≤ ∑ k ∈ Finset.range K, |d k| * ρ ^ K := Finset.sum_le_sum (fun k hk => by
            gcongr
            exact le_of_lt (Finset.mem_range.1 hk))
      _ = Mc * ρ ^ K := by rw [hMc, Finset.sum_mul]
  -- Combine with the asymptotic.
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1 (kummer_poly_le_exp Mc (C / 2) (by positivity) K)
  refine ⟨C / 2, max 1 R₀, by positivity, fun ρ hρR => ?_⟩
  have hρ1 : 1 ≤ ρ := le_trans (le_max_left _ _) hρR
  have h1 := hlb ρ (by linarith)
  have h3 := hR₀ ρ (le_trans (le_max_right _ _) hρR)
  have h4 : σ * kummerM a b ρ ≤ |kummerM a b ρ| := by
    calc σ * kummerM a b ρ ≤ |σ * kummerM a b ρ| := le_abs_self _
      _ = |kummerM a b ρ| := by rw [abs_mul, hσabs, one_mul]
  have hPge : -(C / 2) * Real.exp (ρ / 2) ≤ ∑ k ∈ Finset.range K, d k * ρ ^ k := by
    have h5 := neg_le_abs (∑ k ∈ Finset.range K, d k * ρ ^ k)
    have h2 := hPbound ρ hρ1
    linarith
  linarith [h1, h4, hPge]

end Spectra.Kummer

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
-- For laguerre_complete
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Associated Laguerre Polynomials

The associated Laguerre polynomials L_n^α(x), which form the radial
eigenfunctions of the hydrogen atom after appropriate substitutions.

## Main definitions

* `laguerrePolynomial` — `L_n^α(x)`, via the explicit finite series.
* `laguerreWeight` — the weight function `x^α e^{-x}` on `(0, ∞)`.

## Main statements

* `laguerre_recurrence` — three-term recurrence relation.
* `laguerre_differential_eq` — the Laguerre ODE.
* `laguerre_orthogonality` — orthogonality with weight x^α e^{-x}.
* `laguerre_complete` — completeness in L²(ℝ⁺, x^α e^{-x} dx).

## References

* [Szegő, *Orthogonal Polynomials*][szego1975]
* [Abramowitz, Stegun, *Handbook of Mathematical Functions*][abramowitz1965], Ch. 22.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
-/
open MeasureTheory Complex Filter Real Polynomial
open scoped Topology NNReal ENNReal Nat
namespace Spectra.QuantumMechanics.Hydrogen.Radial
/-! ## Definition -/

/-- The generalized binomial coefficient `C(α, k) = α (α-1) ⋯ (α-k+1) / k!`
for a real `α` and a natural number `k`. -/
noncomputable def realBinom (α : ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k, (α - (i : ℝ))) / (k.factorial : ℝ)

/-- Base case for the generalized binomial. -/
@[simp]
lemma realBinom_zero (α : ℝ) : realBinom α 0 = 1 := by
  rw [realBinom]
  simp only [Finset.range_zero, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one]

/-- Recursive step for the generalized binomial: C(α, m+1) = C(α, m) * (α - m) / (m + 1) -/
lemma realBinom_succ (α : ℝ) (m : ℕ) :
    realBinom α (m + 1) = realBinom α m * (α - (m : ℝ)) / (m + 1 : ℝ) := by
  rw [realBinom, realBinom, Finset.prod_range_succ, Nat.factorial_succ]
  push_cast; ring_nf
  grind

/-- The associated Laguerre polynomial L_n^α(x).
    Defined via the explicit series:
      L_n^α(x) = Σ_{k=0}^{n} (-1)^k C(n+α, n-k) x^k / k! -/
noncomputable def laguerrePolynomial (n : ℕ) (α : ℝ) : ℝ → ℝ :=
  fun x => ∑ k ∈ Finset.range (n + 1),
    (-1 : ℝ)^k * realBinom (n + α) (n - k) * (x^k / (k.factorial : ℝ))

/-- Explicit low-degree values. -/
lemma laguerre_zero (α : ℝ) : laguerrePolynomial 0 α = fun _ => 1 := by
  ext x
  simp [laguerrePolynomial, realBinom]

lemma laguerre_one (α : ℝ) :
    laguerrePolynomial 1 α = fun x => 1 + α - x := by
  ext x
  simp only [laguerrePolynomial, realBinom, Finset.sum_range_succ, Finset.sum_range_zero,
             Finset.prod_range_succ, Finset.prod_range_zero, Nat.sub_zero, Nat.sub_self]
  push_cast
  ring

lemma laguerre_two (α : ℝ) :
    laguerrePolynomial 2 α = fun x =>
      (1 / 2) * ((α + 1) * (α + 2) - 2 * (α + 2) * x + x ^ 2) := by
  ext x
  simp only [laguerrePolynomial, realBinom, Finset.sum_range_succ, Finset.sum_range_zero,
             Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast; norm_num
  ring

/-!
### Recurrence relation
-/

/-- Helper to shift the top parameter of the binomial product -/
private lemma prod_shift_top (x : ℝ) (m : ℕ) :
    ∏ i ∈ Finset.range (m + 1), (x - (i : ℝ)) =
    x * ∏ i ∈ Finset.range m, (x - 1 - (i : ℝ)) := by
  rw [Finset.prod_range_succ']
  -- Match the exact coercion `↑0` (Nat.cast 0) instead of a real literal
  have h_zero : x - ↑(0 : ℕ) = x := by push_cast; ring
  rw [h_zero]
  -- Ensure mul_comm only swaps the (Product) * x on the left side
  conv_lhs => rw [mul_comm]
  apply congr_arg (fun y => x * y)
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  ring

/-- Helper lemma: The underlying binomial coefficient identity required to match
    coefficients of x^k in the recurrence relation. -/
private lemma laguerre_coeff_recurrence (n k : ℕ) (α : ℝ) (hn : 1 ≤ n) (hk : k ≤ n - 1) :
    (n + 1 : ℝ) * realBinom (n + 1 + α) (n + 1 - k) =
    (2 * n + α + 1) * realBinom (n + α) (n - k) +
    k * realBinom (n + α) (n - k + 1) -
    (n + α) * realBinom (n - 1 + α) (n - 1 - k) := by
  -- Since k ≤ n - 1, all Nat subtractions are perfectly safe integer math.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n - 1 - k = m := ⟨n - 1 - k, rfl⟩
  have h1 : n + 1 - k = m + 2 := by omega
  have h2 : n - k = m + 1 := by omega
  have h3 : n - k + 1 = m + 2 := by omega
  have hk_val : (k : ℝ) = n - 1 - m := by
    -- 1. Ask omega to prove the Nat equivalence without any subtraction
    have hn_eq : n = m + k + 1 := by omega
    -- 2. Substitute `n` in our real-valued target
    rw [hn_eq]
    -- 3. Push the Real cast down through the Nat addition
    push_cast
    -- 4. Let ring simplify `m + k + 1 - 1 - m` down to `k`
    ring
  rw [h1, h3, h2, hm]
  -- Unfold everything into explicit products and factorials
  rw [realBinom, realBinom, realBinom, realBinom]
  -- Align all products to exactly `∏ i in range m, (n - 1 + α - i)`
  have h_prod1 : ∏ i ∈ Finset.range (m + 2), (n + 1 + α - (i : ℝ)) =
      (n + 1 + α) * (n + α) * ∏ i ∈ Finset.range m, (n - 1 + α - (i : ℝ)) := by
    rw [prod_shift_top, prod_shift_top]
    have h_eq : ∀ (j : ℕ), n + 1 + α - 1 - 1 - (j : ℝ) = n - 1 + α - (j : ℝ) := by intro j; ring
    simp_rw [h_eq]
    ring
  have h_prod2 : ∏ i ∈ Finset.range (m + 1), (n + α - (i : ℝ)) =
      (n + α) * ∏ i ∈ Finset.range m, (n - 1 + α - (i : ℝ)) := by
    rw [prod_shift_top]
    have h_eq : ∀ (j : ℕ), n + α - 1 - (j : ℝ) = n - 1 + α - (j : ℝ) := by intro j; ring
    simp_rw [h_eq]
  have h_prod3 : ∏ i ∈ Finset.range (m + 2), (n + α - (i : ℝ)) =
      (n + α) * (∏ i ∈ Finset.range m, (n - 1 + α - (i : ℝ))) * (n - 1 + α - (m : ℝ)) := by
    rw [prod_shift_top, Finset.prod_range_succ]
    have h_eq : ∀ (j : ℕ), n + α - 1 - (j : ℝ) = n - 1 + α - (j : ℝ) := by intro j; ring
    simp_rw [h_eq]
    ring
  -- Expand factorials down to m!
  have h_fact1 : ((m + 1 : ℕ).factorial : ℝ) = (m + 1 : ℝ) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h_fact2 : ((m + 2 : ℕ).factorial : ℝ) = (m + 2 : ℝ) * (m + 1 : ℝ) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]; push_cast; ring
  -- Substitute products, factorials, and the value of k
  rw [h_prod1, h_prod2, h_prod3, hk_val, h_fact1, h_fact2]
  -- Factor out the common product and factorial as opaque variables to help `ring`
  set P := ∏ i ∈ Finset.range m, (n - 1 + α - (i : ℝ))
  set F := (m.factorial : ℝ)
  field_simp
  ring

/-- **Three-term recurrence.**
    (n+1) L_{n+1}^α(x) = (2n + α + 1 - x) L_n^α(x) - (n + α) L_{n-1}^α(x)-/
theorem laguerre_recurrence (n : ℕ) (α : ℝ) (hn : 1 ≤ n) (x : ℝ) :
    (n + 1 : ℝ) * laguerrePolynomial (n + 1) α x =
    (2 * n + α + 1 - x) * laguerrePolynomial n α x -
    (n + α) * laguerrePolynomial (n - 1) α x := by
  -- 1. Unfold definitions gently. Avoid `add_mul` and `sub_mul` for now
  -- because they shatter the polynomial into too many pieces!
  unfold laguerrePolynomial
  -- 2. Isolate the `x * Sum` term explicitly
  have h_split : (2 * n + α + 1 - x) * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ))) =
      (2 * n + α + 1) * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ))) -
      x * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ))) := by ring
  rw [h_split]
  -- 3. Push the outer constants (including x) INTO their respective sums
  simp_rw [Finset.mul_sum]
  -- 4. Shift the power of x in the target sum
  -- Now sum_congr works perfectly because `x *` is already inside both sides!
  have h_x_shift : ∑ k ∈ Finset.range (n + 1), x * ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ))) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ (k + 1) / (k.factorial : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h_x_shift]
  -- 5. Align the index for the x term sum
  have h_shift : ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k *
    realBinom (n + α) (n - k) * (x ^ (k + 1) / (k.factorial : ℝ)) =
      ∑ i ∈ Finset.range (n + 2), - (i : ℝ) * (-1 : ℝ) ^ i *
        realBinom (n + α) (n + 1 - i) * (x ^ i / (i.factorial : ℝ)) := by
    -- 1. Focus the rewrite exclusively on the right-hand side
    conv_rhs => rw [Finset.sum_range_succ']
    -- 2. The RHS 0th term is now exposed. Since it starts with `-(0:ℝ)`, it vanishes.
    simp only [Nat.cast_zero, neg_zero, zero_mul, add_zero] -- unused: zero_add
    -- 3. Now both sides are perfectly aligned on `Finset.range (n + 1)`
    apply Finset.sum_congr rfl
    intro i _
    -- 4. Clean up `↑(i + 1)` created by the index shift so `ring` can read it
    push_cast
    -- 5. Apply algebraic identities
    have h_pow : (-1 : ℝ) ^ (i + 1) = - (-1 : ℝ) ^ i := by ring
    have h_fact : ((i + 1 : ℕ).factorial : ℝ) = (i + 1 : ℝ) * (i.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [h_pow, h_fact]
    field_simp
  rw [h_shift]
  -- 6. Peel off the top boundary terms so ALL sums strictly match `Finset.range n`
  have h_bound : n - 1 + 1 = n := by omega
  rw [h_bound]
  -- Peel LHS (n+2 -> n+1 -> n)
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  -- Peel RHS1 (n+1 -> n)
  rw [Finset.sum_range_succ]
  -- Peel RHS2 shifted (n+2 -> n+1 -> n)
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  -- 7. Group the core sums and apply our helper lemma
  have h_sums : ∑ i ∈ Finset.range n, (n + 1 : ℝ) * ((-1 : ℝ) ^ i
      * realBinom (n + 1 + α) (n + 1 - i) * (x ^ i / (i.factorial : ℝ))) =
      ∑ i ∈ Finset.range n, (2 * n + α + 1) * ((-1 : ℝ) ^ i
      * realBinom (n + α) (n - i) * (x ^ i / (i.factorial : ℝ))) -
      ∑ i ∈ Finset.range n, - (i : ℝ) * (-1 : ℝ) ^ i
      * realBinom (n + α) (n + 1 - i) * (x ^ i / (i.factorial : ℝ)) -
      ∑ i ∈ Finset.range n, (n + α) * ((-1 : ℝ) ^ i * realBinom (n - 1 + α) (n - 1 - i) * (x ^ i / (i.factorial : ℝ))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hk : i ≤ n - 1 := by
      rw [Finset.mem_range] at hi; omega
    have h_idx : n + 1 - i = n - i + 1 := by omega
    have h_lem := laguerre_coeff_recurrence n i α hn hk
    calc
      (n + 1 : ℝ) * ((-1 : ℝ) ^ i * realBinom (n + 1 + α) (n + 1 - i) * (x ^ i / (i.factorial : ℝ)))
        = ((n + 1 : ℝ) * realBinom (n + 1 + α) (n + 1 - i)) * ((-1 : ℝ) ^ i * (x ^ i / (i.factorial : ℝ))) := by ring
      _ = ((2 * n + α + 1) * realBinom (n + α) (n - i) + i * realBinom (n + α) (n - i + 1) - (n + α) * realBinom (n - 1 + α) (n - 1 - i)) * ((-1 : ℝ) ^ i * (x ^ i / (i.factorial : ℝ))) := by rw [h_lem]
      _ = (2 * n + α + 1) * ((-1 : ℝ) ^ i * realBinom (n + α) (n - i) * (x ^ i / (i.factorial : ℝ))) -
          -(i : ℝ) * (-1 : ℝ) ^ i * realBinom (n + α) (n + 1 - i) * (x ^ i / (i.factorial : ℝ)) -
          (n + α) * ((-1 : ℝ) ^ i * realBinom (n - 1 + α) (n - 1 - i) * (x ^ i / (i.factorial : ℝ))) := by rw [h_idx]; ring
  -- Substitute the combined sums, leaving only the peeled terms
  -- 7.5 Normalize the natural number coercions in the goal to strictly match `h_sums`
  -- This transforms ↑(n + 1) into ↑n + 1 and ↑(n - 1) into ↑n - 1.
  simp_rw [Nat.cast_add, Nat.cast_sub hn, Nat.cast_one]
  -- Substitute the combined sums, leaving only the peeled terms
  rw [h_sums]
  -- 8. Clean up the boundary terms mathematically
  have hsub1 : n + 1 - n = 1 := by omega
  have hsub2 : n - n = 0 := by omega
  have hsub3 : n + 1 - (n + 1) = 0 := by omega
  have hb1 : realBinom (n + 1 + α) 1 = n + 1 + α := by
    rw [realBinom, Finset.prod_range_one, Nat.factorial_one]; push_cast; ring
  have hb2 : realBinom (n + α) 1 = n + α := by
    rw [realBinom, Finset.prod_range_one, Nat.factorial_one]; push_cast; ring
  -- Simplify the boundary binomials to basic algebra and let ring finish it
  simp only [hsub1, hsub2, hsub3, realBinom_zero, hb1, hb2]
  ring


/-! ## Differential equation -/

lemma deriv_laguerrePolynomial (n : ℕ) (α : ℝ) (x : ℝ) :
    deriv (laguerrePolynomial n α) x =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ)^k * realBinom (n + α) (n - k) * ((k : ℝ) * x^(k - 1) / (k.factorial : ℝ)) := by
  unfold laguerrePolynomial
  -- 1. Convert the lambda of a sum into a sum of functions (lambdas)
  have h_sum : (fun (y : ℝ) => ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (y ^ k / (k.factorial : ℝ))) =
      ∑ k ∈ Finset.range (n + 1), fun (y : ℝ) => (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (y ^ k / (k.factorial : ℝ)) := by
    ext y
    simp only [Finset.sum_apply]
  rw [h_sum]
  -- 2. Apply the linearity of the derivative over finite sums
  rw [deriv_sum]
  · apply Finset.sum_congr rfl
    intro k _
    -- Rearrange the function to clearly isolate y^k for deriv_const_mul
    have h_rearrange : (fun (y : ℝ) => (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (y ^ k / (k.factorial : ℝ))) =
        fun (y : ℝ) => ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) / (k.factorial : ℝ)) * y ^ k := by
      ext y
      ring
    rw [h_rearrange]
    -- Differentiate the constant * x^k term
    rw [deriv_const_mul]
    · simp only [differentiableAt_fun_id, deriv_fun_pow,
        deriv_id'', mul_one]
      -- Re-arrange the resulting expression to match the target goal state
      ring
    · -- Differentiability condition for the power rule
      exact differentiableAt_pow k
  · -- Prove differentiability of each term in the sum to satisfy the deriv_sum hypothesis
    intro k _
    have h_pow : DifferentiableAt ℝ (fun y => y ^ k) x := differentiableAt_pow k
    have h_div : DifferentiableAt ℝ (fun y => y ^ k / (k.factorial : ℝ)) x :=
      DifferentiableAt.div_const h_pow (k.factorial : ℝ)
    exact DifferentiableAt.const_mul h_div ((-1 : ℝ) ^ k * realBinom (n + α) (n - k))

lemma deriv2_laguerrePolynomial (n : ℕ) (α : ℝ) (x : ℝ) :
    deriv^[2] (laguerrePolynomial n α) x =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ)^k * realBinom (n + α) (n - k) * ((k : ℝ) * (k - 1 : ℝ) * x^(k - 2) / (k.factorial : ℝ)) := by
  -- Unfold the iterated derivative to expose the inner function.
  -- The `= _` tells Lean to leave the right-hand side of the equation alone.
  change deriv (fun y => deriv (laguerrePolynomial n α) y) x = _
  -- Rewrite the inner derivative using the previous lemma.
  simp_rw [deriv_laguerrePolynomial]
  -- 1. Convert the lambda of a sum into a sum of functions (lambdas)
  have h_sum : (fun (y : ℝ) => ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ))) =
      ∑ k ∈ Finset.range (n + 1), fun (y : ℝ) => (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ)) := by
    ext y
    simp only [Finset.sum_apply]
  rw [h_sum]
  -- 2. Apply the linearity of the derivative over finite sums
  rw [deriv_sum]
  · apply Finset.sum_congr rfl
    intro k _
    -- Rearrange the function to clearly isolate y^(k-1) for deriv_const_mul
    have h_rearrange : (fun (y : ℝ) => (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ))) =
        fun (y : ℝ) => ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (k : ℝ) / (k.factorial : ℝ)) * y ^ (k - 1) := by
      ext y
      ring
    rw [h_rearrange]
    -- Differentiate the constant * y^(k-1) term
    rw [deriv_const_mul]
    · have h_deriv : deriv (fun y : ℝ => y ^ (k - 1)) x = ↑(k - 1) * x ^ (k - 1 - 1) := by
        exact deriv_pow_field (k - 1)
      rw [h_deriv]
      -- Shift the Nat powers algebraically so they match exactly
      have h_pow_sub : k - 1 - 1 = k - 2 := by omega
      rw [h_pow_sub]
      -- The derivative produced `↑(k - 1)`, but our target has `(k : ℝ) - 1`.
      -- Since 0 - 1 = 0 in Nat, they are only strictly equal when multiplied by k.
      have h_cast : (k : ℝ) * ↑(k - 1) = (k : ℝ) * (k - 1 : ℝ) := by
        cases k
        · simp
        · push_cast; ring
      -- Group the k and (k-1) terms together, apply the cast fix, and finish
      calc
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (k : ℝ) / (k.factorial : ℝ) * (↑(k - 1) * x ^ (k - 2))
          = ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) / (k.factorial : ℝ)) * ((k : ℝ) * ↑(k - 1)) * x ^ (k - 2) := by ring
        _ = ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) / (k.factorial : ℝ)) * ((k : ℝ) * (k - 1 : ℝ)) * x ^ (k - 2) := by rw [h_cast]
        _ = (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * (k - 1 : ℝ) * x ^ (k - 2) / (k.factorial : ℝ)) := by ring
    exact differentiableAt_pow (k - 1)
  · -- Prove differentiability of each term in the sum to satisfy the deriv_sum hypothesis
    intro k _
    have h_pow : DifferentiableAt ℝ (fun y => y ^ (k - 1)) x := differentiableAt_pow (k - 1)
    have h_div : DifferentiableAt ℝ (fun y => (k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ)) x := by
      apply DifferentiableAt.div_const
      exact DifferentiableAt.const_mul h_pow (k : ℝ)
    exact DifferentiableAt.const_mul h_div ((-1 : ℝ) ^ k * realBinom (n + α) (n - k))

private lemma laguerre_ode_coeff (n k : ℕ) (α : ℝ) (hn : 1 ≤ n) (hk : k ≤ n - 1) :
    -((k : ℝ) * realBinom (n + α) (n - (k + 1))) -
    ((α + 1) * realBinom (n + α) (n - (k + 1))) -
    ((k : ℝ) * realBinom (n + α) (n - k)) +
    ((n : ℝ) * realBinom (n + α) (n - k)) = 0 := by
  -- With `1 ≤ n` and `k ≤ n - 1`, every Nat subtraction below is genuine.
  -- Set `m := n - 1 - k`, so `n = m + k + 1`, `n - (k+1) = m`, `n - k = m + 1`.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n - 1 - k = m := ⟨n - 1 - k, rfl⟩
  have hn_eq : n = m + k + 1 := by omega
  have h1 : n - (k + 1) = m := by omega
  have h2 : n - k = m + 1 := by omega
  -- Unfold `C(n+α, m+1) = C(n+α, m)·(n+α−m)/(m+1)` and replace `↑n` by `m+k+1`.
  rw [h1, h2, realBinom_succ]
  have hn_real : (n : ℝ) = (m : ℝ) + (k : ℝ) + 1 := by exact_mod_cast hn_eq
  rw [hn_real]
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm1]
  ring

/-- **The Laguerre ODE.**
    x L_n^{α''}(x) + (α + 1 - x) L_n^{α'}(x) + n L_n^α(x) = 0 -/
theorem laguerre_differential_eq (n : ℕ) (α : ℝ) (x : ℝ) :
    x * deriv^[2] (laguerrePolynomial n α) x +
    (α + 1 - x) * deriv (laguerrePolynomial n α) x +
    (n : ℝ) * laguerrePolynomial n α x = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0 : L₀ ≡ 1, so L₀' = L₀'' = 0.
    rw [deriv2_laguerrePolynomial, deriv_laguerrePolynomial]
    simp [laguerrePolynomial]
  -- Main case 1 ≤ n.
  rw [deriv2_laguerrePolynomial, deriv_laguerrePolynomial]
  simp only [laguerrePolynomial]
  -- (α + 1 − x)·L′ = (α+1)·L′ − x·L′.
  have h_split :
      (α + 1 - x) * ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * x ^ (k - 1) / (k.factorial : ℝ))
        = (α + 1) * ∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * x ^ (k - 1) / (k.factorial : ℝ))
          - x * ∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * x ^ (k - 1) / (k.factorial : ℝ)) := by
    ring
  rw [h_split]
  simp_rw [Finset.mul_sum]
  -- Absorb the leading x into the powers of the L'' and (−x·L′) sums.
  have h_absA :
      (∑ k ∈ Finset.range (n + 1),
        x * ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) *
          ((k : ℝ) * (k - 1 : ℝ) * x ^ (k - 2) / (k.factorial : ℝ))))
      = ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) *
          ((k : ℝ) * (k - 1 : ℝ) * x ^ (k - 1) / (k.factorial : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k _
    rcases lt_or_ge k 2 with hk | hk
    · interval_cases k <;> simp
    · have hx : x ^ (k - 1) = x * x ^ (k - 2) := by
        conv_lhs => rw [show k - 1 = (k - 2) + 1 from by omega]
        rw [pow_succ']
      rw [hx]; ring
  have h_absC :
      (∑ k ∈ Finset.range (n + 1),
        x * ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) *
          ((k : ℝ) * x ^ (k - 1) / (k.factorial : ℝ))))
      = ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) *
          ((k : ℝ) * x ^ k / (k.factorial : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hx : x ^ k = x * x ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        rw [pow_succ']
      rw [hx]; ring
  rw [h_absA, h_absC]
  -- Regroup: (low-power sum P) + (high-power sum R).
  have reassoc : ∀ a b c d : ℝ, a + (b - c) + d = (a + b) + (d - c) := fun _ _ _ _ => by ring
  rw [reassoc, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  -- Reindex P (drop the k = 0 term) and peel R (drop the zero k = n term).
  have h_reP :
      (∑ k ∈ Finset.range (n + 1),
        ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) *
            ((k : ℝ) * (k - 1 : ℝ) * x ^ (k - 1) / (k.factorial : ℝ))
          + (α + 1) * ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) *
              ((k : ℝ) * x ^ (k - 1) / (k.factorial : ℝ)))))
      = ∑ i ∈ Finset.range n,
          ((-1 : ℝ) ^ (i + 1) * realBinom (n + α) (n - (i + 1)) *
              (((i + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) - 1 : ℝ) * x ^ ((i + 1) - 1) / ((i + 1).factorial : ℝ))
            + (α + 1) * ((-1 : ℝ) ^ (i + 1) * realBinom (n + α) (n - (i + 1)) *
                (((i + 1 : ℕ) : ℝ) * x ^ ((i + 1) - 1) / ((i + 1).factorial : ℝ)))) := by
    rw [Finset.sum_range_succ']
    push_cast
    ring
  have h_peelR :
      (∑ k ∈ Finset.range (n + 1),
        ((n : ℝ) * ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ)))
          - (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * x ^ k / (k.factorial : ℝ))))
      = ∑ k ∈ Finset.range n,
          ((n : ℝ) * ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ)))
            - (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * x ^ k / (k.factorial : ℝ))) := by
    rw [Finset.sum_range_succ]
    ring
  rw [h_reP, h_peelR, ← Finset.sum_add_distrib]
  -- Each coefficient vanishes by `laguerre_ode_coeff`.
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  trans ((-((i : ℝ) * realBinom (n + α) (n - (i + 1)))
          - ((α + 1) * realBinom (n + α) (n - (i + 1)))
          - ((i : ℝ) * realBinom (n + α) (n - i))
          + ((n : ℝ) * realBinom (n + α) (n - i)))
        * ((-1 : ℝ) ^ i * x ^ i / (i.factorial : ℝ)))
  · rw [show i + 1 - 1 = i from by omega,
        show ((i + 1).factorial : ℝ) = ((i : ℝ) + 1) * (i.factorial : ℝ) from by
          rw [Nat.factorial_succ]; push_cast; ring]
    have hfi : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · rw [laguerre_ode_coeff n i α hn (by omega)]
    ring

/-! ## Smoothness -/

/-- L_n^α is smooth (it is a polynomial for integer α, smooth for all α). -/
lemma laguerre_smooth (n : ℕ) (α : ℝ) :
    ContDiff ℝ ⊤ (laguerrePolynomial n α) := by
  unfold laguerrePolynomial
  exact ContDiff.sum fun k _ => contDiff_const.mul ((contDiff_id.pow k).div_const _)

/-! ## Orthogonality -/

/-- The Laguerre weight function: w(x) = x^α e^{-x} on (0, ∞). -/
noncomputable def laguerreWeight (α : ℝ) (x : ℝ) : ℝ :=
  if 0 < x then x ^ α * Real.exp (-x) else 0

/-- The Laguerre weight is non-negative. -/
lemma laguerreWeight_nonneg (α : ℝ) (_hα : 0 ≤ α) (x : ℝ) :
    0 ≤ laguerreWeight α x := by
  simp only [laguerreWeight]
  split_ifs with h
  · exact mul_nonneg (rpow_nonneg (le_of_lt h) α) (exp_nonneg _)
  · exact le_refl 0

/-- The Laguerre weight is integrable on (0, ∞) for α > -1. -/
lemma laguerreWeight_integrable (α : ℝ) (hα : -1 < α) :
    Integrable (laguerreWeight α) (volume.restrict (Set.Ioi 0)) := by
  show IntegrableOn (laguerreWeight α) (Set.Ioi 0) volume
  -- The Euler Γ-integrand with s = α + 1; converges since 0 < s ⇔ -1 < α.
  have hconv := Real.GammaIntegral_convergent (s := α + 1) (by linarith)
  refine hconv.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hx
  simp only [laguerreWeight, if_pos hx]
  rw [show α + 1 - 1 = α by ring]
  ring

/-- Weight × monomial is integrable on (0, ∞):
  it's the Euler Γ-integrand with s = α + k + 1. -/
lemma laguerreWeight_mul_pow_integrable (α : ℝ) (hα : -1 < α) (k : ℕ) :
    IntegrableOn (fun x : ℝ => laguerreWeight α x * x ^ k) (Set.Ioi 0) volume := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hconv := Real.GammaIntegral_convergent (s := α + k + 1) (by linarith)
  refine hconv.congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hx
  simp only [laguerreWeight, if_pos hx]
  rw [show α + (k : ℝ) + 1 - 1 = α + (k : ℝ) by ring, ← Real.rpow_natCast x k,
      Real.rpow_add hx]
  ring

/-- Self-adjoint (Sturm–Liouville) form of the Laguerre equation:
    `d/dx (xᵃ⁺¹ e⁻ˣ Lₙ'(x)) = −n · xᵃ e⁻ˣ · Lₙ(x)` on `(0, ∞)`. -/
lemma laguerre_self_adjoint (n : ℕ) (α : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y => y ^ (α + 1) * Real.exp (-y) * deriv (laguerrePolynomial n α) y)
      (-(n : ℝ) * (x ^ α * Real.exp (-x)) * laguerrePolynomial n α x) x := by
  -- Derivatives of the three factors at x (x > 0 supplies the rpow side condition).
  have ha : HasDerivAt (fun y : ℝ => y ^ (α + 1)) ((α + 1) * x ^ α) x := by
    have h := (hasDerivAt_id x).rpow_const (p := α + 1) (Or.inl hx.ne')
    simp only [id_eq] at h
    rw [show α + 1 - 1 = α by ring, one_mul] at h
    exact h
  have hb : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := (hasDerivAt_id x).neg
    have h2 := h1.exp
    rw [mul_neg_one] at h2
    exact h2
  have hc : HasDerivAt (deriv (laguerrePolynomial n α))
      (deriv^[2] (laguerrePolynomial n α) x) x := by
    have hdiff : Differentiable ℝ (deriv (laguerrePolynomial n α)) := by
      have heq : deriv (laguerrePolynomial n α) = fun y => ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * realBinom (n + α) (n - k) *
            ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ)) := by
        funext y; exact deriv_laguerrePolynomial n α y
      rw [heq]
      refine ContDiff.differentiable (n := ⊤) ?_ (by simp)
      apply ContDiff.sum
      intro k _
      exact contDiff_const.mul ((contDiff_const.mul (contDiff_id.pow (k - 1))).div_const _)
    exact (hdiff x).hasDerivAt
  -- Product rule, rewrite xᵃ⁺¹ = xᵃ·x, then close with the Laguerre ODE.
  have hxe : (x : ℝ) ^ (α + 1) = x ^ α * x := by rw [Real.rpow_add hx, Real.rpow_one]
  convert (ha.mul hb).mul hc using 1
  simp only [Pi.mul_apply]; rw [hxe]
  linear_combination (-(x ^ α * Real.exp (-x))) * laguerre_differential_eq n α x

/-- `xᶜ · e⁻ˣ → 0` as `x → +∞`, for any real exponent `c`.
    (Exponential decay beats every power.) -/
lemma rpow_mul_exp_neg_tendsto_atTop (c : ℝ) :
    Tendsto (fun x : ℝ => x ^ c * Real.exp (-x)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.exp x / x ^ c) atTop atTop := by
    exact tendsto_exp_div_rpow_atTop c
  refine (h.inv_tendsto_atTop).congr fun x => ?_
  simp [div_eq_mul_inv, ← Real.exp_neg]

/-- The self-adjoint integrand `y ↦ yᵃ⁺¹ e⁻ʸ Lₙ'(y)` is continuous on `[0, ∞)`.
    Continuity at `0` is where `-1 < α` (so `α + 1 > 0`) is needed. -/
lemma laguerre_self_adjoint_continuousOn (n : ℕ) (α : ℝ) (hα : -1 < α) :
    ContinuousOn
      (fun y : ℝ => y ^ (α + 1) * Real.exp (-y) * deriv (laguerrePolynomial n α) y)
      (Set.Ici 0) := by
  have h0 : (0 : ℝ) < α + 1 := by linarith
  -- yᵃ⁺¹ is continuous everywhere, since the exponent is ≥ 0.
  have c1 : Continuous (fun y : ℝ => y ^ (α + 1)) :=
    continuous_iff_continuousAt.2 fun x =>
      Real.continuousAt_rpow_const x (α + 1) (Or.inr h0.le)
  -- e⁻ʸ is continuous.
  have c2 : Continuous (fun y : ℝ => Real.exp (-y)) := by fun_prop
  -- Lₙ' is continuous (Lₙ is smooth); reuse the explicit-sum form from `laguerre_self_adjoint`.
  have c3 : Continuous (deriv (laguerrePolynomial n α)) := by
    have heq : deriv (laguerrePolynomial n α) = fun y => ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) *
          ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ)) := by
      funext y; exact deriv_laguerrePolynomial n α y
    rw [heq]
    refine ContDiff.continuous (𝕜 := ℝ) (n := ⊤) ?_
    apply ContDiff.sum
    intro k _
    exact contDiff_const.mul ((contDiff_const.mul (contDiff_id.pow (k - 1))).div_const _)
  exact ((c1.continuousOn).mul (c2.continuousOn)).mul (c3.continuousOn)

/-- `w · Lₙ · Lₘ` is integrable on `(0, ∞)`. Expand the product of the two
    polynomials into a double sum of monomials, then hit each term with the
    weight–monomial kernel `laguerreWeight_mul_pow_integrable`. -/
lemma laguerreWeight_mul_laguerre_mul_laguerre_integrable
    (n m : ℕ) (α : ℝ) (hα : -1 < α) :
    IntegrableOn
      (fun x => laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial m α x)
      (Set.Ioi 0) := by
  -- Algebraic expansion: w·Lₙ·Lₘ = ∑ᵢ∑ⱼ (cᵢ cⱼ) · (w · xⁱ⁺ʲ).
  have key : ∀ x : ℝ,
      laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial m α x
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (((-1 : ℝ) ^ i * realBinom (n + α) (n - i) / (i.factorial : ℝ))
            * ((-1 : ℝ) ^ j * realBinom (m + α) (m - j) / (j.factorial : ℝ)))
          * (laguerreWeight α x * x ^ (i + j)) := by
    intro x
    simp only [laguerrePolynomial]
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- The double sum is integrable, term by term, via the monomial kernel.
  have hsum : IntegrableOn
      (fun x => ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (((-1 : ℝ) ^ i * realBinom (n + α) (n - i) / (i.factorial : ℝ))
            * ((-1 : ℝ) ^ j * realBinom (m + α) (m - j) / (j.factorial : ℝ)))
          * (laguerreWeight α x * x ^ (i + j)))
      (Set.Ioi 0) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact Integrable.const_mul (laguerreWeight_mul_pow_integrable α hα (i + j)) _
  exact hsum.congr_fun (fun x _ => (key x).symm) measurableSet_Ioi

/-- `Lₙ' · xᵃ⁺¹e⁻ˣ · Lₘ'` is integrable on `(0, ∞)`. Same skeleton as
    `laguerreWeight_mul_laguerre_mul_laguerre_integrable`, but on `(0,∞)`
    we have `xᵃ⁺¹e⁻ˣ = laguerreWeight (α+1) x`, so every monomial lands on
    the weight-monomial kernel at the shifted parameter `α+1`. First
    parameter is the outer derivative, second the inner one. -/
lemma laguerre_deriv_mul_weight_mul_laguerre_deriv_integrable
    (n m : ℕ) (α : ℝ) (hα : -1 < α) :
    IntegrableOn
      (fun x => deriv (laguerrePolynomial n α) x *
        (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial m α) x))
      (Set.Ioi 0) := by
  have key : ∀ x : ℝ, 0 < x →
      deriv (laguerrePolynomial n α) x *
        (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial m α) x)
      = ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1),
          (((-1 : ℝ) ^ a * realBinom (n + α) (n - a) * (a : ℝ) / (a.factorial : ℝ))
            * ((-1 : ℝ) ^ b * realBinom (m + α) (m - b) * (b : ℝ) / (b.factorial : ℝ)))
          * (laguerreWeight (α + 1) x * x ^ ((a - 1) + (b - 1))) := by
    intro x hx
    have hw : x ^ (α + 1) * Real.exp (-x) = laguerreWeight (α + 1) x := by
      simp only [laguerreWeight, if_pos hx]
    rw [deriv_laguerrePolynomial n α x, deriv_laguerrePolynomial m α x, hw,
      Finset.mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  have hsum : IntegrableOn
      (fun x => ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1),
          (((-1 : ℝ) ^ a * realBinom (n + α) (n - a) * (a : ℝ) / (a.factorial : ℝ))
            * ((-1 : ℝ) ^ b * realBinom (m + α) (m - b) * (b : ℝ) / (b.factorial : ℝ)))
          * (laguerreWeight (α + 1) x * x ^ ((a - 1) + (b - 1))))
      (Set.Ioi 0) := by
    apply integrable_finsetSum
    intro a _
    apply integrable_finsetSum
    intro b _
    exact Integrable.const_mul
      (laguerreWeight_mul_pow_integrable (α + 1) (by linarith) ((a - 1) + (b - 1))) _
  exact hsum.congr_fun (fun x hx => (key x hx).symm) measurableSet_Ioi

/-- The boundary integrand `L_n · (xᵃ⁺¹e⁻ˣ · L_m') → 0` as `x → +∞`.
    First index = the undifferentiated polynomial factor, second = the differentiated one.
    `xᵃ⁺¹` is kept as a ring atom, so `key` is pure algebra for all `x`; the rpow merge is
    isolated in `hker`, where `x > 0` holds eventually. -/
lemma laguerre_mul_weight_mul_laguerre_deriv_tendsto_atTop
    (n m : ℕ) (α : ℝ) (_hα : -1 < α) :
    Tendsto
      (fun x => laguerrePolynomial n α x *
        (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial m α) x))
      atTop (𝓝 0) := by
  -- (nat power) · xᵃ⁺¹ · e⁻ˣ → 0, via the decay kernel after merging powers (needs x > 0).
  have hker : ∀ k : ℕ,
      Tendsto (fun x : ℝ => x ^ k * x ^ (α + 1) * Real.exp (-x)) atTop (𝓝 0) := by
    intro k
    refine (rpow_mul_exp_neg_tendsto_atTop ((k : ℝ) + (α + 1))).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    show x ^ ((k : ℝ) + (α + 1)) * Real.exp (-x) = x ^ k * x ^ (α + 1) * Real.exp (-x)
    rw [Real.rpow_add hx, Real.rpow_natCast]
  -- Pure-algebra expansion (all x; xᵃ⁺¹ stays an atom).
  have key : ∀ x : ℝ,
      laguerrePolynomial n α x *
        (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial m α) x)
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
          (((-1 : ℝ) ^ i * realBinom (n + α) (n - i) / (i.factorial : ℝ))
            * ((-1 : ℝ) ^ j * realBinom (m + α) (m - j) * (j : ℝ) / (j.factorial : ℝ)))
          * (x ^ (i + (j - 1)) * x ^ (α + 1) * Real.exp (-x)) := by
    intro x
    rw [deriv_laguerrePolynomial m α x]
    simp only [laguerrePolynomial]
    rw [Finset.mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simp only [key]
  rw [show (0 : ℝ) = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => ?_))
  have h := (hker (i + (j - 1))).const_mul
    (((-1 : ℝ) ^ i * realBinom (n + α) (n - i) / (i.factorial : ℝ))
      * ((-1 : ℝ) ^ j * realBinom (m + α) (m - j) * (j : ℝ) / (j.factorial : ℝ)))
  rwa [mul_zero] at h

/-- **Orthogonality.**
    ∫₀^∞ x^α e^{-x} L_n^α(x) L_m^α(x) dx = Γ(n+α+1)/n! · δ_{nm}-/
theorem laguerre_orthogonality (n m : ℕ) (α : ℝ) (hα : -1 < α) (hnm : n ≠ m) :
    ∫ x in Set.Ioi 0,
      laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial m α x = 0 := by
  have hα1 : (0 : ℝ) < α + 1 := by linarith
  -- L · V is continuous on [0,∞); feeds the lower-endpoint limits.
  have hcont1 : ContinuousOn
      (fun x => laguerrePolynomial m α x *
        (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial n α) x)) (Set.Ici 0) :=
    (laguerre_smooth m α).continuous.continuousOn.mul (laguerre_self_adjoint_continuousOn n α hα)
  have hcont2 : ContinuousOn
      (fun x => laguerrePolynomial n α x *
        (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial m α) x)) (Set.Ici 0) :=
    (laguerre_smooth n α).continuous.continuousOn.mul (laguerre_self_adjoint_continuousOn m α hα)
  -- Lower-endpoint limits: the value at 0 is 0 since 0^(α+1) = 0.
  have hzero1 : Tendsto
      (fun x => laguerrePolynomial m α x *
        (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial n α) x)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((hcont1 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self).tendsto
    simp only [Real.zero_rpow hα1.ne', zero_mul, mul_zero] at h
    exact h
  have hzero2 : Tendsto
      (fun x => laguerrePolynomial n α x *
        (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial m α) x)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((hcont2 0 Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self).tendsto
    simp only [Real.zero_rpow hα1.ne', zero_mul, mul_zero] at h
    exact h
  -- The two `u·v'` integrands are integrable (= -(idx)·w·Lₙ·Lₘ on (0,∞)), via brick 1 rescaled.
  have huv'1 : IntegrableOn
      (fun x => laguerrePolynomial m α x *
        (-(n : ℝ) * (x ^ α * Real.exp (-x)) * laguerrePolynomial n α x)) (Set.Ioi 0) := by
    have hb : IntegrableOn
        (fun x => -(n : ℝ) *
          (laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial m α x)) (Set.Ioi 0) :=
      Integrable.const_mul (laguerreWeight_mul_laguerre_mul_laguerre_integrable n m α hα) _
    refine hb.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at hx
    simp only [laguerreWeight, if_pos hx]
    ring
  have huv'2 : IntegrableOn
      (fun x => laguerrePolynomial n α x *
        (-(m : ℝ) * (x ^ α * Real.exp (-x)) * laguerrePolynomial m α x)) (Set.Ioi 0) := by
    have hb : IntegrableOn
        (fun x => -(m : ℝ) *
          (laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial m α x)) (Set.Ioi 0) :=
      Integrable.const_mul (laguerreWeight_mul_laguerre_mul_laguerre_integrable n m α hα) _
    refine hb.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at hx
    simp only [laguerreWeight, if_pos hx]
    ring
  -- Integration by parts (Sturm–Liouville), both index orders.
  have eq1 := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x _ => ((laguerre_smooth m α).differentiable (by simp) x).hasDerivAt)
    (fun x hx => laguerre_self_adjoint n α hx) huv'1
    (laguerre_deriv_mul_weight_mul_laguerre_deriv_integrable m n α hα) hzero1
    (laguerre_mul_weight_mul_laguerre_deriv_tendsto_atTop m n α hα)
  have eq2 := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x _ => ((laguerre_smooth n α).differentiable (by simp) x).hasDerivAt)
    (fun x hx => laguerre_self_adjoint m α hx) huv'2
    (laguerre_deriv_mul_weight_mul_laguerre_deriv_integrable n m α hα) hzero2
    (laguerre_mul_weight_mul_laguerre_deriv_tendsto_atTop n m α hα)
  simp only [zero_sub, sub_zero] at eq1 eq2
  -- Identify the `u·v'` integrals with scalar multiples of the target I.
  have cLHS1 : (∫ x in Set.Ioi 0,
        laguerrePolynomial m α x * (-(n : ℝ) * (x ^ α * Real.exp (-x)) * laguerrePolynomial n α x))
      = -(n : ℝ) * ∫ x in Set.Ioi 0,
        laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial m α x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Set.mem_Ioi] at hx
    simp only [laguerreWeight, if_pos hx];
    ring
  have cLHS2 : (∫ x in Set.Ioi 0,
        laguerrePolynomial n α x * (-(m : ℝ) * (x ^ α * Real.exp (-x)) * laguerrePolynomial m α x))
      = -(m : ℝ) * ∫ x in Set.Ioi 0,
        laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial m α x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Set.mem_Ioi] at hx
    simp only [laguerreWeight, if_pos hx]
    ring
  -- The two `u'·v` kinetic integrals coincide (integrands commute).
  have cK : (∫ x in Set.Ioi 0,
        deriv (laguerrePolynomial m α) x *
          (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial n α) x))
      = ∫ x in Set.Ioi 0,
        deriv (laguerrePolynomial n α) x *
          (x ^ (α + 1) * Real.exp (-x) * deriv (laguerrePolynomial m α) x) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  rw [cLHS1] at eq1
  rw [cLHS2] at eq2
  rw [cK] at eq1
  -- eq1 : -(n)·I = -K ,  eq2 : -(m)·I = -K  ⟹  (m - n)·I = 0  ⟹  I = 0.
  have hkey := eq1.trans eq2.symm
  have hmn : (m : ℝ) - (n : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm.symm)
  have hprod : ((m : ℝ) - (n : ℝ)) * ∫ x in Set.Ioi 0,
      laguerreWeight α x * laguerrePolynomial n α x * laguerrePolynomial m α x = 0 := by
    linear_combination hkey
  exact (mul_eq_zero.mp hprod).resolve_left hmn

/-- The weighted moment: ∫₀^∞ xᵃ e⁻ˣ · xᵏ dx = Γ(α+k+1). -/
lemma laguerreWeight_mul_pow_moment (α : ℝ) (hα : -1 < α) (k : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * x ^ k = Real.Gamma (α + k + 1) := by
  have hs : (0 : ℝ) < α + k + 1 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
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
    ((n : ℝ) + 1) * (∫ x in Set.Ioi (0 : ℝ), laguerreWeight α x * (laguerrePolynomial (n + 1) α x) ^ 2)
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
            (laguerreWeight α x * laguerrePolynomial (n + 1) α x * laguerrePolynomial (n - 1) α x) := by
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
        (Integrable.add (Integrable.const_mul iC1 (-2 : ℝ)) (Integrable.const_mul iC2 ((n : ℝ) + 2)))
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
    ring
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

lemma laguerreWeight_nonneg' (α : ℝ) (x : ℝ) : 0 ≤ laguerreWeight α x := by
  simp only [laguerreWeight]
  split_ifs with h
  · exact mul_nonneg (Real.rpow_nonneg h.le _) (Real.exp_nonneg _)
  · exact le_refl 0

lemma measurable_laguerreWeight (α : ℝ) : Measurable (laguerreWeight α) := by
  unfold laguerreWeight
  -- `x ↦ x^α * exp (-x)` is measurable; the `if 0 < x` guard is on a measurable set
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  fun_prop

/-! ### Finiteness of `laguerreMeasure α` and integration against the Lebesgue weight `w` -/

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

lemma g_integrable (α : ℝ) (hα : -1 < α) (f : ℝ → ℝ)
    (hf : MemLp f 2 (laguerreMeasure α)) :
    Integrable (fun x => laguerreWeight α x * f x) := by
  have h := g_tilt_integrable α hα f hf (c := 0) (by norm_num)
  simpa using h

/-! ### The complex Laplace/Fourier transform and its analytic properties -/

/-- The open strip `{Re z < 1/2}`; convex hence preconnected, open, contains `0`. -/
def strip : Set ℂ := {z : ℂ | z.re < 1 / 2}

lemma isOpen_strip : IsOpen strip := isOpen_lt Complex.continuous_re continuous_const

lemma convex_strip : Convex ℝ strip :=
  -- `strip = {z | z.re < 1/2}` is a half-space for the ℝ-linear map `Complex.re`.
  convex_halfSpace_lt Complex.reLm.isLinear (1 / 2)
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
    Complex.continuous_ofReal.comp_aestronglyMeasurable (g_integrable α hα f hf).aestronglyMeasurable
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
      have hexp : HasSum (fun n => (z * (x : ℂ)) ^ n / (n.factorial : ℂ)) (Complex.exp (z * x)) := by
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
      rw [show (fun x : ℝ => (laguerreWeight α x : ℂ) * (f x : ℂ) * ((z * x) ^ n / (n.factorial : ℂ)))
            = (fun x : ℝ => ((laguerreWeight α x * f x : ℝ) : ℂ) * ((z * x) ^ n / (n.factorial : ℂ)))
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

lemma ae_zero_of_fourier_zero (g : ℝ → ℝ) (hg : Integrable g)
    (h : ∀ t : ℝ, ∫ x : ℝ, (g x : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) = 0) :
    g =ᵐ[volume] 0 := by
  -- Split g = g⁺ - g⁻, build finite measures μ± = volume.withDensity (ofReal ∘ g±).
  set gp : ℝ → ℝ := fun x => max (g x) 0
  set gn : ℝ → ℝ := fun x => max (-g x) 0
  have hgp : Integrable gp := hg.pos_part          -- name check: pos/neg part of an Integrable fn
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

lemma ae_zero_laguerreMeasure_of_g_ae_zero (α : ℝ) (f : ℝ → ℝ)
    (hg : (fun x => laguerreWeight α x * f x) =ᵐ[volume] 0) :
    f =ᵐ[laguerreMeasure α] 0 := by
  -- μ_α = withDensity (ofReal w).  `f =ᵐ[μ_α] 0` ⟺ ∀ᵐ x ∂volume, ofReal(w x) ≠ 0 → f x = 0.
  rw [laguerreMeasure, EventuallyEq,
      ae_withDensity_iff (measurable_laguerreWeight α).ennreal_ofReal]
  filter_upwards [hg] with x hx hwpos
  -- ofReal (w x) ≠ 0 ⟹ w x > 0 ⟹ (on supp) w x * f x = 0 forces f x = 0
  have hw : 0 < laguerreWeight α x := by
    rw [ENNReal.ofReal_ne_zero_iff] at hwpos  -- name check (`ofReal_ne_zero` / `pos_iff`)
    exact hwpos
  have : laguerreWeight α x * f x = 0 := hx
  exact (mul_eq_zero.1 this).resolve_left hw.ne'

/-! ### Completeness: assembling the main theorem -/

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

/-! ## Generating function -/

/-! ### Bridge: `realBinom` = Mathlib's generalized binomial `Ring.choose` -/

 /-- The falling factorial as a product (no division, no `Ring.choose`). -/
lemma descPochhammer_smeval_prod (α : ℝ) (k : ℕ) :
    (descPochhammer ℤ k).smeval α = ∏ i ∈ Finset.range k, (α - (i : ℝ)) := by
  induction k with
  | zero => simp
  | succ p ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ]
      simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
      ring

/-- Spectra's `realBinom α k = (∏ i<k, (α-i)) / k!` is exactly `Ring.choose α k` on `ℝ`. -/
lemma realBinom_eq_ringChoose (α : ℝ) (k : ℕ) :
    realBinom α k = Ring.choose α k := by
  have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hprod : (∏ i ∈ Finset.range k, (α - (i : ℝ))) = (k.factorial : ℝ) * Ring.choose α k := by
    rw [← descPochhammer_smeval_prod, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  rw [realBinom, hprod, mul_comm, mul_div_assoc, div_self hfac, mul_one]

/-! ### Diagonal coefficient (pure algebra) -/

/-- Grouped by total degree, the `tⁿ` coefficient of the 2-D family is `Lₙ^{(α)}(x)`. -/
lemma genfun_antidiagonal_coeff (α x t : ℝ) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
        ((-1 : ℝ) ^ p.1 * x ^ p.1 / (p.1.factorial : ℝ)
          * Ring.choose (α + (p.1 : ℝ) + (p.2 : ℝ)) p.2) * t ^ (p.1 + p.2)
      = laguerrePolynomial n α x * t ^ n := by
  -- On the antidiagonal, `p.1 + p.2 = n`, so `t^(p.1+p.2) = t^n`.
  have hstep : ∀ p ∈ Finset.antidiagonal n,
      ((-1 : ℝ) ^ p.1 * x ^ p.1 / (p.1.factorial : ℝ)
          * Ring.choose (α + (p.1 : ℝ) + (p.2 : ℝ)) p.2) * t ^ (p.1 + p.2)
      = ((-1 : ℝ) ^ p.1 * x ^ p.1 / (p.1.factorial : ℝ)
          * Ring.choose (α + (p.1 : ℝ) + (p.2 : ℝ)) p.2) * t ^ n := by
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [hp]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]   -- VERIFY exact name
  congr 1
  rw [laguerrePolynomial]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  -- `α + k + (n-k) = n + α`  (uses `k ≤ n` to turn ℕ-subtraction into ℝ-subtraction)
  have harg : α + (k : ℝ) + ((n - k : ℕ) : ℝ) = (n : ℝ) + α := by
    rw [Nat.cast_sub hkn]; ring
  rw [harg, ← realBinom_eq_ringChoose]
  ring

/-! ### Inner sum: binomial series at the shifted parameter -/

/-- For `|t| < 1`, `∑ₘ C(α+k+m, m) tᵐ = (1-t)^(-(α+k+1))`. -/
lemma genfun_binom_hasSum (α t : ℝ) (ht : |t| < 1) (k : ℕ) :
    HasSum (fun m : ℕ => Ring.choose (α + (k : ℝ) + (m : ℝ)) m * t ^ m)
      (1 / (1 - t) ^ (α + (k : ℝ) + 1)) := by
  have hball := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (α + (k : ℝ) + 1)
  -- `t` is in the radius-1 ball
  have hy : t ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal, Metric.mem_ball, dist_zero_right,
        Real.norm_eq_abs]
    exact ht
  have H := hball.hasSum hy
  -- unfold the `ofScalars` application: pₘ(fun _ => t) = C(...) • tᵐ = C(...) * tᵐ
  simp only [FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul, zero_add] at H
  -- H : HasSum (fun m => Ring.choose (α + ↑k + 1 + ↑m - 1) m * t ^ m) (1 / (1 - t) ^ (α + ↑k + 1))
  -- reconcile the index `(α+k+1)+m-1 = α+k+m`
  have hfg : (fun m : ℕ => Ring.choose (α + (k : ℝ) + (m : ℝ)) m * t ^ m)
           = (fun m : ℕ => Ring.choose (α + (k : ℝ) + 1 + (m : ℝ) - 1) m * t ^ m) := by
    funext m
    rw [show α + (k : ℝ) + (m : ℝ) = α + (k : ℝ) + 1 + (m : ℝ) - 1 from by ring]
  rw [hfg]
  exact H

/-! ### Outer sum: exponential factor -/

/-- The `k`-sum reproduces the exponential. -/
lemma genfun_exp_hasSum (x t : ℝ) (_ht1 : (1 : ℝ) - t ≠ 0) :
    HasSum (fun k : ℕ => ((-1 : ℝ) ^ k * x ^ k / (k.factorial : ℝ)) * (t / (1 - t)) ^ k)
      (Real.exp (-(x * t) / (1 - t))) := by
  -- rewrite the summand as `u^k / k!` with `u = -(x t)/(1-t) = (-x)·(t/(1-t))`
  have hfun :
      (fun k : ℕ => ((-1 : ℝ) ^ k * x ^ k / (k.factorial : ℝ)) * (t / (1 - t)) ^ k)
        = (fun k : ℕ => (-(x * t) / (1 - t)) ^ k / (k.factorial : ℝ)) := by
    funext k
    rw [show (-(x * t) / (1 - t)) = (-x) * (t / (1 - t)) from by ring, mul_pow, neg_pow]
    ring
  rw [hfun, Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp _

/-- Absolute-value bound on the generalized binomial coefficient, via `|α|`. -/
lemma realBinom_abs_le (α : ℝ) (k m : ℕ) :
    |Ring.choose (α + (k : ℝ) + (m : ℝ)) m| ≤ Ring.choose (|α| + (k : ℝ) + (m : ℝ)) m := by
  rw [← realBinom_eq_ringChoose, ← realBinom_eq_ringChoose]
  simp only [realBinom]
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (m.factorial : ℝ)), Finset.abs_prod]
  gcongr with i hi
  -- per factor: |(α+k+m) - i| ≤ (|α|+k+m) - i
  rw [Finset.mem_range] at hi
  have hi' : (i : ℝ) < (m : ℝ) := by exact_mod_cast hi
  have hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hb : (0 : ℝ) ≤ (k : ℝ) + (m : ℝ) - (i : ℝ) := by linarith
  rw [show α + (k:ℝ) + (m:ℝ) - (i:ℝ) = α + ((k:ℝ) + (m:ℝ) - (i:ℝ)) from by ring]
  calc |α + ((k:ℝ) + (m:ℝ) - (i:ℝ))|
      ≤ |α| + |(k:ℝ) + (m:ℝ) - (i:ℝ)| := abs_add_le α (↑k + ↑m - ↑i)
    _ = |α| + ((k:ℝ) + (m:ℝ) - (i:ℝ)) := by rw [abs_of_nonneg hb]
    _ = |α| + (k:ℝ) + (m:ℝ) - (i:ℝ) := by ring

/-- Absolute row-sum bound for the binomial series. -/
lemma genfun_binom_abs_tsum_le (α t : ℝ) (ht : |t| < 1) (k : ℕ) :
    ∑' m : ℕ, |Ring.choose (α + (k : ℝ) + (m : ℝ)) m * t ^ m|
      ≤ 1 / (1 - |t|) ^ (|α| + (k : ℝ) + 1) := by
  have hbase := genfun_binom_hasSum |α| |t| (by rwa [abs_abs]) k
  have hterm : ∀ m : ℕ,
      |Ring.choose (α + (k:ℝ) + (m:ℝ)) m * t ^ m|
        ≤ Ring.choose (|α| + (k:ℝ) + (m:ℝ)) m * |t| ^ m := by
    intro m; rw [abs_mul, abs_pow]; gcongr; exact realBinom_abs_le α k m
  have hLHS := (summable_abs_iff.mpr (genfun_binom_hasSum α t ht k).summable).hasSum
  exact hasSum_le hterm hLHS hbase

/-! ### Main theorem -/

/-- **Generating function.**  For `|t| < 1`,
    `Σₙ Lₙ^{(α)}(x) tⁿ = exp(-xt/(1-t)) / (1-t)^{α+1}`. -/
theorem laguerre_generating_function (α x t : ℝ) (ht : |t| < 1) :
    HasSum (fun n : ℕ => laguerrePolynomial n α x * t ^ n)
      (Real.exp (-(x * t) / (1 - t)) / (1 - t) ^ (α + 1)) := by
  have htlt : t < 1 := (abs_lt.mp ht).2
  have ht1 : (0 : ℝ) < 1 - t := by linarith
  have ht1' : (1 : ℝ) - t ≠ 0 := ne_of_gt ht1
  -- The 2-D family.  (If the `set`/unfold dance below misbehaves, inline `F` or
  --  add `F` to the `simp only` sets.)
  set F : ℕ × ℕ → ℝ := fun p =>
      ((-1 : ℝ) ^ p.1 * x ^ p.1 / (p.1.factorial : ℝ)
        * Ring.choose (α + (p.1 : ℝ) + (p.2 : ℝ)) p.2) * t ^ (p.1 + p.2) with hFdef
  --------------------------------------------------------------------------
  -- §1 absolute summability of F over ℕ×ℕ for |t| < 1.
  --------------------------------------------------------------------------
  have hSum : Summable F := by
    have h1abs : (0 : ℝ) < 1 - |t| := by linarith
    -- |F (k,m)| factors as Aₖ · |C(α+k+m,m) tᵐ|
    have hFabs : ∀ k m : ℕ, |F (k, m)|
        = (|x| ^ k / (k.factorial : ℝ) * |t| ^ k) * |Ring.choose (α + (k:ℝ) + (m:ℝ)) m * t ^ m| := by
      intro k m
      simp only [hFdef, abs_mul, abs_pow, abs_div, abs_neg, abs_one, one_pow, Nat.abs_cast, pow_add]
      ring
    -- the exponential majorant for the k-series
    set M : ℕ → ℝ := fun k =>
        (1 / (1 - |t|) ^ (|α| + 1)) * ((|x| * |t| / (1 - |t|)) ^ k / (k.factorial : ℝ)) with hMdef
    have hMsummable : Summable M := by
      simp only [hMdef]
      exact (NormedSpace.expSeries_div_hasSum_exp (|x| * |t| / (1 - |t|))).summable.mul_left _
    have hrowsum_le : ∀ k : ℕ, (∑' m, |F (k, m)|) ≤ M k := by
      intro k
      have hrow := summable_abs_iff.mpr (genfun_binom_hasSum α t ht k).summable
      calc ∑' m, |F (k, m)|
          = (|x|^k / (k.factorial:ℝ) * |t|^k) * ∑' m, |Ring.choose (α+(k:ℝ)+(m:ℕ)) m * t^m| := by
            rw [tsum_congr (hFabs k)]; exact hrow.tsum_mul_left _
        _ ≤ (|x|^k / (k.factorial:ℝ) * |t|^k) * (1 / (1 - |t|) ^ (|α| + (k:ℝ) + 1)) := by
            gcongr; exact genfun_binom_abs_tsum_le α t ht k
        _ = M k := by
            simp only [hMdef]
            rw [show |α| + (k:ℝ) + 1 = (|α| + 1) + (k:ℝ) from by ring, Real.rpow_add h1abs,
                Real.rpow_natCast, div_pow, mul_pow]
            ring
    -- assemble
    rw [← summable_abs_iff]
    refine (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr ⟨fun k => ?_, ?_⟩
    · -- rows
      rw [funext (hFabs k)]
      exact (summable_abs_iff.mpr (genfun_binom_hasSum α t ht k).summable).mul_left _
    · -- k-series
      exact Summable.of_nonneg_of_le
        (fun k => tsum_nonneg fun m => abs_nonneg _) hrowsum_le hMsummable
  --------------------------------------------------------------------------
  -- §2 regroup ℕ×ℕ by antidiagonals; the nth block is the LHS coefficient.
  --------------------------------------------------------------------------
  have hgrouped : HasSum (fun n : ℕ => ∑ p ∈ Finset.antidiagonal n, F p) (∑' p, F p) := by
    have h1 : HasSum (F ∘ ⇑Finset.sigmaAntidiagonalEquivProd) (∑' p, F p) :=
      (Finset.sigmaAntidiagonalEquivProd.hasSum_iff).mpr hSum.hasSum
    refine h1.sigma fun n => ?_
    have hval : (∑ p ∈ Finset.antidiagonal n, F p)
              = ∑ c : ↥(Finset.antidiagonal n),
                  (F ∘ ⇑Finset.sigmaAntidiagonalEquivProd) ⟨n, c⟩ := by
      rw [← Finset.sum_coe_sort (Finset.antidiagonal n) F]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [Finset.sigmaAntidiagonalEquivProd_apply]
    rw [hval]
    exact hasSum_fintype _
  have hLHS : HasSum (fun n : ℕ => laguerrePolynomial n α x * t ^ n) (∑' p, F p) := by
    have h := hgrouped
    simp only [hFdef] at h                                   -- unfold F inside the blocks
    simpa only [genfun_antidiagonal_coeff α x t] using h     -- block n  ↦  Lₙ · tⁿ
  --------------------------------------------------------------------------
  -- §3 sum F by m-then-k to obtain the RHS closed form.
  --------------------------------------------------------------------------
  have hRHS : (∑' p, F p) = Real.exp (-(x * t) / (1 - t)) / (1 - t) ^ (α + 1) := by
    -- inner sum over m, for each fixed k
    have hinner : ∀ k : ℕ, HasSum (fun m : ℕ => F (k, m))
        (((-1 : ℝ) ^ k * x ^ k / (k.factorial : ℝ) * t ^ k)
          * (1 / (1 - t) ^ (α + (k : ℝ) + 1))) := by
      intro k
      have hb := (genfun_binom_hasSum α t ht k).mul_left
        ((-1 : ℝ) ^ k * x ^ k / (k.factorial : ℝ) * t ^ k)
      have hfun :
          (fun m : ℕ =>
              ((-1 : ℝ) ^ k * x ^ k / (k.factorial : ℝ) * t ^ k)
                * (Ring.choose (α + (k : ℝ) + (m : ℝ)) m * t ^ m))
            = fun m : ℕ => F (k, m) := by
        funext m
        simp only [hFdef]
        ring
      rwa [hfun] at hb
    -- outer sum over k
    have houter : HasSum
        (fun k : ℕ =>
            ((-1 : ℝ) ^ k * x ^ k / (k.factorial : ℝ) * t ^ k)
              * (1 / (1 - t) ^ (α + (k : ℝ) + 1)))
        (Real.exp (-(x * t) / (1 - t)) / (1 - t) ^ (α + 1)) := by
      have he := (genfun_exp_hasSum x t ht1').mul_left (1 / (1 - t) ^ (α + 1))
      have hfun :
          (fun k : ℕ => (1 / (1 - t) ^ (α + 1))
              * (((-1 : ℝ) ^ k * x ^ k / (k.factorial : ℝ)) * (t / (1 - t)) ^ k))
            = fun k : ℕ => ((-1 : ℝ) ^ k * x ^ k / (k.factorial : ℝ) * t ^ k)
                * (1 / (1 - t) ^ (α + (k : ℝ) + 1)) := by
        funext k
        simp only [show α + (k : ℝ) + 1 = (α + 1) + (k : ℝ) from by ring,
            Real.rpow_add ht1, Real.rpow_natCast, div_pow]
        ring
      rw [hfun] at he
      rw [show Real.exp (-(x * t) / (1 - t)) / (1 - t) ^ (α + 1)
            = (1 / (1 - t) ^ (α + 1)) * Real.exp (-(x * t) / (1 - t)) from by ring]
      exact he
    -- chain through Fubini
    rw [hSum.tsum_prod' (fun k => (hinner k).summable),
        tsum_congr (fun k => (hinner k).tsum_eq)]
    exact houter.tsum_eq
  rw [hRHS] at hLHS
  exact hLHS


/-! ## Interface summary

### For `RadialEquation.lean`:
- `laguerrePolynomial` — the polynomial solutions
- `laguerre_differential_eq` — to verify they solve the radial ODE
- `laguerre_orthogonality` — for orthonormality of radial wavefunctions
- `laguerre_complete` — for completeness of the discrete eigenfunctions
- `laguerre_norm_sq` — for normalisation constants
-/


end QuantumMechanics.Hydrogen.Radial

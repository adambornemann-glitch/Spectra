/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

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
* `laguerre_smooth` — `L_n^α` is `C^ω` (a polynomial in `x`).
* `laguerre_orthogonality` — off-diagonal (`n ≠ m`) orthogonality with weight
  `x^α e^{-x}`.

## Implementation notes

* `realBinom α k` is a from-scratch generalized binomial coefficient
  `(∏ i<k, (α - i)) / k!`; it agrees with Mathlib's `Ring.choose α k` on `ℝ`
  (see `realBinom_eq_ringChoose` in `Laguerre/GenFun.lean`, which is proved once
  the generating-function machinery is available), so no reimplementation is
  needed here — this file keeps the elementary definition to stay independent
  of that later import.
* `laguerreWeight α x` is `x^α * e^{-x}` for `x > 0` and `0` otherwise (a
  junk-value split, rather than a subtype of `(0,∞)`) because every downstream
  consumer integrates over `Set.Ioi 0` or `Set.Ici 0`, where the two agree; the
  global junk value lets the weight participate in ordinary `ℝ → ℝ` calculus
  lemmas (`ContinuousOn`, `Tendsto`, `deriv`) without subtype bookkeeping.
* `laguerre_orthogonality` is proved by a genuine Sturm–Liouville argument:
  `laguerre_self_adjoint` rewrites the ODE as `d/dx (x^{α+1}e^{-x} L_n') =
  -n·x^α e^{-x} L_n`, then integration by parts (`integral_Ioi_mul_deriv_eq_deriv_mul`)
  applied with `n` and `m` swapped gives two expressions for the same kinetic
  integral, `-n·I` and `-m·I`; since `n ≠ m` forces `I = 0`. The boundary terms
  vanish at `0` (continuity, `0^{α+1} = 0`) and at `∞` (exponential decay beats
  every power, `rpow_mul_exp_neg_tendsto_atTop`).

## References

* [Szegő, *Orthogonal Polynomials*][szego1975]
* [Abramowitz, Stegun, *Handbook of Mathematical Functions*][abramowitz1965], Ch. 22.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
-/
open MeasureTheory Filter Real
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

/-- Explicit value of the degree-one Laguerre polynomial: `L₁^α(x) = 1 + α - x`. -/
lemma laguerre_one (α : ℝ) :
    laguerrePolynomial 1 α = fun x => 1 + α - x := by
  ext x
  simp only [laguerrePolynomial, realBinom, Finset.sum_range_succ, Finset.sum_range_zero,
             Finset.prod_range_succ, Finset.prod_range_zero, Nat.sub_zero, Nat.sub_self]
  push_cast
  ring

/-- Explicit value of the degree-two Laguerre polynomial:
    `L₂^α(x) = ½·((α+1)(α+2) - 2(α+2)x + x²)`. -/
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
    (n+1) L_{n+1}^α(x) = (2n + α + 1 - x) L_n^α(x) - (n + α) L_{n-1}^α(x) -/
theorem laguerre_recurrence (n : ℕ) (α : ℝ) (hn : 1 ≤ n) (x : ℝ) :
    (n + 1 : ℝ) * laguerrePolynomial (n + 1) α x =
    (2 * n + α + 1 - x) * laguerrePolynomial n α x -
    (n + α) * laguerrePolynomial (n - 1) α x := by
  -- 1. Unfold definitions gently. Avoid `add_mul` and `sub_mul` for now
  -- because they shatter the polynomial into too many pieces!
  unfold laguerrePolynomial
  -- 2. Isolate the `x * Sum` term explicitly
  have h_split : (2 * n + α + 1 - x) *
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ))) =
      (2 * n + α + 1) * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ))) -
      x * (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ))) := by ring
  rw [h_split]
  -- 3. Push the outer constants (including x) INTO their respective sums
  simp_rw [Finset.mul_sum]
  -- 4. Shift the power of x in the target sum
  -- Now sum_congr works perfectly because `x *` is already inside both sides!
  have h_x_shift : ∑ k ∈ Finset.range (n + 1),
        x * ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ k / (k.factorial : ℝ))) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (x ^ (k + 1) / (k.factorial : ℝ)) := by
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
    simp only [Nat.cast_zero, neg_zero, zero_mul, add_zero]
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
      ∑ i ∈ Finset.range n,
        (n + α) * ((-1 : ℝ) ^ i * realBinom (n - 1 + α) (n - 1 - i)
          * (x ^ i / (i.factorial : ℝ))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hk : i ≤ n - 1 := by
      rw [Finset.mem_range] at hi; omega
    have h_idx : n + 1 - i = n - i + 1 := by omega
    have h_lem := laguerre_coeff_recurrence n i α hn hk
    calc
      (n + 1 : ℝ) *
          ((-1 : ℝ) ^ i * realBinom (n + 1 + α) (n + 1 - i) * (x ^ i / (i.factorial : ℝ)))
        = ((n + 1 : ℝ) * realBinom (n + 1 + α) (n + 1 - i))
            * ((-1 : ℝ) ^ i * (x ^ i / (i.factorial : ℝ))) := by ring
      _ = ((2 * n + α + 1) * realBinom (n + α) (n - i) + i * realBinom (n + α) (n - i + 1)
              - (n + α) * realBinom (n - 1 + α) (n - 1 - i))
            * ((-1 : ℝ) ^ i * (x ^ i / (i.factorial : ℝ))) := by rw [h_lem]
      _ = (2 * n + α + 1)
            * ((-1 : ℝ) ^ i * realBinom (n + α) (n - i) * (x ^ i / (i.factorial : ℝ))) -
          -(i : ℝ) * (-1 : ℝ) ^ i * realBinom (n + α) (n + 1 - i) * (x ^ i / (i.factorial : ℝ)) -
          (n + α) * ((-1 : ℝ) ^ i * realBinom (n - 1 + α) (n - 1 - i)
            * (x ^ i / (i.factorial : ℝ))) := by rw [h_idx]; ring
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

/-- First derivative of `Lₙ^α`, term-by-term:
    `d/dx Lₙ^α(x) = Σₖ (-1)ᵏ C(n+α, n-k) · k·x^{k-1} / k!`. -/
lemma deriv_laguerrePolynomial (n : ℕ) (α : ℝ) (x : ℝ) :
    deriv (laguerrePolynomial n α) x =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ)^k * realBinom (n + α) (n - k) * ((k : ℝ) * x^(k - 1) / (k.factorial : ℝ)) := by
  unfold laguerrePolynomial
  -- 1. Convert the lambda of a sum into a sum of functions (lambdas)
  have h_sum : (fun (y : ℝ) => ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (y ^ k / (k.factorial : ℝ))) =
      ∑ k ∈ Finset.range (n + 1),
        fun (y : ℝ) => (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (y ^ k / (k.factorial : ℝ)) := by
    ext y
    simp only [Finset.sum_apply]
  rw [h_sum]
  -- 2. Apply the linearity of the derivative over finite sums
  rw [deriv_sum]
  · apply Finset.sum_congr rfl
    intro k _
    -- Rearrange the function to clearly isolate y^k for deriv_const_mul
    have h_rearrange : (fun (y : ℝ) =>
          (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (y ^ k / (k.factorial : ℝ))) =
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

/-- Second derivative of `Lₙ^α`, term-by-term:
    `d²/dx² Lₙ^α(x) = Σₖ (-1)ᵏ C(n+α, n-k) · k(k-1)·x^{k-2} / k!`. -/
lemma deriv2_laguerrePolynomial (n : ℕ) (α : ℝ) (x : ℝ) :
    deriv^[2] (laguerrePolynomial n α) x =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ)^k * realBinom (n + α) (n - k)
        * ((k : ℝ) * (k - 1 : ℝ) * x^(k - 2) / (k.factorial : ℝ)) := by
  -- Unfold the iterated derivative to expose the inner function.
  -- The `= _` tells Lean to leave the right-hand side of the equation alone.
  change deriv (fun y => deriv (laguerrePolynomial n α) y) x = _
  -- Rewrite the inner derivative using the previous lemma.
  simp_rw [deriv_laguerrePolynomial]
  -- 1. Convert the lambda of a sum into a sum of functions (lambdas)
  have h_sum : (fun (y : ℝ) => ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ))) =
      ∑ k ∈ Finset.range (n + 1), fun (y : ℝ) =>
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ)) := by
    ext y
    simp only [Finset.sum_apply]
  rw [h_sum]
  -- 2. Apply the linearity of the derivative over finite sums
  rw [deriv_sum]
  · apply Finset.sum_congr rfl
    intro k _
    -- Rearrange the function to clearly isolate y^(k-1) for deriv_const_mul
    have h_rearrange : (fun (y : ℝ) =>
          (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ))) =
        fun (y : ℝ) =>
          ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (k : ℝ) / (k.factorial : ℝ))
            * y ^ (k - 1) := by
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
        (-1 : ℝ) ^ k * realBinom (n + α) (n - k) * (k : ℝ) / (k.factorial : ℝ)
              * (↑(k - 1) * x ^ (k - 2))
          = ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) / (k.factorial : ℝ))
              * ((k : ℝ) * ↑(k - 1)) * x ^ (k - 2) := by ring
        _ = ((-1 : ℝ) ^ k * realBinom (n + α) (n - k) / (k.factorial : ℝ))
              * ((k : ℝ) * (k - 1 : ℝ)) * x ^ (k - 2) := by rw [h_cast]
        _ = (-1 : ℝ) ^ k * realBinom (n + α) (n - k)
              * ((k : ℝ) * (k - 1 : ℝ) * x ^ (k - 2) / (k.factorial : ℝ)) := by ring
    exact differentiableAt_pow (k - 1)
  · -- Prove differentiability of each term in the sum to satisfy the deriv_sum hypothesis
    intro k _
    have h_pow : DifferentiableAt ℝ (fun y => y ^ (k - 1)) x := differentiableAt_pow (k - 1)
    have h_div : DifferentiableAt ℝ (fun y => (k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ)) x := by
      apply DifferentiableAt.div_const
      exact DifferentiableAt.const_mul h_pow (k : ℝ)
    exact DifferentiableAt.const_mul h_div ((-1 : ℝ) ^ k * realBinom (n + α) (n - k))

/-- The per-coefficient binomial identity that makes the Laguerre ODE series vanish
    term by term: the coefficient of `x^k` in `x·L'' + (α+1-x)·L' + n·L` is zero
    (valid for `1 ≤ n` and `k ≤ n - 1`, where the natural subtractions are genuine). -/
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
            (-1 : ℝ) ^ k * realBinom (n + α) (n - k)
              * ((k : ℝ) * x ^ (k - 1) / (k.factorial : ℝ)) := by
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
              (((i + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) - 1 : ℝ) * x ^ ((i + 1) - 1)
                / ((i + 1).factorial : ℝ))
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
            - (-1 : ℝ) ^ k * realBinom (n + α) (n - k)
              * ((k : ℝ) * x ^ k / (k.factorial : ℝ))) := by
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

/-- L_n^α is analytic: it is a polynomial in `x` for every real `α`.

Here the bare `⊤` exponent is `ω` (`C^ω` = real-analytic, the top of
`WithTop ℕ∞`), and this is deliberate — not the usual `C^∞` spelling
`(⊤ : ℕ∞)`.  Polynomials are honestly analytic, and downstream consumers
(e.g. `Spectrum/SeparatedEigenfunction/Profile.lean`) rely on this via
`.of_le le_top` to extract `ContDiff` at every lower exponent. -/
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
  change IntegrableOn (laguerreWeight α) (Set.Ioi 0) volume
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
  have _hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
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
      refine ContDiff.differentiable (n := (⊤ : ℕ∞)) ?_ (by simp)
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
    refine ContDiff.continuous (𝕜 := ℝ) (n := (⊤ : ℕ∞)) ?_
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
    the identity `xᵃ⁺¹e⁻ˣ = laguerreWeight (α+1) x` holds, so every monomial lands on
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
  rw [show (0 : ℝ) = ∑ i ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (m + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => ?_))
  have h := (hker (i + (j - 1))).const_mul
    (((-1 : ℝ) ^ i * realBinom (n + α) (n - i) / (i.factorial : ℝ))
      * ((-1 : ℝ) ^ j * realBinom (m + α) (m - j) * (j : ℝ) / (j.factorial : ℝ)))
  rwa [mul_zero] at h

/-- **Orthogonality (off-diagonal vanishing).**
    For `n ≠ m`, `∫₀^∞ x^α e^{-x} L_n^α(x) L_m^α(x) dx = 0`.

    This is the `n ≠ m` half of the full orthogonality relation
    `∫₀^∞ x^α e^{-x} L_n^α(x) L_m^α(x) dx = Γ(n+α+1)/n! · δ_{nm}`; the `n = m`
    normalization constant is proved separately as `laguerre_norm_sq` in
    `Laguerre/Complete.lean`. -/
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

end Spectra.QuantumMechanics.Hydrogen.Radial

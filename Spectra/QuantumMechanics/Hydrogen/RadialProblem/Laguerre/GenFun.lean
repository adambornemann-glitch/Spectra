/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Orthogonality
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Complete
/-!
# Generating Function for the Associated Laguerre Polynomials

The exponential generating function `Σₙ Lₙ^{(α)}(x) tⁿ = exp(-xt/(1-t))/(1-t)^{α+1}` for the
associated Laguerre polynomials `laguerrePolynomial` (defined in `Laguerre/Orthogonality.lean`).

## Main statements

* `laguerre_generating_function` — the headline identity, proved by regrouping the absolutely
  summable double series `Σ_{k,m} (-1)^k xᵏ/k! · C(α+k+m,m) · t^(k+m)` over `ℕ × ℕ`: summing along
  antidiagonals recovers the LHS (`Lₙ^{(α)}(x) tⁿ`, via `genfun_antidiagonal_coeff`), while summing
  `m`-then-`k` recovers the RHS closed form (via `genfun_binom_hasSum` and `genfun_exp_hasSum`).

## Implementation notes

* `realBinom_eq_ringChoose` identifies Spectra's from-scratch `realBinom α k` with Mathlib's
  generalized binomial coefficient `Ring.choose α k` on `ℝ`; this is what lets the inner binomial
  series be matched against `Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`.

## References

* [Szegő, *Orthogonal Polynomials*][szego1975]
* [Abramowitz, Stegun, *Handbook of Mathematical Functions*][abramowitz1965], Ch. 22.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
-/
namespace Spectra.QuantumMechanics.Hydrogen.Radial

/-! ## Generating function -/

/-! ### Bridge: `realBinom` = Mathlib's generalized binomial `Ring.choose` -/

/-- The falling factorial as a product (no division, no `Ring.choose`). -/
private lemma descPochhammer_smeval_prod (α : ℝ) (k : ℕ) :
    (descPochhammer ℤ k).smeval α = ∏ i ∈ Finset.range k, (α - (i : ℝ)) := by
  induction k with
  | zero => simp
  | succ p ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ]
      simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
      ring

/-- Spectra's `realBinom α k = (∏ i<k, (α-i)) / k!` is exactly `Ring.choose α k` on `ℝ`. -/
private lemma realBinom_eq_ringChoose (α : ℝ) (k : ℕ) :
    realBinom α k = Ring.choose α k := by
  have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hprod : (∏ i ∈ Finset.range k, (α - (i : ℝ))) = (k.factorial : ℝ) * Ring.choose α k := by
    rw [← descPochhammer_smeval_prod, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  rw [realBinom, hprod, mul_comm, mul_div_assoc, div_self hfac, mul_one]

/-! ### Diagonal coefficient (pure algebra) -/

/-- Grouped by total degree, the `tⁿ` coefficient of the 2-D family is `Lₙ^{(α)}(x)`. -/
private lemma genfun_antidiagonal_coeff (α x t : ℝ) (n : ℕ) :
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
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
private lemma genfun_binom_hasSum (α t : ℝ) (ht : |t| < 1) (k : ℕ) :
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

/-- The `k`-sum reproduces the exponential. Holds for every real `t` (including `t = 1`,
where `(1 - t)` is `0` and division-by-zero junk values on both sides agree). -/
private lemma genfun_exp_hasSum (x t : ℝ) :
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
private lemma realBinom_abs_le (α : ℝ) (k m : ℕ) :
    |Ring.choose (α + (k : ℝ) + (m : ℝ)) m| ≤ Ring.choose (|α| + (k : ℝ) + (m : ℝ)) m := by
  rw [← realBinom_eq_ringChoose, ← realBinom_eq_ringChoose]
  simp only [realBinom]
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (m.factorial : ℝ)), Finset.abs_prod]
  gcongr with i hi
  -- per factor: |(α+k+m) - i| ≤ (|α|+k+m) - i
  rw [Finset.mem_range] at hi
  have hi' : (i : ℝ) < (m : ℝ) := by exact_mod_cast hi
  have _hk' : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hb : (0 : ℝ) ≤ (k : ℝ) + (m : ℝ) - (i : ℝ) := by linarith
  rw [show α + (k:ℝ) + (m:ℝ) - (i:ℝ) = α + ((k:ℝ) + (m:ℝ) - (i:ℝ)) from by ring]
  calc |α + ((k:ℝ) + (m:ℝ) - (i:ℝ))|
      ≤ |α| + |(k:ℝ) + (m:ℝ) - (i:ℝ)| := abs_add_le α (↑k + ↑m - ↑i)
    _ = |α| + ((k:ℝ) + (m:ℝ) - (i:ℝ)) := by rw [abs_of_nonneg hb]
    _ = |α| + (k:ℝ) + (m:ℝ) - (i:ℝ) := by ring

/-- Absolute row-sum bound for the binomial series. -/
private lemma genfun_binom_abs_tsum_le (α t : ℝ) (ht : |t| < 1) (k : ℕ) :
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
  -- The 2-D family whose antidiagonal sums give the LHS and whose row/column
  -- sums (m-then-k) give the RHS closed form.
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
        = (|x| ^ k / (k.factorial : ℝ) * |t| ^ k)
          * |Ring.choose (α + (k:ℝ) + (m:ℝ)) m * t ^ m| := by
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
      have he := (genfun_exp_hasSum x t).mul_left (1 / (1 - t) ^ (α + 1))
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

end Spectra.QuantumMechanics.Hydrogen.Radial

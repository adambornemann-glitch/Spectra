/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.PositiveDefinite.Unitary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fejér means of a unitary's autocorrelation sequence

Given a unitary `U : H →L[ℂ] H`, a vector `ψ : H`, and its autocorrelation sequence
`c(n) = unitaryCorrelation U ψ n` (see `PositiveDefinite/Unitary.lean`), this file builds the
**Fejér mean density** `F_N(θ) = ∑_{|n|≤N} w_N(n) c(n) e^{-inθ}`, a trigonometric polynomial
weighted by the **Fejér weights** `w_N(n) = 1 - |n|/(N+1)`, and proves the two facts the Herglotz
construction needs: `F_N(θ) ≥ 0` for every `θ` (so `F_N(θ) dθ/2π` is a genuine positive measure on
the circle), and `F_N` has total mass `2π · c(0) = 2π‖ψ‖²`.

## Main definitions

* `fejerWeight`: the Fejér weight `w_N(n) = 1 - |n|/(N+1)` for `|n| ≤ N`, else `0`.
* `fejerMeanDensity`: the trigonometric polynomial `F_N(θ) = ∑_{|n|≤N} w_N(n) c(n) e^{-inθ}`.

## Main results

* `fejerMeanDensity_nonneg`: `F_N(θ) ≥ 0` for every `θ`.
* `set_integral_cexp_neg_int`: Fourier orthogonality, `∫_{[0,2π]} e^{-inθ} dθ = 2π` if `n = 0`
  else `0`.
* `fejerMeanDensity_integral`: `∫_{[0,2π]} F_N(θ) dθ = 2π · c(0)`.

## Implementation notes

The positivity proof goes through a diagonal-reindexing identity (`exp_conj_mul`, `fiber_count`,
`double_sum_eq_weighted`, `fejerWeight_mul_eq`, `fejer_reindex`) that rewrites `(N+1) · F_N(θ)` as
the same double sum `unitaryCorrelation_positive_definite` already shows is `≥ 0`, for the specific
coefficients `α_j = e^{-ijθ}`. This avoids ever constructing the classical Fejér kernel
`K_N(θ) = ∑_{|n|≤N} w_N(n) e^{-inθ}` as a real-valued function on the circle and separately proving
*it* is nonnegative (the usual textbook route, via `K_N(θ) = (N+1)⁻¹ (sin((N+1)θ/2)/sin(θ/2))²`) —
the double-sum identity gets positivity directly from `U`'s unitarity, with no trigonometric
identity or `θ = 0` case split needed.

## References

* L. Fejér, *Untersuchungen über Fouriersche Reihen*, Mathematische Annalen **58** (1904), 51–69 —
  the original Fejér kernel and Cesàro-summability construction.
* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press, 2004,
  §I.3 — the Fejér kernel's positivity and approximate-identity properties.
* G. Herglotz, *Über Potenzreihen mit positivem, reellen Teil im Einheitskreis*, Leipziger
  Berichte **63** (1911), 501–511 — the theorem this file's Fejér means are ultimately built
  towards (see `PositiveDefinite/Unitary.lean`).

## Tags

Fejér kernel, Fejér mean, trigonometric polynomial, Fourier orthogonality, positive-definite
sequence
-/

open Complex MeasureTheory
open Spectra.PositiveDefinite
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Herglotz

section FejerMeans

variable (U : H →L[ℂ] H)

/-- The **Fejér weight**: `w_N(n) = 1 - |n|/(N+1)` for `|n| ≤ N`, else 0.
This is the Fourier coefficient of the Fejér kernel. -/
noncomputable def fejerWeight (N : ℕ) (n : ℤ) : ℝ :=
  if n.natAbs ≤ N then 1 - n.natAbs / (N + 1 : ℝ) else 0

/-- `w_N(0) = 1`. -/
lemma fejerWeight_zero (N : ℕ) : fejerWeight N 0 = 1 := by
  simp [fejerWeight]

/-- The **Fejér mean density** at angle `θ`:
`F_N(θ) = ∑_{|n|≤N} w_N(n) c(n) e^{-inθ}`.

This is a trigonometric polynomial. When multiplied by `dθ/(2π)`, it
gives a positive measure on `𝕋`. -/
noncomputable def fejerMeanDensity (ψ : H) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    (fejerWeight N n : ℂ) * unitaryCorrelation U ψ n * exp (-I * n * θ)

/-- `conj(e^{-ijθ}) · e^{-ikθ} = e^{-i(k-j)θ}`: collapsing a conjugate-times product of phases. -/
private lemma exp_conj_mul (j k : ℤ) (θ : ℝ) :
    starRingEnd ℂ (exp (-I * ↑j * ↑θ)) * exp (-I * ↑k * ↑θ) =
    exp (-I * ↑(k - j) * ↑θ) := by
  have hconj : starRingEnd ℂ (exp (-I * ↑j * ↑θ)) = exp (I * ↑j * ↑θ) := by
    have : starRingEnd ℂ (exp (-I * ↑j * ↑θ)) = exp (starRingEnd ℂ (-I * ↑j * ↑θ)) := by
      exact Eq.symm (exp_conj (-I * ↑j * ↑θ))
    rw [this, map_mul, map_mul, map_neg]
    simp only [conj_I, neg_neg, map_intCast, conj_ofReal]
  rw [hconj, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- For `n ∈ [-N, N]`, the number of pairs `(j,k) ∈ {0,...,N}²` with
`k - j = n` is `N + 1 - |n|`. -/
private lemma fiber_count (N : ℕ) (n : ℤ) (hn : n ∈ Finset.Icc (-(N : ℤ)) N) :
    (((Finset.univ : Finset (Fin (N + 1))) ×ˢ Finset.univ).filter
      fun p : Fin (N + 1) × Fin (N + 1) => (↑p.2 : ℤ) - ↑p.1 = n).card =
    N + 1 - n.natAbs := by
  have hn_le : n.natAbs ≤ N := by
    simp only [Finset.mem_Icc] at hn; omega
  set S := ((Finset.univ ×ˢ Finset.univ).filter
    fun p : Fin (N + 1) × Fin (N + 1) => (↑p.2 : ℤ) - ↑p.1 = n)
  rw [show N + 1 - n.natAbs = (Finset.range (N + 1 - n.natAbs)).card
    from (Finset.card_range _).symm]
  cases n with
  | ofNat m =>
    -- n = m ≥ 0, fiber = {(j, j+m) | j + m ≤ N}
    -- Projection to first coordinate bijects with range(N+1-m)
    simp only [Int.ofNat_eq_natCast, Int.natAbs_natCast]
    have hm : m ≤ N := hn_le
    apply Finset.card_bij (fun p _ => p.1.val)
    · -- image lands in range
      intro ⟨j, k⟩ hp
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
                  true_and, Finset.mem_range, Int.ofNat_eq_natCast] at hp ⊢
      have _hk := k.isLt; omega
    · -- injective: j determines k = j + m
      intro ⟨j₁, k₁⟩ h₁ ⟨j₂, k₂⟩ h₂ heq
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
                  true_and] at h₁ h₂
      have hj : j₁ = j₂ := Fin.ext heq
      have hk : k₁ = k₂ := Fin.ext (by omega)
      exact Prod.ext hj hk
    · -- surjective: given i < N+1-m, take (i, i+m)
      intro i hi
      rw [Finset.mem_range] at hi
      refine ⟨(⟨i, by omega⟩, ⟨i + m, by omega⟩), ?_, rfl⟩
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
                  true_and, Int.ofNat_eq_natCast]
      push_cast; omega
  | negSucc m =>
    -- n = -(m+1), fiber = {(k+m+1, k) | k+m+1 ≤ N}
    -- Projection to second coordinate bijects with range(N-m)
    simp only [Int.natAbs_negSucc]
    have hm : m + 1 ≤ N := hn_le
    apply Finset.card_bij (fun p _ => p.2.val)
    · -- image lands in range
      intro ⟨j, k⟩ hp
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
                  true_and, Finset.mem_range] at hp ⊢
      have _hj := j.isLt; omega
    · -- injective: k determines j = k + m + 1
      intro ⟨j₁, k₁⟩ h₁ ⟨j₂, k₂⟩ h₂ heq
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
                  true_and] at h₁ h₂
      have hk : k₁ = k₂ := Fin.ext heq
      have hj : j₁ = j₂ := Fin.ext (by omega)
      exact Prod.ext hj hk
    · -- surjective: given i < N-m, take (i+m+1, i)
      intro i hi
      rw [Finset.mem_range] at hi
      refine ⟨(⟨i + m + 1, by omega⟩, ⟨i, by omega⟩), ?_, rfl⟩
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
                  true_and]
      push_cast; omega

/-- Diagonal reindex: `∑_{j,k < N+1} g(k-j) = ∑_{n=-N}^{N} (N+1-|n|)·g(n)`. -/
private lemma double_sum_eq_weighted (g : ℤ → ℂ) (N : ℕ) :
    ∑ j : Fin (N + 1), ∑ k : Fin (N + 1), g ((↑k : ℤ) - ↑j) =
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (↑(N + 1 - n.natAbs) : ℂ) * g n := by
  set π : Fin (N+1) × Fin (N+1) → ℤ := fun p => (↑p.2 : ℤ) - ↑p.1
  have hπ : ∀ p ∈ (Finset.univ : Finset (Fin (N+1) × Fin (N+1))),
      π p ∈ Finset.Icc (-(N : ℤ)) N := by
    intro ⟨j, k⟩ _; simp only [π, Finset.mem_Icc]; constructor <;> omega
  -- Double sum = sum over product type
  have h1 : ∑ j : Fin (N + 1), ∑ k : Fin (N + 1), g ((↑k : ℤ) - ↑j) =
      ∑ p : Fin (N + 1) × Fin (N + 1), g (π p) := by
    rw [← Finset.sum_product']; rfl
  -- Fiberwise decomposition
  rw [h1, ← Finset.univ_product_univ]
  simp only [Finset.univ_product_univ, ← Finset.sum_fiberwise_of_maps_to hπ]
  apply Finset.sum_congr rfl
  intro n hn
  -- On the fiber, g(π p) = g(n), so sum = card • g(n)
  rw [Finset.sum_congr rfl (fun p hp => by
        rw [show π p = n from (Finset.mem_filter.mp hp).2]),
      Finset.sum_const, nsmul_eq_mul]
  congr 1
  -- Card of fiber = N+1-|n|
  have h_filt : ((Finset.univ ×ˢ Finset.univ).filter fun p => π p = n) =
      ((Finset.univ ×ˢ Finset.univ).filter
        fun p : Fin (N+1) × Fin (N+1) => (↑p.2 : ℤ) - ↑p.1 = n) := by
    rfl
  rw [← fiber_count N n hn]
  rw [h_filt]
  exact Nat.cast_inj.mpr rfl

/-- Clearing the Fejér weight's denominator: `(N+1)·w_N(n) = N+1-|n|` for `|n| ≤ N`. -/
private lemma fejerWeight_mul_eq (N : ℕ) (n : ℤ) (hn : n.natAbs ≤ N) :
    (↑(N + 1) : ℂ) * (↑(fejerWeight N n) : ℂ) = ↑(N + 1 - n.natAbs) := by
  simp only [fejerWeight, if_pos hn]
  have _hN : (N + 1 : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub (by omega : n.natAbs ≤ N + 1)]
  field_simp

/-- The double sum with exponential weights equals `(N+1) * F_N(θ)`.
This is the classical identity connecting the Fejér kernel to its
square factorization: `∑_{j,k} e^{i(j-k)θ} c(k-j) = (N+1) F_N(θ)`. -/
private lemma fejer_reindex (ψ : H) (N : ℕ) (θ : ℝ) :
    (∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
      starRingEnd ℂ (exp (-I * ↑(↑j : ℤ) * ↑θ)) *
        exp (-I * ↑(↑k : ℤ) * ↑θ) *
        unitaryCorrelation U ψ (↑k - ↑j)).re =
    (↑(N + 1) : ℝ) * (fejerMeanDensity U ψ N θ).re := by
  -- Step 1: Simplify exponentials
  have h_exp : ∀ j k : Fin (N + 1),
      starRingEnd ℂ (exp (-I * ↑(↑j : ℤ) * ↑θ)) *
        exp (-I * ↑(↑k : ℤ) * ↑θ) *
        unitaryCorrelation U ψ (↑k - ↑j) =
      exp (-I * ↑((↑k : ℤ) - ↑j) * ↑θ) *
        unitaryCorrelation U ψ (↑k - ↑j) := by
    intro j k; rw [mul_assoc, ← exp_conj_mul]; ring
  simp_rw [h_exp]
  set g : ℤ → ℂ := fun n => exp (-I * ↑n * ↑θ) * unitaryCorrelation U ψ n
  -- Step 2: Suffices to show complex identity
  suffices h : ∑ j : Fin (N + 1), ∑ k : Fin (N + 1), g ((↑k : ℤ) - ↑j) =
      (↑(N + 1) : ℂ) * fejerMeanDensity U ψ N θ by
    have h_re : (↑(N + 1) : ℝ) * (fejerMeanDensity U ψ N θ).re =
        ((↑(N + 1) : ℂ) * fejerMeanDensity U ψ N θ).re := by
      simp [Complex.mul_re]
    rw [h_re]; exact congrArg Complex.re h
  -- Step 3: LHS = ∑_n (N+1-|n|) * g(n) via double_sum_eq_weighted
  rw [double_sum_eq_weighted g N]
  -- Step 4: RHS = ∑_n (N+1)*w(n) * stuff, show termwise equality
  simp only [fejerMeanDensity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn_abs : n.natAbs ≤ N := by simp only [Finset.mem_Icc] at hn; omega
  rw [← fejerWeight_mul_eq N n hn_abs]
  ring

/-- The real part of the Fejér mean density is non-negative: `Re F_N(θ) ≥ 0`. (Real-valuedness,
i.e. `Im F_N(θ) = 0`, is proved separately in `Herglotz.FejerMeasure`, not here.) -/
lemma fejerMeanDensity_nonneg (hU : Operator.Unitary U) (ψ : H) (N : ℕ) (θ : ℝ) :
    0 ≤ (fejerMeanDensity U ψ N θ).re := by
  have h_pd := unitaryCorrelation_positive_definite U hU ψ (N + 1)
    (fun j => exp (-I * ↑(↑j : ℤ) * ↑θ))
  rw [fejer_reindex U ψ N θ] at h_pd
  have hN : (0 : ℝ) < ↑(N + 1) := Nat.cast_pos.mpr (Nat.succ_pos N)
  exact nonneg_of_mul_nonneg_right h_pd hN

/-- The antiderivative of `θ ↦ exp(c · θ)` for nonzero `c : ℂ`. -/
private lemma hasDerivAt_cexp_div {c : ℂ} (hc : c ≠ 0) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => exp (c * ↑t) / c) (exp (c * ↑θ)) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 θ := (hasDerivAt_id θ).ofReal_comp
  have h2 := (h1.const_mul c).cexp.div_const c
  simp only [mul_one] at h2
  rwa [mul_div_cancel_right₀ _ hc] at h2

/-- Continuity of `θ ↦ exp(-inθ)`. -/
private lemma continuous_cexp_neg_int_mul (n : ℤ) :
    Continuous (fun θ : ℝ => exp (-I * ↑n * ↑θ)) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- **Fourier orthogonality**: `∫_{[0,2π]} exp(-inθ) dθ = 2π` if `n = 0`, else `0`. -/
lemma set_integral_cexp_neg_int (n : ℤ) :
    ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
      exp (-I * ↑n * ↑θ) =
    if n = 0 then ↑(2 * Real.pi) else 0 := by
  split
  · -- n = 0: integrand is 1, integral = 2π
    next h =>
      subst h
      simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero]
      rw [setIntegral_const, Measure.real,
          Real.volume_Icc, sub_zero,
          ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      exact (@Complex.real_smul (2 * Real.pi) 1).trans (mul_one _)
  · -- n ≠ 0: FTC gives 0
    next hn =>
      set c := -I * (↑n : ℂ) with hc_def
      have hc : c ≠ 0 := by
        simp only [hc_def, neg_mul, ne_eq, neg_eq_zero]
        exact mul_ne_zero I_ne_zero (Int.cast_ne_zero.mpr hn)
      -- Rewrite integrand to use c
      have h_fn : (fun θ : ℝ => exp (-I * ↑n * ↑θ)) =
          fun (θ : ℝ) => exp (c * (↑θ : ℂ)) := by
        ext θ; congr 1
      rw [h_fn]
      -- Convert: Icc set integral → Ioc set integral → interval integral
      have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
      -- Continuity (needed for integrability)
      have h_cts : Continuous (fun θ : ℝ => exp (c * ↑θ)) :=
        Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
      -- Apply FTC
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x _ => hasDerivAt_cexp_div hc x)
            (h_cts.intervalIntegrable _ _)]
      -- Goal: exp(c * ↑(2 * Real.pi)) / c - exp(c * ↑0) / c = 0
      have h_period : exp (c * ↑(2 * Real.pi)) = 1 := by
        have : c * ↑(2 * Real.pi) = ↑(-n) * (2 * ↑Real.pi * I) := by
          simp [hc_def]; ring
        rw [this, Complex.exp_int_mul_two_pi_mul_I]
      rw [h_period, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self]

/-- The integral of the Fejér mean density over `[0, 2π)` is `2π · c(0)` — which is `2π‖ψ‖²` after
one more substitution via `unitaryCorrelation_zero`, not performed here. -/
lemma fejerMeanDensity_integral (ψ : H) (N : ℕ) :
    ∫ θ in Set.Icc 0 (2 * Real.pi),
      fejerMeanDensity U ψ N θ = 2 * Real.pi * unitaryCorrelation U ψ 0 := by
  simp only [fejerMeanDensity]
  -- Step 1: Exchange finite sum and Bochner integral
  rw [MeasureTheory.integral_finsetSum _ (fun n _ => ?_)]
  · -- Step 2: evaluate each integral and collapse sum
    have step : ∀ i ∈ Finset.Icc (-(N : ℤ)) N,
        (∫ a in Set.Icc (0 : ℝ) (2 * Real.pi),
          (↑(fejerWeight N i) : ℂ) * unitaryCorrelation U ψ i * exp (-I * ↑i * ↑a)) =
        ↑(fejerWeight N i) * unitaryCorrelation U ψ i *
          (if i = 0 then ↑(2 * Real.pi) else 0) := by
      intro i _
      show _ = _
      rw [show (∫ a in Set.Icc (0 : ℝ) (2 * Real.pi),
            (↑(fejerWeight N i) : ℂ) * unitaryCorrelation U ψ i * exp (-I * ↑i * ↑a)) =
            ↑(fejerWeight N i) * unitaryCorrelation U ψ i *
            ∫ a in Set.Icc (0 : ℝ) (2 * Real.pi), exp (-I * ↑i * ↑a)
          from integral_const_mul _ _, set_integral_cexp_neg_int]
    rw [Finset.sum_congr rfl step]
    simp [Finset.sum_ite_eq']
    simp only [fejerWeight_zero, ofReal_one, one_mul]
    ring
  · -- Integrability: each summand is continuous on compact Icc
    exact (continuous_const.mul (continuous_cexp_neg_int_mul n)).continuousOn.integrableOn_compact
      isCompact_Icc

end FejerMeans
end Spectra.Herglotz

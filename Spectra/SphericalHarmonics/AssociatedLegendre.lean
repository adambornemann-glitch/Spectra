/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
/-!
# Associated Legendre polynomials

The associated Legendre functions `P_ℓ^m(x)`, built from the Rodrigues formula,
together with their regularity, the Sturm–Liouville form of the associated
Legendre ODE, orthogonality (`ℓ ≠ ℓ'`, fixed `m`), and the `L²[-1,1]`
normalisation `∫_{-1}^1 (P_ℓ^m)² = (2/(2ℓ+1))·(ℓ+m)!/(ℓ-m)!`.

These are the one-variable special functions underlying the spherical harmonics
`Y_ℓ^m` (see `Spectra.SphericalHarmonics.Basic`); this file is pure real
analysis on `[-1,1]` and knows nothing about the sphere.

## Notes

* `AssociatedLegendre` is a *real* definition (Rodrigues formula via
  `Polynomial.derivative^[k]`), not a stub. Mathlib has no Legendre polynomials
  (verified against v4.31.0-rc1: only the number-theoretic `LegendreSymbol`), so
  this is original infrastructure. For `|x| ≤ 1` and even `m` it agrees with the
  polynomial form `(1-x²)^{m/2}`; for `|x| > 1` the `Real.sqrt` factor vanishes,
  which is harmless since `x = cos θ`.
* Smoothness is `ContDiffOn ℝ ∞` on `Ioo (-1) 1` (`associatedLegendre_smooth`);
  the earlier global-smoothness claim was false and remains corrected.
* The orthogonality and normalisation proofs go through the Sturm–Liouville
  momentum `assocLegendreSL x = (1-x²)·(P_ℓ^m)′(x)` — which, unlike `P′` itself,
  extends continuously to `[-1,1]` and vanishes at `±1` — together with the
  polynomial three-term identity `rodriguesDeriv_step` and the ladder relation
  `assocLegendreNat_ladder`.

## Main definitions

* `rodriguesDeriv ℓ k` — the polynomial `d^k/dx^k (x²-1)^ℓ`.
* `AssociatedLegendre ℓ m` — `P_ℓ^m(x)` via the Rodrigues formula.
* `assocLegendreSL ℓ m` — the Sturm–Liouville momentum `(1-x²)·(P_ℓ^m)′(x)`.

## Main statements

* `associatedLegendre_smooth`, `associatedLegendre_continuous` — regularity.
* `hasDerivAt_assocLegendreSL` — the associated Legendre ODE in SL form.
* `associatedLegendre_orthogonality` — `∫ P_ℓ^m P_{ℓ'}^m = 0` for `ℓ ≠ ℓ'`.
* `assocLegendreNat_normalization` — the `L²[-1,1]` norm of `P_ℓ^m`.
* `rodriguesDeriv_natDegree_le`, `rodriguesDeriv_coeff_ne_zero`,
  `span_of_natDegree` — triangularity of the Rodrigues family, consumed by the
  completeness proof (`Spectra.SphericalHarmonics.Completeness`).

## References

* [Stein, Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*][steinweiss1971]
* [Müller, *Spherical Harmonics*][muller1966]
-/

open MeasureTheory Complex Filter InnerProductSpace
open scoped Topology NNReal ENNReal ContDiff

namespace Spectra.SphericalHarmonics

/-- The polynomial `d^k/dx^k (x² - 1)^ℓ` appearing in the Rodrigues formula. -/
noncomputable def rodriguesDeriv (ℓ k : ℕ) : Polynomial ℝ :=
  Polynomial.derivative^[k] ((Polynomial.X ^ 2 - 1) ^ ℓ)

/-- P_ℓ^m for a non-negative upper index `m : ℕ`:
      P_ℓ^m(x) = ((-1)^m / (2^ℓ ℓ!)) · √(1-x²)^m · d^{ℓ+m}/dx^{ℓ+m} (x²-1)^ℓ.

    For `|x| ≤ 1` (the physical domain `x = cos θ`) and even `m` this agrees
    with the textbook `(1-x²)^{m/2}`; for `|x| > 1` the sqrt factor clamps
    to 0, which never matters on the sphere. -/
noncomputable def assocLegendreNat (ℓ m : ℕ) : ℝ → ℝ := fun x =>
  (-1 : ℝ) ^ m / (2 ^ ℓ * ℓ.factorial : ℝ) * Real.sqrt (1 - x ^ 2) ^ m *
    (rodriguesDeriv ℓ (ℓ + m)).eval x

/-- The associated Legendre function P_ℓ^m(x) for ℓ ≥ 0 and arbitrary `m : ℤ`,
    via the Rodrigues formula for m ≥ 0 and the reflection
      P_ℓ^{-m} = (-1)^m (ℓ-m)!/(ℓ+m)! P_ℓ^m
    for m < 0 (Condon–Shortley convention). Total in `m`; for `|m| > ℓ` the
    `(ℓ+|m|)`-fold derivative of a degree-`2ℓ` polynomial vanishes, so
    `P_ℓ^m = 0`, matching the standard convention. -/
noncomputable def AssociatedLegendre (ℓ : ℕ) (m : ℤ) : ℝ → ℝ :=
  if 0 ≤ m then assocLegendreNat ℓ m.toNat
  else fun x =>
    ((-1 : ℝ) ^ m.natAbs * (ℓ - m.natAbs).factorial / (ℓ + m.natAbs).factorial) *
      assocLegendreNat ℓ m.natAbs x

/-! ### Explicit low-degree values (proved) -/

lemma rodriguesDeriv_zero_zero : rodriguesDeriv 0 0 = 1 := by
  simp [rodriguesDeriv]

lemma rodriguesDeriv_one_one :
    rodriguesDeriv 1 1 = Polynomial.C 2 * Polynomial.X := by
  simp [rodriguesDeriv]; ring_nf
  exact Polynomial.coeff_inj.mp rfl

lemma rodriguesDeriv_one_two : rodriguesDeriv 1 2 = Polynomial.C 2 := by
  have h : rodriguesDeriv 1 2 = Polynomial.derivative (rodriguesDeriv 1 1) := by
    simp [rodriguesDeriv, Function.iterate_succ_apply']
  rw [h, rodriguesDeriv_one_one]
  simp

lemma associatedLegendre_0_0 : AssociatedLegendre 0 0 = fun _ => 1 := by
  funext x
  unfold AssociatedLegendre
  rw [if_pos le_rfl]
  simp [assocLegendreNat, rodriguesDeriv_zero_zero]

lemma associatedLegendre_1_0 : AssociatedLegendre 1 0 = fun x => x := by
  funext x
  unfold AssociatedLegendre
  rw [if_pos le_rfl]
  simp only [Int.toNat_zero, assocLegendreNat, Nat.add_zero, rodriguesDeriv_one_one]
  simp [Nat.factorial]

lemma associatedLegendre_1_1 :
    AssociatedLegendre 1 1 = fun x => -Real.sqrt (1 - x ^ 2) := by
  funext x
  unfold AssociatedLegendre
  rw [if_pos (by norm_num : (0:ℤ) ≤ 1)]
  simp only [Int.toNat_one, assocLegendreNat]
  rw [rodriguesDeriv_one_two]
  simp [Nat.factorial]
  ring

/-! ### Regularity (proved) -/

/-- Evaluation of a real polynomial is C^∞. -/
lemma polynomial_contDiff (p : Polynomial ℝ) :
    ContDiff ℝ ∞ fun x : ℝ => p.eval x := by
  have h : ContDiff ℝ ∞ fun x : ℝ => (Polynomial.aeval x) p :=
    Polynomial.contDiff_aeval p ∞
  simpa [Polynomial.coe_aeval_eq_eval] using h

lemma assocLegendreNat_continuous (ℓ m : ℕ) :
    Continuous (assocLegendreNat ℓ m) := by
  have hq : Continuous fun x : ℝ => (rodriguesDeriv ℓ (ℓ + m)).eval x := by
    fun_prop
  have hs : Continuous fun x : ℝ => Real.sqrt (1 - x ^ 2) ^ m :=
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).pow m
  exact (continuous_const.mul hs).mul hq

/-- P_ℓ^m is continuous on all of ℝ (with the clamped-sqrt convention). -/
lemma associatedLegendre_continuous (ℓ : ℕ) (m : ℤ) :
    Continuous (AssociatedLegendre ℓ m) := by
  unfold AssociatedLegendre
  split_ifs
  · exact assocLegendreNat_continuous ℓ _
  · exact continuous_const.mul (assocLegendreNat_continuous ℓ _)

lemma assocLegendreNat_contDiffOn (ℓ m : ℕ) :
    ContDiffOn ℝ ∞ (assocLegendreNat ℓ m) (Set.Ioo (-1 : ℝ) 1) := by
  have hpoly : ContDiffOn ℝ ∞ (fun x : ℝ => (rodriguesDeriv ℓ (ℓ + m)).eval x)
      (Set.Ioo (-1 : ℝ) 1) := (polynomial_contDiff _).contDiffOn
  have hsqrt : ContDiffOn ℝ ∞ (fun x : ℝ => Real.sqrt (1 - x ^ 2) ^ m)
      (Set.Ioo (-1 : ℝ) 1) := by
    refine ContDiffOn.pow ?_ m
    refine ContDiffOn.sqrt ((contDiff_const.sub (contDiff_id.pow 2)).contDiffOn) ?_
    intro x hx
    have h1 : -1 < x := hx.1
    have h2 : x < 1 := hx.2
    nlinarith
  exact (contDiffOn_const.mul hsqrt).mul hpoly

/-- **P_ℓ^m is smooth on (-1, 1).** This replaces the earlier (false) claim of
    global smoothness on ℝ: for odd `m` the factor `√(1-x²)` is not
    differentiable at `x = ±1` (e.g. P₁¹). On the open interval — the image of
    `cos` on `(0, π)`, which is all the eigenvalue equation needs — full C^∞
    regularity holds, with no hypothesis on `m`. -/
lemma associatedLegendre_smooth (ℓ : ℕ) (m : ℤ) :
    ContDiffOn ℝ ∞ (AssociatedLegendre ℓ m) (Set.Ioo (-1 : ℝ) 1) := by
  unfold AssociatedLegendre
  split_ifs
  · exact assocLegendreNat_contDiffOn ℓ _
  · exact contDiffOn_const.mul (assocLegendreNat_contDiffOn ℓ _)

/-! ### The reflection factor

`AssociatedLegendre ℓ m` is always a scalar multiple of
`assocLegendreNat ℓ m.natAbs`; isolating the scalar lets every analytic
statement below be proved once, for the ℕ-indexed function. -/

/-- The scalar relating `AssociatedLegendre ℓ m` to `assocLegendreNat ℓ m.natAbs`:
    `1` for `m ≥ 0`, and the Condon–Shortley reflection factor for `m < 0`. -/
noncomputable def reflectionFactor (ℓ : ℕ) (m : ℤ) : ℝ :=
  if 0 ≤ m then 1
  else (-1 : ℝ) ^ m.natAbs * (ℓ - m.natAbs).factorial / (ℓ + m.natAbs).factorial

lemma associatedLegendre_eq_reflection (ℓ : ℕ) (m : ℤ) :
    AssociatedLegendre ℓ m =
      fun x => reflectionFactor ℓ m * assocLegendreNat ℓ m.natAbs x := by
  unfold AssociatedLegendre reflectionFactor
  split_ifs with h
  · have hnm : m.toNat = m.natAbs := by omega
    rw [hnm]
    funext x
    rw [one_mul]
  · rfl

/-! ### The Rodrigues three-term identity

The engine behind the associated Legendre ODE. Writing `T_ℓ,k` for
`rodriguesDeriv ℓ k = d^k (x²-1)^ℓ`, repeated differentiation of
`(x²-1)·T' = 2ℓx·T` (the defining ODE of `(x²-1)^ℓ`) gives, by induction on
`k`, the *subtraction-free* polynomial identity

  (x²-1)·T_{k+2} + (2k+2)·x·T_{k+1} + k(k+1)·T_k
      = 2ℓ·x·T_{k+1} + 2ℓ(k+1)·T_k.

Evaluated at `k = ℓ+m`, this is exactly the associated Legendre ODE in
Rodrigues form. -/

lemma rodriguesDeriv_succ (ℓ k : ℕ) :
    rodriguesDeriv ℓ (k + 1) = Polynomial.derivative (rodriguesDeriv ℓ k) := by
  simp [rodriguesDeriv, Function.iterate_succ_apply']

lemma rodriguesDeriv_zero (ℓ : ℕ) :
    rodriguesDeriv ℓ 0 = (Polynomial.X ^ 2 - 1) ^ ℓ := by
  simp [rodriguesDeriv]

/-- The defining first-order ODE of `(x²-1)^ℓ`:
    `(x²-1) · d(x²-1)^ℓ = 2ℓ·x·(x²-1)^ℓ`. -/
lemma rodriguesDeriv_base (ℓ : ℕ) :
    (Polynomial.X ^ 2 - 1) * rodriguesDeriv ℓ 1 =
      2 * (ℓ : Polynomial ℝ) * (Polynomial.X * rodriguesDeriv ℓ 0) := by
  rcases ℓ with _ | n
  · simp [rodriguesDeriv]
  · have h0 : rodriguesDeriv (n + 1) 0 = (Polynomial.X ^ 2 - 1) ^ (n + 1) :=
      rodriguesDeriv_zero (n + 1)
    have h1 : rodriguesDeriv (n + 1) 1 =
        Polynomial.derivative ((Polynomial.X ^ 2 - 1) ^ (n + 1)) := by
      simp [rodriguesDeriv]
    rw [h0, h1, Polynomial.derivative_pow]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X_pow, Nat.add_sub_cancel, sub_zero,
      Polynomial.C_eq_natCast]
    push_cast
    ring

/-- The three-term Rodrigues identity (see section docstring). Subtraction-free
    so that it lives in `ℕ`-indexed form; the proof is `d/dx` of the previous
    line at every step. -/
lemma rodriguesDeriv_step (ℓ k : ℕ) :
    (Polynomial.X ^ 2 - 1) * rodriguesDeriv ℓ (k + 2)
        + (2 * (k : Polynomial ℝ) + 2) * Polynomial.X * rodriguesDeriv ℓ (k + 1)
        + (k : Polynomial ℝ) * ((k : Polynomial ℝ) + 1) * rodriguesDeriv ℓ k =
      2 * (ℓ : Polynomial ℝ) * Polynomial.X * rodriguesDeriv ℓ (k + 1)
        + 2 * (ℓ : Polynomial ℝ) * ((k : Polynomial ℝ) + 1) * rodriguesDeriv ℓ k := by
  induction k with
  | zero =>
      have h := congrArg Polynomial.derivative (rodriguesDeriv_base ℓ)
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
        Polynomial.derivative_one, Polynomial.derivative_X_pow,
        Polynomial.derivative_natCast, Polynomial.derivative_ofNat,
        Polynomial.derivative_X, Polynomial.C_eq_natCast,
        ← rodriguesDeriv_succ] at h
      -- normalise the (purely numeral) iterate indices so that `ring` sees
      -- `rodriguesDeriv ℓ 2`, `… 1`, `… 0` as the same atoms in `h` and in
      -- the goal
      norm_num at h ⊢
      linear_combination h
  | succ n ih =>
      have h := congrArg Polynomial.derivative ih
      simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
        Polynomial.derivative_sub, Polynomial.derivative_one,
        Polynomial.derivative_X_pow, Polynomial.derivative_natCast,
        Polynomial.derivative_ofNat, Polynomial.derivative_X,
        Polynomial.C_eq_natCast, ← rodriguesDeriv_succ] at h
      -- align `n + 2 + 1` (from differentiating `ih`) with `n + 1 + 2`
      -- (the index appearing in the goal)
      rw [show n + 2 + 1 = n + 1 + 2 by omega] at h
      push_cast at h ⊢
      linear_combination h

/-! ### Derivative infrastructure on (-1, 1) -/

/-- Derivative of the clamped factor `√(1-x²)^m` on the open interval. -/
lemma hasDerivAt_sqrt_one_sub_sq_pow (m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2) ^ m)
      (-(m : ℝ) * x * Real.sqrt (1 - x ^ 2) ^ m / (1 - x ^ 2)) x := by
  have hu : (0:ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs : (0:ℝ) < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hu
  have hin : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have hsq : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x := hin.sqrt hu.ne'
  have h := hsq.fun_pow m
  convert h using 1
  rcases m with _ | n
  · simp
  · set s := Real.sqrt (1 - x ^ 2) with _hs_def
    have hs2 : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hu.le
    rw [← hs2]
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev,
      add_tsub_cancel_right]
    field_simp
    ring

/-- Derivative of `(rodriguesDeriv ℓ k).eval`, with the index bumped. -/
lemma hasDerivAt_rodriguesDeriv_eval (ℓ k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (rodriguesDeriv ℓ k).eval y)
      ((rodriguesDeriv ℓ (k + 1)).eval x) x := by
  have h := Polynomial.hasDerivAt (rodriguesDeriv ℓ k) x
  rwa [← rodriguesDeriv_succ] at h

/-- **The Sturm–Liouville momentum** `(1-x²)·(P_ℓ^m)′(x)`, written so that it is
    defined and continuous on all of ℝ (unlike `(P_ℓ^m)′` itself, which blows
    up at ±1 for odd m). On `(-1,1)` it equals `(1-x²)` times the derivative of
    `assocLegendreNat ℓ m` (see `hasDerivAt_assocLegendreNat`), and it vanishes
    at `x = ±1` — which is exactly why the Sturm–Liouville boundary terms
    vanish in `assocLegendreNat_orthogonality`. -/
noncomputable def assocLegendreSL (ℓ m : ℕ) : ℝ → ℝ := fun x =>
  (-1 : ℝ) ^ m / (2 ^ ℓ * ℓ.factorial : ℝ) *
    ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2) ^ m * (rodriguesDeriv ℓ (ℓ + m + 1)).eval x
      - (m : ℝ) * x * Real.sqrt (1 - x ^ 2) ^ m * (rodriguesDeriv ℓ (ℓ + m)).eval x)

lemma assocLegendreSL_continuous (ℓ m : ℕ) : Continuous (assocLegendreSL ℓ m) := by
  have hs : Continuous fun x : ℝ => Real.sqrt (1 - x ^ 2) ^ m :=
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).pow m
  have hq1 : Continuous fun x : ℝ => (rodriguesDeriv ℓ (ℓ + m + 1)).eval x := by
    fun_prop
  have hq0 : Continuous fun x : ℝ => (rodriguesDeriv ℓ (ℓ + m)).eval x := by
    fun_prop
  exact continuous_const.mul
    ((((continuous_const.sub (continuous_pow 2)).mul hs).mul hq1).sub
      (((continuous_const.mul continuous_id).mul hs).mul hq0))

lemma assocLegendreSL_one (ℓ m : ℕ) : assocLegendreSL ℓ m 1 = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [assocLegendreSL]
  · simp [assocLegendreSL, zero_pow hm.ne']

lemma assocLegendreSL_neg_one (ℓ m : ℕ) : assocLegendreSL ℓ m (-1) = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [assocLegendreSL]
  · simp [assocLegendreSL, zero_pow hm.ne']

/-- On `(-1,1)`, `P_ℓ^m` is differentiable with
    `(P_ℓ^m)′(x) = assocLegendreSL ℓ m x / (1-x²)`. -/
lemma hasDerivAt_assocLegendreNat (ℓ m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (assocLegendreNat ℓ m) (assocLegendreSL ℓ m x / (1 - x ^ 2)) x := by
  have hu : (0:ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  set c : ℝ := (-1 : ℝ) ^ m / (2 ^ ℓ * ℓ.factorial : ℝ) with hc
  have hsm := hasDerivAt_sqrt_one_sub_sq_pow m hx
  have hq := hasDerivAt_rodriguesDeriv_eval ℓ (ℓ + m) x
  have h := (hsm.const_mul c).fun_mul hq
  have hfun : assocLegendreNat ℓ m = fun y =>
      c * Real.sqrt (1 - y ^ 2) ^ m * (rodriguesDeriv ℓ (ℓ + m)).eval y := by
    funext y
    simp only [assocLegendreNat, ← hc]
  have hSL : assocLegendreSL ℓ m x =
      c * ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2) ^ m * (rodriguesDeriv ℓ (ℓ + m + 1)).eval x
        - (m : ℝ) * x * Real.sqrt (1 - x ^ 2) ^ m * (rodriguesDeriv ℓ (ℓ + m)).eval x) := by
    simp only [assocLegendreSL, ← hc]
  rw [hfun, hSL]
  convert h using 1
  field_simp
  ring

/-- **The associated Legendre ODE in Sturm–Liouville form**: on `(-1,1)`,

      d/dx [ (1-x²)·(P_ℓ^m)′ ] = -( ℓ(ℓ+1) - m²/(1-x²) ) · P_ℓ^m.

    Equivalently `(1-x²)P'' - 2xP' + [ℓ(ℓ+1) - m²/(1-x²)]P = 0`. The proof is
    the evaluation of `rodriguesDeriv_step` at `k = ℓ+m`. -/
lemma hasDerivAt_assocLegendreSL (ℓ m : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (assocLegendreSL ℓ m)
      (-((ℓ : ℝ) * ((ℓ : ℝ) + 1) - (m : ℝ) ^ 2 / (1 - x ^ 2))
        * assocLegendreNat ℓ m x) x := by
  have hu : (0:ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  set c : ℝ := (-1 : ℝ) ^ m / (2 ^ ℓ * ℓ.factorial : ℝ) with hc
  -- the pieces
  have hone : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have hsm := hasDerivAt_sqrt_one_sub_sq_pow m hx
  have hq0 := hasDerivAt_rodriguesDeriv_eval ℓ (ℓ + m) x
  have hq1 := hasDerivAt_rodriguesDeriv_eval ℓ (ℓ + m + 1) x
  rw [show ℓ + m + 1 + 1 = ℓ + m + 2 by omega] at hq1
  have hid : HasDerivAt (fun y : ℝ => (m : ℝ) * y) (m : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (m : ℝ)
  have hA := (hone.fun_mul hsm).fun_mul hq1
  have hB := (hid.fun_mul hsm).fun_mul hq0
  have h := (hA.fun_sub hB).const_mul c
  -- align the function
  have hfun : assocLegendreSL ℓ m = fun y =>
      c * ((1 - y ^ 2) * Real.sqrt (1 - y ^ 2) ^ m * (rodriguesDeriv ℓ (ℓ + m + 1)).eval y
        - (m : ℝ) * y * Real.sqrt (1 - y ^ 2) ^ m * (rodriguesDeriv ℓ (ℓ + m)).eval y) := by
    funext y
    simp only [assocLegendreSL, ← hc]
  have hP : assocLegendreNat ℓ m x =
      c * Real.sqrt (1 - x ^ 2) ^ m * (rodriguesDeriv ℓ (ℓ + m)).eval x := by
    simp only [assocLegendreNat, ← hc]
  rw [hfun, hP]
  -- the ODE content: solve `rodriguesDeriv_step` (evaluated at x) for the
  -- top derivative
  have hstep := congrArg (Polynomial.eval x) (rodriguesDeriv_step ℓ (ℓ + m))
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_X,
    Polynomial.eval_natCast, Polynomial.eval_ofNat] at hstep
  push_cast at hstep
  have hq2solved : (rodriguesDeriv ℓ (ℓ + m + 2)).eval x =
      (2 * ((m : ℝ) + 1) * x * (rodriguesDeriv ℓ (ℓ + m + 1)).eval x
        - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - (m : ℝ) * ((m : ℝ) + 1))
            * (rodriguesDeriv ℓ (ℓ + m)).eval x) / (1 - x ^ 2) := by
    rw [eq_div_iff hu.ne']
    linear_combination -hstep
  convert h using 1
  rw [hq2solved]
  field_simp
  ring

/-! ### Recurrence and orthogonality -/

/-- Orthogonality at the ℕ-indexed level: the Sturm–Liouville/Wronskian
    argument. With `W = P_ℓ·(SL of P_{ℓ'}) - P_{ℓ'}·(SL of P_ℓ)` one computes
    `W′ = (λ_ℓ - λ_{ℓ'})·P_ℓ·P_{ℓ'}` on `(-1,1)` — the `m²/(1-x²)` singular
    terms cancel — and `W(±1) = 0` since the SL momentum vanishes at the
    endpoints. FTC and the eigenvalue gap finish it. -/
lemma assocLegendreNat_orthogonality (ℓ ℓ' m : ℕ) (hne : ℓ ≠ ℓ') :
    ∫ x in (-1 : ℝ)..1, assocLegendreNat ℓ m x * assocLegendreNat ℓ' m x = 0 := by
  have hcont : ContinuousOn
      (fun y => assocLegendreNat ℓ m y * assocLegendreSL ℓ' m y
        - assocLegendreNat ℓ' m y * assocLegendreSL ℓ m y)
      (Set.Icc (-1 : ℝ) 1) :=
    (((assocLegendreNat_continuous ℓ m).mul (assocLegendreSL_continuous ℓ' m)).sub
      ((assocLegendreNat_continuous ℓ' m).mul (assocLegendreSL_continuous ℓ m))).continuousOn
  have hderiv : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt
        (fun y => assocLegendreNat ℓ m y * assocLegendreSL ℓ' m y
          - assocLegendreNat ℓ' m y * assocLegendreSL ℓ m y)
        (((ℓ : ℝ) * ((ℓ : ℝ) + 1) - (ℓ' : ℝ) * ((ℓ' : ℝ) + 1))
          * (assocLegendreNat ℓ m y * assocLegendreNat ℓ' m y)) y := by
    intro y hy
    have hu : (0:ℝ) < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    have h := ((hasDerivAt_assocLegendreNat ℓ m hy).fun_mul
        (hasDerivAt_assocLegendreSL ℓ' m hy)).fun_sub
      ((hasDerivAt_assocLegendreNat ℓ' m hy).fun_mul
        (hasDerivAt_assocLegendreSL ℓ m hy))
    convert h using 1
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun y => ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - (ℓ' : ℝ) * ((ℓ' : ℝ) + 1))
        * (assocLegendreNat ℓ m y * assocLegendreNat ℓ' m y)) volume (-1) 1 :=
    (continuous_const.mul
      ((assocLegendreNat_continuous ℓ m).mul
        (assocLegendreNat_continuous ℓ' m))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1:ℝ) ≤ 1) hcont hderiv hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [assocLegendreSL_one, assocLegendreSL_neg_one, mul_zero,
    sub_self] at hFTC
  have hgap : ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - (ℓ' : ℝ) * ((ℓ' : ℝ) + 1)) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    rcases hne.lt_or_gt with h | h
    · have hc : (ℓ : ℝ) < (ℓ' : ℝ) := by exact_mod_cast h
      have key : (0:ℝ) < ((ℓ' : ℝ) - ℓ) * ((ℓ' : ℝ) + ℓ + 1) :=
        mul_pos (by linarith) (by positivity)
      exact ne_of_lt (by nlinarith [key])
    · have hc : (ℓ' : ℝ) < (ℓ : ℝ) := by exact_mod_cast h
      have key : (0:ℝ) < ((ℓ : ℝ) - ℓ') * ((ℓ : ℝ) + ℓ' + 1) :=
        mul_pos (by linarith) (by positivity)
      exact ne_of_gt (by nlinarith [key])
  exact (mul_eq_zero.mp hFTC).resolve_left hgap

/-- Orthogonality of associated Legendre functions (same m, different ℓ).
    ∫_{-1}^{1} P_ℓ^m(x) P_{ℓ'}^m(x) dx = 0 for ℓ ≠ ℓ'.

    Proved by reducing to `assocLegendreNat_orthogonality` through the
    reflection factor. -/
lemma associatedLegendre_orthogonality (ℓ ℓ' : ℕ) (m : ℤ)
    (_hm : |m| ≤ ℓ) (_hm' : |m| ≤ ℓ') (hne : ℓ ≠ ℓ') :
    ∫ x in Set.Icc (-1 : ℝ) 1,
      AssociatedLegendre ℓ m x * AssociatedLegendre ℓ' m x = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  simp only [associatedLegendre_eq_reflection]
  have hsplit : ∀ x : ℝ,
      reflectionFactor ℓ m * assocLegendreNat ℓ m.natAbs x *
        (reflectionFactor ℓ' m * assocLegendreNat ℓ' m.natAbs x) =
      reflectionFactor ℓ m * reflectionFactor ℓ' m *
        (assocLegendreNat ℓ m.natAbs x * assocLegendreNat ℓ' m.natAbs x) :=
    fun x => by ring
  calc (∫ x in (-1 : ℝ)..1,
          reflectionFactor ℓ m * assocLegendreNat ℓ m.natAbs x *
            (reflectionFactor ℓ' m * assocLegendreNat ℓ' m.natAbs x))
      = ∫ x in (-1 : ℝ)..1,
          reflectionFactor ℓ m * reflectionFactor ℓ' m *
            (assocLegendreNat ℓ m.natAbs x * assocLegendreNat ℓ' m.natAbs x) :=
        intervalIntegral.integral_congr fun x _ => hsplit x
    _ = reflectionFactor ℓ m * reflectionFactor ℓ' m *
          ∫ x in (-1 : ℝ)..1,
            assocLegendreNat ℓ m.natAbs x * assocLegendreNat ℓ' m.natAbs x :=
        intervalIntegral.integral_const_mul _ _
    _ = 0 := by rw [assocLegendreNat_orthogonality ℓ ℓ' m.natAbs hne, mul_zero]


lemma assocLegendreNat_one (ℓ m : ℕ) (hm : m ≠ 0) : assocLegendreNat ℓ m 1 = 0 := by
  simp [assocLegendreNat, zero_pow hm]

lemma assocLegendreNat_neg_one (ℓ m : ℕ) (hm : m ≠ 0) : assocLegendreNat ℓ m (-1) = 0 := by
  simp [assocLegendreNat, zero_pow hm]

/-- `(x²-1)^{ℓ-k}` divides the `k`-th Rodrigues derivative; in particular the
    latter vanishes at `±1` for `k < ℓ`, which kills all boundary terms in the
    integration by parts below. -/
lemma pow_dvd_rodriguesDeriv (ℓ k : ℕ) :
    ((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ (ℓ - k) ∣ rodriguesDeriv ℓ k := by
  induction k with
  | zero =>
      rw [rodriguesDeriv_zero, Nat.sub_zero]
  | succ k ih =>
      rcases Nat.lt_or_ge k ℓ with h | h
      · obtain ⟨q, hq⟩ := ih
        refine ⟨Polynomial.C (((ℓ - k : ℕ)) : ℝ)
            * Polynomial.derivative ((Polynomial.X : Polynomial ℝ) ^ 2 - 1) * q
          + ((Polynomial.X : Polynomial ℝ) ^ 2 - 1) * Polynomial.derivative q, ?_⟩
        rw [rodriguesDeriv_succ, hq, Polynomial.derivative_mul, Polynomial.derivative_pow,
          show ℓ - k = (ℓ - (k+1)) + 1 by omega, Nat.add_sub_cancel]
        ring
      · rw [show ℓ - (k+1) = 0 by omega, pow_zero]
        exact one_dvd _

lemma rodriguesDeriv_eval_one (ℓ k : ℕ) (h : k < ℓ) :
    (rodriguesDeriv ℓ k).eval 1 = 0 := by
  obtain ⟨q, hq⟩ := pow_dvd_rodriguesDeriv ℓ k
  have hne : ℓ - k ≠ 0 := Nat.sub_ne_zero_of_lt h
  rw [hq]
  simp [zero_pow hne]

/-- If `p` has degree at most `n`, its `n`-fold derivative is the constant
    `n! · (coefficient of xⁿ)`. -/
lemma iterate_derivative_eq_C (n : ℕ) :
    ∀ p : Polynomial ℝ, p.natDegree ≤ n →
      Polynomial.derivative^[n] p = Polynomial.C ((n.factorial : ℝ) * p.coeff n) := by
  induction n with
  | zero =>
      intro p hp
      simpa using Polynomial.eq_C_of_natDegree_le_zero hp
  | succ n ih =>
      intro p hp
      rw [Function.iterate_succ_apply]
      have hd : (Polynomial.derivative p).natDegree ≤ n := by
        have h := Polynomial.natDegree_derivative_le p
        omega
      rw [ih _ hd, Polynomial.coeff_derivative]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      ring

/-- The top Rodrigues derivative is the constant `(2ℓ)!`. -/
lemma rodriguesDeriv_two_mul_self (ℓ : ℕ) :
    rodriguesDeriv ℓ (2 * ℓ) = Polynomial.C (((2 * ℓ).factorial : ℝ)) := by
  have hmon : ((Polynomial.X : Polynomial ℝ) ^ 2 - 1).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : ℝ) (n := 2) (by norm_num)
  have hP : (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ ℓ).Monic := hmon.pow ℓ
  have hdeg : (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ ℓ).natDegree = 2 * ℓ := by
    have h2 : ((Polynomial.X : Polynomial ℝ) ^ 2 - 1).natDegree = 2 := by
      simpa using Polynomial.natDegree_X_pow_sub_C (n := 2) (r := (1 : ℝ))
    rw [Polynomial.natDegree_pow, h2, Nat.mul_comm]
  have hcoeff : (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ ℓ).coeff (2 * ℓ) = 1 := by
    have h := hP.coeff_natDegree
    rwa [hdeg] at h
  have h := iterate_derivative_eq_C (2 * ℓ) (((Polynomial.X : Polynomial ℝ) ^ 2 - 1) ^ ℓ)
    (le_of_eq hdeg)
  rw [hcoeff, mul_one] at h
  simpa [rodriguesDeriv] using h

/-- Below the top index, the Rodrigues derivatives vanish at `-1`. -/
lemma rodriguesDeriv_eval_neg_one (ℓ k : ℕ) (h : k < ℓ) :
    (rodriguesDeriv ℓ k).eval (-1) = 0 := by
  obtain ⟨q, hq⟩ := pow_dvd_rodriguesDeriv ℓ k
  rw [hq]
  simp [zero_pow (Nat.sub_ne_zero_of_lt h)]

/-- One integration by parts in the Rodrigues chain: a derivative moves from
    the left factor to the right one (the boundary terms vanish since the left
    index stays `< ℓ`). -/
lemma rodriguesDeriv_integral_step (ℓ a b : ℕ) (ha : a < ℓ) :
    ∫ x in (-1:ℝ)..1, (rodriguesDeriv ℓ (a+1)).eval x * (rodriguesDeriv ℓ b).eval x
      = - ∫ x in (-1:ℝ)..1, (rodriguesDeriv ℓ a).eval x * (rodriguesDeriv ℓ (b+1)).eval x := by
  have hc1 : Continuous fun x : ℝ =>
      (rodriguesDeriv ℓ (a+1)).eval x * (rodriguesDeriv ℓ b).eval x := by fun_prop
  have hc2 : Continuous fun x : ℝ =>
      (rodriguesDeriv ℓ a).eval x * (rodriguesDeriv ℓ (b+1)).eval x := by fun_prop
  have hderiv : ∀ x ∈ Set.uIcc (-1:ℝ) 1,
      HasDerivAt (fun y => (rodriguesDeriv ℓ a).eval y * (rodriguesDeriv ℓ b).eval y)
        ((rodriguesDeriv ℓ (a+1)).eval x * (rodriguesDeriv ℓ b).eval x
          + (rodriguesDeriv ℓ a).eval x * (rodriguesDeriv ℓ (b+1)).eval x) x := by
    intro x _
    exact (hasDerivAt_rodriguesDeriv_eval ℓ a x).fun_mul (hasDerivAt_rodriguesDeriv_eval ℓ b x)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hc1.add hc2).intervalIntegrable _ _)
  simp only [rodriguesDeriv_eval_one ℓ a ha, rodriguesDeriv_eval_neg_one ℓ a ha,
    zero_mul, sub_zero] at hFTC
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _)] at hFTC
  linarith

/-- The `j`-fold integration by parts: `∫ T_ℓ² = (-1)^j ∫ T_{ℓ-j} · T_{ℓ+j}`. -/
lemma rodriguesDeriv_integral_shift (ℓ : ℕ) :
    ∀ j ≤ ℓ, ∫ x in (-1:ℝ)..1, (rodriguesDeriv ℓ ℓ).eval x * (rodriguesDeriv ℓ ℓ).eval x
      = (-1:ℝ)^j * ∫ x in (-1:ℝ)..1,
          (rodriguesDeriv ℓ (ℓ-j)).eval x * (rodriguesDeriv ℓ (ℓ+j)).eval x := by
  intro j
  induction j with
  | zero =>
      intro _
      simp
  | succ j ih =>
      intro hj
      rw [ih (Nat.le_of_succ_le hj),
        show ℓ - j = ℓ - (j+1) + 1 by omega,
        rodriguesDeriv_integral_step ℓ (ℓ-(j+1)) (ℓ+j) (by omega),
        show ℓ + (j+1) = ℓ + j + 1 by omega]
      ring

/-- `∫_{-1}^1 (1-x²)ⁿ dx = 2^{2n+1} (n!)² / (2n+1)!` (Wallis). -/
lemma integral_one_sub_sq_pow (n : ℕ) :
    ∫ x in (-1:ℝ)..1, (1 - x^2)^n
      = 2^(2*n+1) * ((n.factorial : ℝ))^2 / ((2*n+1).factorial : ℝ) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hderiv : ∀ x ∈ Set.uIcc (-1:ℝ) 1,
          HasDerivAt (fun y : ℝ => y * (1 - y^2)^(n+1))
            ((2*(n:ℝ)+3) * (1 - x^2)^(n+1) - (2*(n:ℝ)+2) * (1 - x^2)^n) x := by
        intro x _
        have h1 : HasDerivAt (fun y : ℝ => 1 - y^2) (-(2*x)) x := by
          simpa using (hasDerivAt_pow 2 x).const_sub 1
        have h2 := h1.fun_pow (n+1)
        rw [Nat.add_sub_cancel] at h2
        have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
        have h := hid.fun_mul h2
        convert h using 1
        push_cast
        ring
      have hcont1 : Continuous fun x : ℝ => (1 - x^2)^(n+1) := by fun_prop
      have hcont0 : Continuous fun x : ℝ => (1 - x^2)^n := by fun_prop
      have h1 : IntervalIntegrable (fun x : ℝ => (2*(n:ℝ)+3) * (1 - x^2)^(n+1)) volume (-1) 1 :=
        (continuous_const.mul hcont1).intervalIntegrable _ _
      have h2 : IntervalIntegrable (fun x : ℝ => (2*(n:ℝ)+2) * (1 - x^2)^n) volume (-1) 1 :=
        (continuous_const.mul hcont0).intervalIntegrable _ _
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (h1.sub h2)
      norm_num at hFTC
      -- hFTC : ∫ ((2n+3)(1-x²)^{n+1} - (2n+2)(1-x²)ⁿ) = 0
      rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, ih] at hFTC
      have h2n3 : (2*(n:ℝ)+3) ≠ 0 := by positivity
      have _h2n2 : (2*(n:ℝ)+2) ≠ 0 := by positivity
      have hne : ((2*n+1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hI : (∫ x in (-1:ℝ)..1, (1 - x^2)^(n+1))
          = (2*(n:ℝ)+2) * (2^(2*n+1) * ((n.factorial : ℝ))^2 / ((2*n+1).factorial : ℝ))
              / (2*(n:ℝ)+3) := by
        rw [eq_div_iff h2n3]
        linarith
      rw [hI]
      have hfa : ((2*(n+1)+1).factorial : ℝ)
          = (2*(n:ℝ)+3) * ((2*(n:ℝ)+2) * ((2*n+1).factorial : ℝ)) := by
        rw [show 2*(n+1)+1 = (2*n+2)+1 by omega, Nat.factorial_succ,
          show 2*n+2 = (2*n+1)+1 by omega, Nat.factorial_succ]
        push_cast
        ring
      have hfb : (((n+1).factorial : ℝ)) = ((n:ℝ)+1) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfa, hfb]
      field_simp
      ring

/-- The squared raising relation: on `1 - x² ≥ 0`,
      `(1-x²) · (P_ℓ^{m+1})² = (S + m·x·P_ℓ^m)²`,  `S = assocLegendreSL ℓ m`.
    (Pointwise; both sides are squares so the Condon–Shortley signs drop out.) -/
lemma assocLegendreNat_sq_succ (ℓ m : ℕ) {x : ℝ} (hx : (0 : ℝ) ≤ 1 - x ^ 2) :
    (1 - x^2) * (assocLegendreNat ℓ (m+1) x * assocLegendreNat ℓ (m+1) x)
      = (assocLegendreSL ℓ m x + (m:ℝ) * x * assocLegendreNat ℓ m x)^2 := by
  have hs : Real.sqrt (1 - x^2) ^ 2 = 1 - x^2 := Real.sq_sqrt hx
  simp only [assocLegendreNat, assocLegendreSL, ← add_assoc]
  set s := Real.sqrt (1 - x^2) with _hsdef
  rw [← hs]
  ring

/-- **The ladder identity**
      `∫ (P_ℓ^{m+1})² = (ℓ(ℓ+1) - m(m+1)) · ∫ (P_ℓ^m)²`.
    One FTC application: on `(-1,1)`,
      `d/dx [P·S + m·x·P²] = (P_ℓ^{m+1})² - (ℓ(ℓ+1)-m(m+1))·(P_ℓ^m)²`
    (the `1/(1-x²)` singular pieces cancel against the squared raising
    relation), and the boundary values vanish. Holds for all `m`, with both
    sides `0` once `m ≥ ℓ`. -/
lemma assocLegendreNat_ladder (ℓ m : ℕ) :
    ∫ x in (-1:ℝ)..1, assocLegendreNat ℓ (m+1) x * assocLegendreNat ℓ (m+1) x
      = ((ℓ:ℝ) * ((ℓ:ℝ)+1) - (m:ℝ) * ((m:ℝ)+1))
          * ∫ x in (-1:ℝ)..1, assocLegendreNat ℓ m x * assocLegendreNat ℓ m x := by
  have hcont : ContinuousOn
      (fun y => assocLegendreNat ℓ m y * assocLegendreSL ℓ m y
        + (m:ℝ) * y * (assocLegendreNat ℓ m y * assocLegendreNat ℓ m y))
      (Set.Icc (-1:ℝ) 1) :=
    (((assocLegendreNat_continuous ℓ m).mul (assocLegendreSL_continuous ℓ m)).add
      ((continuous_const.mul continuous_id).mul
        ((assocLegendreNat_continuous ℓ m).mul (assocLegendreNat_continuous ℓ m)))).continuousOn
  have hderiv : ∀ y ∈ Set.Ioo (-1:ℝ) 1,
      HasDerivAt
        (fun y => assocLegendreNat ℓ m y * assocLegendreSL ℓ m y
          + (m:ℝ) * y * (assocLegendreNat ℓ m y * assocLegendreNat ℓ m y))
        (assocLegendreNat ℓ (m+1) y * assocLegendreNat ℓ (m+1) y
          - ((ℓ:ℝ) * ((ℓ:ℝ)+1) - (m:ℝ) * ((m:ℝ)+1))
              * (assocLegendreNat ℓ m y * assocLegendreNat ℓ m y)) y := by
    intro y hy
    have hu : (0:ℝ) < 1 - y^2 := by nlinarith [hy.1, hy.2]
    have hkey := assocLegendreNat_sq_succ ℓ m hu.le
    have hP := hasDerivAt_assocLegendreNat ℓ m hy
    have hS := hasDerivAt_assocLegendreSL ℓ m hy
    have hid : HasDerivAt (fun t : ℝ => (m:ℝ) * t) (m:ℝ) y := by
      simpa using (hasDerivAt_id y).const_mul (m:ℝ)
    have h := (hP.fun_mul hS).fun_add (hid.fun_mul (hP.fun_mul hP))
    convert h using 1
    have h2 : (1 - y^2) ≠ 0 := hu.ne'
    apply mul_left_cancel₀ h2
    rw [mul_sub, hkey]
    field_simp
    ring
  have hint1 : IntervalIntegrable
      (fun y => assocLegendreNat ℓ (m+1) y * assocLegendreNat ℓ (m+1) y) volume (-1) 1 :=
    ((assocLegendreNat_continuous ℓ (m+1)).mul
      (assocLegendreNat_continuous ℓ (m+1))).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun y => ((ℓ:ℝ) * ((ℓ:ℝ)+1) - (m:ℝ) * ((m:ℝ)+1))
        * (assocLegendreNat ℓ m y * assocLegendreNat ℓ m y)) volume (-1) 1 :=
    (continuous_const.mul
      ((assocLegendreNat_continuous ℓ m).mul
        (assocLegendreNat_continuous ℓ m))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1:ℝ) ≤ 1) hcont hderiv (hint1.sub hint2)
  have hb1 : assocLegendreNat ℓ m 1 * assocLegendreSL ℓ m 1
      + (m:ℝ) * 1 * (assocLegendreNat ℓ m 1 * assocLegendreNat ℓ m 1) = 0 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [assocLegendreSL_one]
    · simp [assocLegendreSL_one, assocLegendreNat_one ℓ m hm.ne']
  have hbm1 : assocLegendreNat ℓ m (-1) * assocLegendreSL ℓ m (-1)
      + (m:ℝ) * (-1) * (assocLegendreNat ℓ m (-1) * assocLegendreNat ℓ m (-1)) = 0 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [assocLegendreSL_neg_one]
    · simp [assocLegendreSL_neg_one, assocLegendreNat_neg_one ℓ m hm.ne']
  rw [intervalIntegral.integral_sub hint1 hint2,
    intervalIntegral.integral_const_mul] at hFTC
  simp only [hb1, hbm1, sub_zero] at hFTC
  linarith

/-- The classical Legendre normalisation `∫_{-1}^1 P_ℓ² = 2/(2ℓ+1)` — the
    `m = 0` base case — via the `ℓ`-fold integration by parts
    `rodriguesDeriv_integral_shift` and the Wallis integral. -/
lemma assocLegendreNat_zero_normalization (ℓ : ℕ) :
    ∫ x in (-1:ℝ)..1, assocLegendreNat ℓ 0 x * assocLegendreNat ℓ 0 x
      = 2 / (2 * (ℓ:ℝ) + 1) := by
  have hrw : ∀ x : ℝ, assocLegendreNat ℓ 0 x * assocLegendreNat ℓ 0 x
      = (1 / ((2:ℝ) ^ ℓ * (ℓ.factorial : ℝ))) ^ 2
          * ((rodriguesDeriv ℓ ℓ).eval x * (rodriguesDeriv ℓ ℓ).eval x) := by
    intro x
    simp only [assocLegendreNat, pow_zero, Nat.add_zero]
    ring
  simp only [hrw]
  rw [intervalIntegral.integral_const_mul, rodriguesDeriv_integral_shift ℓ ℓ le_rfl,
    Nat.sub_self, ← two_mul, ← intervalIntegral.integral_const_mul]
  have hrw2 : ∀ x : ℝ,
      (-1:ℝ) ^ ℓ * ((rodriguesDeriv ℓ 0).eval x * (rodriguesDeriv ℓ (2 * ℓ)).eval x)
        = ((2 * ℓ).factorial : ℝ) * (1 - x ^ 2) ^ ℓ := by
    intro x
    rw [rodriguesDeriv_zero, rodriguesDeriv_two_mul_self]
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_C]
    have hbase : (-1:ℝ) ^ ℓ * (x ^ 2 - 1) ^ ℓ = (1 - x ^ 2) ^ ℓ := by
      rw [← mul_pow]
      congr 1
      ring
    calc (-1:ℝ) ^ ℓ * ((x ^ 2 - 1) ^ ℓ * ((2 * ℓ).factorial : ℝ))
        = ((2 * ℓ).factorial : ℝ) * ((-1:ℝ) ^ ℓ * (x ^ 2 - 1) ^ ℓ) := by ring
      _ = ((2 * ℓ).factorial : ℝ) * (1 - x ^ 2) ^ ℓ := by rw [hbase]
  simp only [hrw2]
  rw [intervalIntegral.integral_const_mul, integral_one_sub_sq_pow]
  have hfac : ((2 * ℓ + 1).factorial : ℝ) = (2 * (ℓ:ℝ) + 1) * ((2 * ℓ).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have h1 : ((ℓ.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr ℓ.factorial_ne_zero
  have h2 : (((2 * ℓ).factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((2:ℝ) ^ ℓ) ≠ 0 := by positivity
  have h4 : (2 * (ℓ:ℝ) + 1) ≠ 0 := by positivity
  rw [hfac]
  field_simp
  ring

/-- **Normalisation of the associated Legendre functions** (`m ≤ ℓ`):
      ∫_{-1}^1 (P_ℓ^m)² = (2/(2ℓ+1)) · (ℓ+m)!/(ℓ-m)!. -/
lemma assocLegendreNat_normalization (ℓ m : ℕ) (hm : m ≤ ℓ) :
    ∫ x in (-1 : ℝ)..1, assocLegendreNat ℓ m x * assocLegendreNat ℓ m x =
      2 / (2 * (ℓ : ℝ) + 1) * ((ℓ + m).factorial : ℝ) / ((ℓ - m).factorial : ℝ) := by
  induction m with
  | zero =>
      rw [assocLegendreNat_zero_normalization ℓ, Nat.add_zero, Nat.sub_zero,
        mul_div_assoc, div_self (Nat.cast_ne_zero.mpr ℓ.factorial_ne_zero), mul_one]
  | succ m ih =>
      have hm' : m ≤ ℓ := Nat.le_of_succ_le hm
      have hlt : (m:ℝ) < (ℓ:ℝ) := by exact_mod_cast Nat.lt_of_succ_le hm
      rw [assocLegendreNat_ladder ℓ m, ih hm']
      have hfac1 : ((ℓ + (m+1)).factorial : ℝ)
          = ((ℓ:ℝ) + (m:ℝ) + 1) * ((ℓ + m).factorial : ℝ) := by
        rw [show ℓ + (m+1) = (ℓ + m) + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      have hfac2 : ((ℓ - m).factorial : ℝ)
          = ((ℓ:ℝ) - (m:ℝ)) * ((ℓ - (m+1)).factorial : ℝ) := by
        rw [show ℓ - m = (ℓ - (m+1)) + 1 by omega, Nat.factorial_succ]
        have hsub : ((ℓ - (m+1) : ℕ) : ℝ) = (ℓ:ℝ) - (m:ℝ) - 1 := by
          rw [Nat.cast_sub hm]
          push_cast
          ring
        push_cast [hsub]
        ring
      rw [hfac1, hfac2]
      have hne0 : ((ℓ:ℝ) - (m:ℝ)) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
      have hne1 : ((ℓ - (m+1)).factorial : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have _hne2 : (2*(ℓ:ℝ)+1) ≠ 0 := by positivity
      field_simp
      ring

/-! ### Triangularity of the Rodrigues family

For fixed `k`, the polynomials `rodriguesDeriv (k + j) (k + j + k)` (`j ∈ ℕ`)
have degree ≤ `j` with a nonzero `j`-th coefficient, so they span `ℝ[X]`.
Through `assocLegendreNat`, this makes `sin^k θ · q(cos θ)` reachable from the
associated Legendre functions for *every* polynomial `q`. -/

lemma X_sq_sub_one_monic : (Polynomial.X ^ 2 - 1 : Polynomial ℝ).Monic := by
  simpa using Polynomial.monic_X_pow_sub_C (1 : ℝ) two_ne_zero

lemma X_sq_sub_one_natDegree :
    (Polynomial.X ^ 2 - 1 : Polynomial ℝ).natDegree = 2 := by
  rw [show (1 : Polynomial ℝ) = Polynomial.C 1 from Polynomial.C_1.symm]
  exact Polynomial.natDegree_X_pow_sub_C

/-- `d^{ℓ+k}(x²-1)^ℓ` has degree at most `ℓ - k`. -/
lemma rodriguesDeriv_natDegree_le (ℓ k : ℕ) :
    (rodriguesDeriv ℓ (ℓ + k)).natDegree ≤ ℓ - k := by
  unfold rodriguesDeriv
  have h := Polynomial.natDegree_iterate_derivative
    ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ ℓ) (ℓ + k)
  have hdeg : ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ ℓ).natDegree = 2 * ℓ := by
    rw [X_sq_sub_one_monic.natDegree_pow, X_sq_sub_one_natDegree, Nat.mul_comm ℓ 2]
  rw [hdeg] at h
  omega

/-- The top (`ℓ-k`)-th coefficient of `d^{ℓ+k}(x²-1)^ℓ` is the nonzero falling
    factorial `(2ℓ)·(2ℓ-1)⋯(ℓ-k+1)` — differentiation never kills the leading
    monomial of the monic `(x²-1)^ℓ` in characteristic zero. -/
lemma rodriguesDeriv_coeff_ne_zero (ℓ k : ℕ) (hk : k ≤ ℓ) :
    (rodriguesDeriv ℓ (ℓ + k)).coeff (ℓ - k) ≠ 0 := by
  unfold rodriguesDeriv
  rw [Polynomial.coeff_iterate_derivative]
  have h2ℓ : ℓ - k + (ℓ + k) = 2 * ℓ := by omega
  rw [h2ℓ]
  have hcoeff : ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ ℓ).coeff (2 * ℓ) = 1 := by
    have h := (X_sq_sub_one_monic.pow (n := ℓ)).coeff_natDegree
    rwa [X_sq_sub_one_monic.natDegree_pow, X_sq_sub_one_natDegree,
      Nat.mul_comm ℓ 2] at h
  rw [hcoeff, nsmul_eq_mul, mul_one]
  exact Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (by omega)).ne'

/-- A triangular family of polynomials — `T j` of degree ≤ `j` with nonzero
    `j`-th coefficient — spans `ℝ[X]`: strong induction on the degree, peeling
    the leading term with a scalar multiple of `T (natDegree q)`. -/
lemma span_of_natDegree (T : ℕ → Polynomial ℝ)
    (hdeg : ∀ j, (T j).natDegree ≤ j) (hcoeff : ∀ j, (T j).coeff j ≠ 0) :
    ∀ q : Polynomial ℝ, q ∈ Submodule.span ℝ (Set.range T) := by
  suffices H : ∀ N (q : Polynomial ℝ), q.natDegree ≤ N →
      q ∈ Submodule.span ℝ (Set.range T) by
    intro q
    exact H q.natDegree q le_rfl
  intro N
  induction N with
  | zero =>
      intro q hq
      have hqC : q = Polynomial.C (q.coeff 0) :=
        Polynomial.eq_C_of_natDegree_le_zero hq
      have hT0 : Polynomial.C ((T 0).coeff 0) = T 0 :=
        (Polynomial.eq_C_of_natDegree_le_zero (hdeg 0)).symm
      have hkey : q = (q.coeff 0 / (T 0).coeff 0) • T 0 := by
        rw [← hT0, Polynomial.smul_C, smul_eq_mul]
        simp only [Polynomial.coeff_C_zero, div_mul_cancel₀ _ (hcoeff 0)]
        exact hqC
      rw [hkey]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | succ N ih =>
      intro q hq
      set a : ℝ := q.coeff (N + 1) / (T (N + 1)).coeff (N + 1) with ha
      have hrem : (q - a • T (N + 1)).natDegree ≤ N := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro M hM
        rw [Polynomial.coeff_sub, Polynomial.coeff_smul, smul_eq_mul]
        rcases Nat.lt_or_ge (N + 1) M with hlt | hge
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hlt),
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (lt_of_le_of_lt (hdeg (N + 1)) hlt),
            mul_zero, sub_zero]
        · have hM1 : M = N + 1 := by omega
          subst hM1
          rw [ha, div_mul_cancel₀ _ (hcoeff (N + 1)), sub_self]
      have hsum : q = (q - a • T (N + 1)) + a • T (N + 1) := by ring
      rw [hsum]
      exact Submodule.add_mem _ (ih _ hrem)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨N + 1, rfl⟩))

end Spectra.SphericalHarmonics

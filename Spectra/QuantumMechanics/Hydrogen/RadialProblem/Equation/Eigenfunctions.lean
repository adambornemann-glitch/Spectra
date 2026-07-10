/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.ODE.Gronwall
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Kummer
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Complete
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.GenFun
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Orthogonality
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic

/-!
# Hydrogen Radial Eigenfunctions

Energy eigenvalues, explicit radial wavefunctions, their differential equation,
boundary conditions, square-integrability, and fixed-eigenvalue Wronskian uniqueness.

## Main definitions

* `hydrogenEigenvalue` — the bound-state energies `E_n = -1/(2n^2)`.
* `radialNormalization` — the normalisation constant `N_{nℓ}`.
* `hydrogenRadialWavefunction` — the radial eigenfunction `R_{nℓ}`.
* `hydrogenReducedWavefunction` — the reduced radial eigenfunction `χ_{nℓ} = r · R_{nℓ}`.
* `radialHamiltonian` — the radial Hamiltonian acting on classical radial functions.
* `RadialL2` — square-integrability for the radial measure `r^2 dr`.

## Main statements

* `radial_eigenvalue_eq` — `R_{nℓ}` solves the radial eigenvalue equation for `r > 0`.
* `continuous_hydrogenRadialWavefunction` / `differentiable_hydrogenRadial` — `R_{nℓ}` is
  continuous and differentiable on all of `ℝ`.
* `tendsto_hydrogenRadial_mul_exp`, `tendsto_deriv_hydrogenRadial_mul_exp`,
  `tendsto_deriv2_hydrogenRadial_mul_exp` — `R_{nℓ}` and its first two derivatives decay
  exponentially: `· e^{εr} → 0` for `ε < 1/n`.
* `radial_boundary_r_zero` / `radial_boundary_r_infty` — boundary behaviour of the reduced
  wavefunction: `χ_{nℓ}(r) ~ r^{ℓ+1}` as `r → 0` and `χ_{nℓ}(r) → 0` as `r → ∞`.
* `radial_wavefunction_L2` — `R_{nℓ} ∈ L²(ℝ⁺, r² dr)`.
* `radial_wavefunction_norm` — unit norm: `∫₀^∞ |R_{nℓ}|² r² dr = 1`.
* `radial_wavefunction_orthonormal` — fixed-`ℓ` radial wavefunctions with distinct `n` are
  orthogonal.
* `radial_eigenfunction_unique` — Abel/Wronskian uniqueness (no degeneracy) at a fixed
  eigenvalue.

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

/-! ## Energy eigenvalues -/

/-- The hydrogen energy eigenvalue for principal quantum number n.
    E_n = −1/(2n²) in atomic units (ℏ = m_e = e = 1, a₀ = 1).

    In physical units: E_n = −m_e e⁴/(2ℏ²n²) = −13.6 eV / n². -/
noncomputable def hydrogenEigenvalue (n : ℕ) (_hn : 1 ≤ n) : ℝ :=
  -1 / (2 * (n : ℝ) ^ 2)

/-- The eigenvalues are negative. -/
lemma hydrogenEigenvalue_neg (n : ℕ) (hn : 1 ≤ n) :
    hydrogenEigenvalue n hn < 0 := by
  simp only [hydrogenEigenvalue]
  apply div_neg_of_neg_of_pos (by norm_num)
  positivity

/-- The eigenvalues increase toward zero: E_n < E_{n+1} < 0. -/
lemma hydrogenEigenvalue_strictMono {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n < m) :
    hydrogenEigenvalue n hn < hydrogenEigenvalue m hm := by
  simp only [hydrogenEigenvalue]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmn : (n : ℝ) < m := by exact_mod_cast hnm
  have h1 : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := by positivity
  have h2 : 2 * (n : ℝ) ^ 2 < 2 * (m : ℝ) ^ 2 := by nlinarith
  calc -1 / (2 * (n : ℝ) ^ 2)
      = -(1 / (2 * (n : ℝ) ^ 2)) := by ring
    _ < -(1 / (2 * (m : ℝ) ^ 2)) := by
        exact neg_lt_neg (one_div_lt_one_div_of_lt h1 h2)
    _ = -1 / (2 * (m : ℝ) ^ 2) := by ring

/-- The eigenvalues accumulate at zero: E_n → 0 as n → ∞. -/
lemma hydrogenEigenvalue_tendsto :
    Filter.Tendsto (fun n => hydrogenEigenvalue (n + 1) (by omega))
      Filter.atTop (nhds 0) := by
  simp only [hydrogenEigenvalue]
  have hg : Filter.Tendsto (fun n : ℕ => 2 * ((n + 1 : ℕ) : ℝ) ^ 2)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact Filter.Tendsto.div_atTop tendsto_const_nhds hg

/-! ## Radial wavefunctions -/

/-- The radial normalisation constant.
    N_{nℓ} = √((2/n)³ · (n−ℓ−1)! / (2n · (n+ℓ)!))

    This is the positive normalisation matching the associated Laguerre
    convention used in `laguerrePolynomial` (the "mathematician's" L_n^α,
    with L_0^α = 1 and L_1^α = 1 + α − x). It is chosen so that
    ∫₀^∞ |R_{nℓ}(r)|² r² dr = 1.

    (Texts using the "physicist's" Laguerre — which carries an extra (n+ℓ)!
    factor — write the denominator as 2n·((n+ℓ)!)³ instead, and some adopt a
    Condon–Shortley minus sign; both are convention choices.) -/
noncomputable def radialNormalization (n : ℕ) (ℓ : ℕ) (_hn : ℓ + 1 ≤ n) : ℝ :=
  Real.sqrt ((2 / (n : ℝ)) ^ 3 * ((n - ℓ - 1).factorial : ℝ) /
    (2 * (n : ℝ) * ((n + ℓ).factorial : ℝ)))

/-- The hydrogen radial wavefunction R_{nℓ}(r).

    R_{nℓ}(r) = N_{nℓ} · (2r/n)^ℓ · e^{−r/n} · L_{n−ℓ−1}^{2ℓ+1}(2r/n)

    This is the radial part of the full wavefunction ψ_{nℓm} = R_{nℓ} Y_ℓ^m.

    Both the Laplace method (complex contour integrals) and the Frobenius
    method used in modern textbooks arrive at the same Laguerre polynomials. -/
noncomputable def hydrogenRadialWavefunction (n : ℕ) (ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ℝ → ℝ :=
  fun r =>
    radialNormalization n ℓ hn *
    (2 * r / n) ^ ℓ *
    Real.exp (-r / n) *
    laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n)

/-- The reduced radial wavefunction χ_{nℓ}(r) = r · R_{nℓ}(r). -/
noncomputable def hydrogenReducedWavefunction (n : ℕ) (ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ℝ → ℝ :=
  fun r => r * hydrogenRadialWavefunction n ℓ hn r

/-! ## The radial Hamiltonian -/

/-- The radial Hamiltonian H_ℓ acting on a radial function ψ (in atomic units,
    ℏ = m_e = e = 1):

    H_ℓ ψ = −½ ψ'' − (1/r) ψ' + ℓ(ℓ+1)/(2r²) · ψ − (1/r) · ψ.

    The first two terms are the radial part of −½∇² (kinetic energy); the
    third is the centrifugal barrier; the last is the Coulomb potential −1/r.
    With these conventions the eigenvalues are E_n = −1/(2n²)
    (see `hydrogenEigenvalue` and `radial_eigenvalue_eq`). -/
noncomputable def radialHamiltonian (ℓ : ℕ) (ψ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(1 / 2) * deriv^[2] ψ r - (1 / r) * deriv ψ r
    + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2)) * ψ r - (1 / r) * ψ r

/-- Square-integrability with respect to the radial measure r² dr on (0, ∞):
    `ψ ∈ L²(ℝ⁺, r² dr)` iff `r ↦ ψ(r)² · r²` is integrable on (0, ∞). -/
def RadialL2 (ψ : ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun r => ψ r ^ 2 * r ^ 2) (Set.Ioi 0) MeasureTheory.volume

/-! ## Eigenvalue equation -/

/-- Power bookkeeping: `r · (ℓ · r^{ℓ-1}) = ℓ · r^ℓ`, valid for all `ℓ`
    (the `ℓ = 0` case holds because the coefficient `ℓ` vanishes). -/
private lemma natCast_mul_pow_pred (ℓ : ℕ) (y : ℝ) :
    y * ((ℓ : ℝ) * y ^ (ℓ - 1)) = (ℓ : ℝ) * y ^ ℓ := by
  cases ℓ with
  | zero => simp
  | succ k => rw [Nat.add_sub_cancel, pow_succ]; push_cast; ring

/-- Power bookkeeping for the second derivative:
    `r² · (ℓ · (ℓ-1) · r^{ℓ-2}) = ℓ · (ℓ-1) · r^ℓ`, for all `ℓ`. -/
private lemma natCast_mul_pow_pred_two (ℓ : ℕ) (y : ℝ) :
    y ^ 2 * ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * y ^ (ℓ - 2)) =
      (ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * y ^ ℓ := by
  match ℓ with
  | 0 => simp
  | 1 => simp
  | (k + 2) =>
    rw [show k + 2 - 2 = k from rfl, show k + 2 - 1 = k + 1 from rfl, pow_succ, pow_succ]
    push_cast; ring

/-- Factored form of the radial wavefunction, pulling the explicit `x^ℓ`
    out front so that the variable base of the power is just `x`. -/
private lemma hydrogenRadial_eq_factored (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    hydrogenRadialWavefunction n ℓ hn = fun x =>
      radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * x ^ ℓ *
        Real.exp (-x / n) * laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n) := by
  funext x
  unfold hydrogenRadialWavefunction
  rw [show (2 * x / (n : ℝ)) ^ ℓ = (2 / (n : ℝ)) ^ ℓ * x ^ ℓ by rw [← mul_pow]; congr 1; ring]
  ring

/-- First derivative of the radial wavefunction (closed form, valid everywhere). -/
private lemma deriv_hydrogenRadial (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (hydrogenRadialWavefunction n ℓ hn) = fun x =>
      radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
        (ℓ : ℝ) * x ^ (ℓ - 1) * Real.exp (-x / n) *
          laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)
        + x ^ ℓ * Real.exp (-x / n) * (-(1 / n)) *
          laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)
        + x ^ ℓ * Real.exp (-x / n) *
          ((2 / n) * deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * x / n))) := by
  funext x
  rw [hydrogenRadial_eq_factored n ℓ hn]
  set A := radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ with _hA
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with _hLdef
  have hLd : ∀ y, HasDerivAt L (deriv L y) y :=
    fun y => ((laguerre_smooth _ _).differentiable (by simp)).differentiableAt.hasDerivAt
  have hpow := hasDerivAt_pow ℓ x
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x / n)) (Real.exp (-x / n) * (-1 / n)) x := by
    have hin : HasDerivAt (fun x : ℝ => -x / n) (-1 / n) x := by
      simpa using (hasDerivAt_id x).neg.div_const (n : ℝ)
    simpa using hin.exp
  have hcomp : HasDerivAt (fun x : ℝ => L (2 * x / n)) (deriv L (2 * x / n) * (2 / n)) x := by
    have hin : HasDerivAt (fun x : ℝ => 2 * x / n) (2 / n) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).div_const (n : ℝ)
    exact (hLd (2 * x / n)).comp x hin
  have hF : HasDerivAt (fun x : ℝ => A * x ^ ℓ * Real.exp (-x / n) * L (2 * x / n)) _ x :=
    ((hpow.const_mul A).mul hexp).mul hcomp
  rw [hF.deriv]
  simp only [Pi.mul_apply]
  ring

/-- The derivative of an associated Laguerre polynomial is again differentiable. -/
private lemma differentiable_deriv_laguerre (p : ℕ) (α : ℝ) :
    Differentiable ℝ (deriv (laguerrePolynomial p α)) := by
  have heq : deriv (laguerrePolynomial p α) = fun y => ∑ k ∈ Finset.range (p + 1),
      (-1 : ℝ) ^ k * realBinom (p + α) (p - k) * ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ)) := by
    funext y; exact deriv_laguerrePolynomial p α y
  rw [heq]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ∑ k ∈ Finset.range (p + 1),
      (-1 : ℝ) ^ k * realBinom (p + α) (p - k) * ((k : ℝ) * y ^ (k - 1) / (k.factorial : ℝ))) := by
    apply ContDiff.sum
    intro k _
    exact contDiff_const.mul ((contDiff_const.mul (contDiff_id.pow (k - 1))).div_const _)
  exact hcd.differentiable (by simp)

/-- Second derivative of the radial wavefunction (closed form, valid everywhere). -/
private lemma deriv2_hydrogenRadial (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv^[2] (hydrogenRadialWavefunction n ℓ hn) = fun x =>
      radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * Real.exp (-x / n) * (
        (4 / n ^ 2) * x ^ ℓ * deriv^[2] (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * x / n)
        + (4 * ℓ / n) * x ^ (ℓ - 1) * deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * x / n)
        - (4 / n ^ 2) * x ^ ℓ * deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * x / n)
        + (ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * x ^ (ℓ - 2) *
          laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)
        - (2 * ℓ / n) * x ^ (ℓ - 1) * laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)
        + (1 / n ^ 2) * x ^ ℓ * laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)) := by
  funext x
  have h2 : deriv^[2] (hydrogenRadialWavefunction n ℓ hn) x
      = deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) x := rfl
  rw [h2, deriv_hydrogenRadial n ℓ hn]
  set A := radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ with _hA
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with _hLdef
  have hLd : ∀ y, HasDerivAt L (deriv L y) y :=
    fun y => ((laguerre_smooth _ _).differentiable (by simp)).differentiableAt.hasDerivAt
  have hLd2 : ∀ y, HasDerivAt (deriv L) (deriv^[2] L y) y :=
    fun y => (differentiable_deriv_laguerre _ _ y).hasDerivAt
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x / n)) (Real.exp (-x / n) * (-1 / n)) x := by
    have hin : HasDerivAt (fun x : ℝ => -x / n) (-1 / n) x := by
      simpa using (hasDerivAt_id x).neg.div_const (n : ℝ)
    simpa using hin.exp
  have hin2 : HasDerivAt (fun x : ℝ => 2 * x / n) (2 / n) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).div_const (n : ℝ)
  have hcomp : HasDerivAt (fun x : ℝ => L (2 * x / n)) (deriv L (2 * x / n) * (2 / n)) x := by
    exact (hLd (2 * x / n)).comp x hin2
  have hcomp' : HasDerivAt (fun x : ℝ => deriv L (2 * x / n))
      (deriv^[2] L (2 * x / n) * (2 / n)) x := by
    exact (hLd2 (2 * x / n)).comp x hin2
  have hpowℓ := hasDerivAt_pow ℓ x
  have hpowℓ1 := hasDerivAt_pow (ℓ - 1) x
  have hD1 : HasDerivAt (fun x : ℝ => A * (
      (ℓ : ℝ) * x ^ (ℓ - 1) * Real.exp (-x / n) * L (2 * x / n)
      + x ^ ℓ * Real.exp (-x / n) * (-(1 / n)) * L (2 * x / n)
      + x ^ ℓ * Real.exp (-x / n) * ((2 / n) * deriv L (2 * x / n)))) _ x :=
    ((((hpowℓ1.const_mul (ℓ : ℝ)).mul hexp).mul hcomp).add
      (((hpowℓ.mul hexp).mul_const (-(1 / (n : ℝ)))).mul hcomp)).add
      ((hpowℓ.mul hexp).mul (hcomp'.const_mul (2 / (n : ℝ)))) |>.const_mul A
  rw [hD1.deriv]
  simp only [Pi.mul_apply]
  rw [show ℓ - 1 - 1 = ℓ - 2 from by omega]
  ring

/-- A single monomial times exponential decay tends to zero. -/
lemma tendsto_pow_mul_exp_neg_div (j m : ℕ) (hm : 0 < m) :
    Filter.Tendsto (fun r : ℝ => r ^ j * Real.exp (-r / m)) Filter.atTop (nhds 0) := by
  have hb : (0 : ℝ) < 1 / (m : ℝ) := by
    have : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    positivity
  refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j : ℝ) (1 / (m : ℝ)) hb).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r _hr
  rw [Real.rpow_natCast, show -(1 / (m : ℝ)) * r = -r / m from by ring]

/-- `r^a · e^{−r/n} · L_p^β(2r/n) → 0` at infinity (a monomial × exp × Laguerre). -/
private lemma tendsto_pow_exp_laguerre (n p a : ℕ) (β : ℝ) (hn : 0 < n) :
    Filter.Tendsto (fun r : ℝ => r ^ a * Real.exp (-r / n) * laguerrePolynomial p β (2 * r / n))
      Filter.atTop (nhds 0) := by
  have heq : (fun r : ℝ => r ^ a * Real.exp (-r / n) * laguerrePolynomial p β (2 * r / n))
      = fun r => ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * realBinom (p + β) (p - k) / (k.factorial : ℝ) * (2 / (n : ℝ)) ^ k)
            * (r ^ (a + k) * Real.exp (-r / n)) := by
    funext r
    simp only [laguerrePolynomial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [heq, show (0 : ℝ) = ∑ _k ∈ Finset.range (p + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun k _ => ?_)
  simpa using (tendsto_pow_mul_exp_neg_div (a + k) n hn).const_mul _

/-- `r^a · e^{−r/n} · (L_p^β)'(2r/n) → 0` at infinity. -/
private lemma tendsto_pow_exp_deriv_laguerre (n p a : ℕ) (β : ℝ) (hn : 0 < n) :
    Filter.Tendsto
      (fun r : ℝ => r ^ a * Real.exp (-r / n) * deriv (laguerrePolynomial p β) (2 * r / n))
      Filter.atTop (nhds 0) := by
  have heq : (fun r : ℝ => r ^ a * Real.exp (-r / n) * deriv (laguerrePolynomial p β) (2 * r / n))
      = fun r => ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * realBinom (p + β) (p - k) * (k : ℝ) / (k.factorial : ℝ) *
            (2 / (n : ℝ)) ^ (k - 1)) * (r ^ (a + (k - 1)) * Real.exp (-r / n)) := by
    funext r
    rw [deriv_laguerrePolynomial p β (2 * r / n)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [heq, show (0 : ℝ) = ∑ _k ∈ Finset.range (p + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun k _ => ?_)
  simpa using (tendsto_pow_mul_exp_neg_div (a + (k - 1)) n hn).const_mul _

/-- The radial wavefunction decays to zero at infinity. -/
private lemma tendsto_hydrogenRadial_atTop (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Filter.Tendsto (hydrogenRadialWavefunction n ℓ hn) Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : hydrogenRadialWavefunction n ℓ hn = fun r => ∑ k ∈ Finset.range (n - ℓ - 1 + 1),
      (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ *
        ((-1 : ℝ) ^ k * realBinom ((n - ℓ - 1 : ℕ) + (2 * ℓ + 1)) ((n - ℓ - 1) - k) /
          (k.factorial : ℝ) * (2 / (n : ℝ)) ^ k)) * (r ^ (ℓ + k) * Real.exp (-r / n)) := by
    funext r
    rw [hydrogenRadial_eq_factored n ℓ hn]
    simp only [laguerrePolynomial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [heq]
  rw [show (0 : ℝ) = ∑ _k ∈ Finset.range (n - ℓ - 1 + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun k _ => ?_)
  simpa using (tendsto_pow_mul_exp_neg_div (ℓ + k) n hn').const_mul _

/-- `r^a · R_{nℓ}'(r) → 0` at infinity (any power times the derivative decays). -/
private lemma tendsto_pow_deriv_hydrogenRadial (n ℓ a : ℕ) (hn : ℓ + 1 ≤ n) :
    Filter.Tendsto (fun r : ℝ => r ^ a * deriv (hydrogenRadialWavefunction n ℓ hn) r)
      Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : (fun r : ℝ => r ^ a * deriv (hydrogenRadialWavefunction n ℓ hn) r)
      = fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
          (ℓ : ℝ) * (r ^ (a + (ℓ - 1)) * Real.exp (-r / n) *
            laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n))
          + (-(1 / (n : ℝ))) * (r ^ (a + ℓ) * Real.exp (-r / n) *
            laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n))
          + (2 / (n : ℝ)) * (r ^ (a + ℓ) * Real.exp (-r / n) *
            deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n))) := by
    funext r
    rw [deriv_hydrogenRadial n ℓ hn]
    ring
  rw [heq]
  have h1 := tendsto_pow_exp_laguerre n (n - ℓ - 1) (a + (ℓ - 1)) (2 * ℓ + 1) hn'
  have h2 := tendsto_pow_exp_laguerre n (n - ℓ - 1) (a + ℓ) (2 * ℓ + 1) hn'
  have h3 := tendsto_pow_exp_deriv_laguerre n (n - ℓ - 1) (a + ℓ) (2 * ℓ + 1) hn'
  have hsum := ((h1.const_mul (ℓ : ℝ)).add (h2.const_mul (-(1 / (n : ℝ))))).add
    (h3.const_mul (2 / (n : ℝ)))
  simpa using hsum.const_mul (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ)

/-- The radial wavefunction is differentiable everywhere. -/
lemma differentiable_hydrogenRadial (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Differentiable ℝ (hydrogenRadialWavefunction n ℓ hn) := by
  rw [hydrogenRadial_eq_factored n ℓ hn]
  have hL : Differentiable ℝ
      (fun x : ℝ => laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)) :=
    ((laguerre_smooth _ _).differentiable (by simp)).comp (by fun_prop)
  fun_prop

/-- The radial wavefunction is continuous on all of `ℝ`. -/
theorem continuous_hydrogenRadialWavefunction (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Continuous (hydrogenRadialWavefunction n ℓ hn) :=
  (differentiable_hydrogenRadial n ℓ hn).continuous

/-- The derivative of the radial wavefunction is differentiable everywhere
    (so the second derivative exists pointwise as `HasDerivAt`). -/
lemma differentiable_deriv_hydrogenRadial (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Differentiable ℝ (deriv (hydrogenRadialWavefunction n ℓ hn)) := by
  rw [deriv_hydrogenRadial n ℓ hn]
  have hL : Differentiable ℝ
      (fun x : ℝ => laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)) :=
    ((laguerre_smooth _ _).differentiable (by simp)).comp (by fun_prop)
  have hdL : Differentiable ℝ
      (fun x : ℝ => deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * x / n)) :=
    (differentiable_deriv_laguerre _ _).comp (by fun_prop)
  fun_prop

/-- **R_{nℓ} solves the radial equation.**

    H_ℓ R_{nℓ}(r) = E_n R_{nℓ}(r)   for r > 0,

    where H_ℓ is `radialHamiltonian` and E_n = `hydrogenEigenvalue n`.

    **Discharge route (~100 lines):**
    1. Substitute ρ = 2r/n, u(ρ) = e^{ρ/2} ρ^{−ℓ} R(nρ/2).
    2. The equation for u is the Laguerre ODE with parameters
       α = 2ℓ+1 and degree n−ℓ−1.
    3. By `laguerre_differential_eq`, L_{n−ℓ−1}^{2ℓ+1} satisfies this ODE.
    4. Undo the substitution. -/
theorem radial_eigenvalue_eq (n : ℕ) (ℓ : ℕ) (hn : ℓ + 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    radialHamiltonian ℓ (hydrogenRadialWavefunction n ℓ hn) r
      = hydrogenEigenvalue n (by omega) * hydrogenRadialWavefunction n ℓ hn r := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrne : r ≠ 0 := ne_of_gt hr
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with hLdef
  -- The Laguerre ODE at the point 2r/n, with the degree cast to ℝ.
  have hode := laguerre_differential_eq (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n)
  rw [← hLdef] at hode
  have hcast : ((n - ℓ - 1 : ℕ) : ℝ) = (n : ℝ) - ℓ - 1 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega : ℓ + 1 ≤ n)]; push_cast; ring
  rw [hcast] at hode
  -- Solve the ODE for the second derivative of L.
  have hL'' : deriv^[2] L (2 * r / n) =
      -(((2 * (ℓ : ℝ) + 1) + 1 - 2 * r / n) * deriv L (2 * r / n)
        + ((n : ℝ) - ℓ - 1) * L (2 * r / n)) / (2 * r / n) := by
    rw [eq_div_iff (div_ne_zero (by positivity) hn0)]
    linear_combination hode
  -- Expand the Hamiltonian, the eigenvalue and the wavefunction.
  unfold radialHamiltonian
  rw [deriv2_hydrogenRadial n ℓ hn, deriv_hydrogenRadial n ℓ hn,
    hydrogenRadial_eq_factored n ℓ hn]
  simp only [hydrogenEigenvalue, ← hLdef]
  rw [hL'']
  -- Close the field identity; split on ℓ to collapse the `r^{ℓ-1}`, `r^{ℓ-2}` powers.
  rcases lt_or_ge ℓ 2 with hℓ | hℓ
  · interval_cases ℓ <;> · field_simp; ring
  · obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 2 := ⟨ℓ - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl]
    field_simp
    push_cast
    ring

/-! ## Exponentially-weighted decay of `R_{nℓ}` and its derivatives

For the `H²`-regularity of the Cartesian eigenfunction `f(x) = c·R_{nℓ}(‖x‖)` one needs the
radial profile *and its first two derivatives* to be `L²` against `r²dr`.  The clean way to get
this is an **exponential decay with a buffer**: since `R_{nℓ}` and its derivatives are
`(polynomial)·e^{−r/n}`, multiplying by `e^{εr}` for any `0 < ε < 1/n` still tends to `0` at
`+∞`.  A bound `|R'(r)| ≤ C·e^{−εr}` then drops straight into the generic
`exp ⟹ L²` pipeline.

The proofs reduce, term by term, to the single-monomial decay `r^a·e^{−b r} → 0` (`b > 0`). -/

/-- A monomial times a (strictly) decaying exponential tends to `0` at `+∞`. -/
private lemma tendsto_pow_mul_exp_neg_mul (a : ℕ) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun r : ℝ => r ^ a * Real.exp (-b * r)) Filter.atTop (nhds 0) := by
  refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a : ℝ) b hb).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r _
  rw [Real.rpow_natCast]

/-- `r^a · e^{−b r} · L_p^β(s r) → 0` at infinity (a monomial × exp × Laguerre), for any
    decay rate `b > 0` and scale `s`. -/
private lemma tendsto_pow_mul_exp_laguerre_gen (p a : ℕ) (β s : ℝ) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun r : ℝ => r ^ a * Real.exp (-b * r) * laguerrePolynomial p β (s * r))
      Filter.atTop (nhds 0) := by
  have heq : (fun r : ℝ => r ^ a * Real.exp (-b * r) * laguerrePolynomial p β (s * r))
      = fun r => ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * realBinom (p + β) (p - k) / (k.factorial : ℝ) * s ^ k)
            * (r ^ (a + k) * Real.exp (-b * r)) := by
    funext r
    simp only [laguerrePolynomial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [heq, show (0 : ℝ) = ∑ _k ∈ Finset.range (p + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun k _ => ?_)
  simpa using (tendsto_pow_mul_exp_neg_mul (a + k) hb).const_mul _

/-- `r^a · e^{−b r} · (L_p^β)'(s r) → 0` at infinity, for any decay rate `b > 0`. -/
private lemma tendsto_pow_mul_exp_deriv_laguerre_gen (p a : ℕ) (β s : ℝ) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto
      (fun r : ℝ => r ^ a * Real.exp (-b * r) * deriv (laguerrePolynomial p β) (s * r))
      Filter.atTop (nhds 0) := by
  have heq : (fun r : ℝ => r ^ a * Real.exp (-b * r) * deriv (laguerrePolynomial p β) (s * r))
      = fun r => ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * realBinom (p + β) (p - k) * (k : ℝ) / (k.factorial : ℝ) * s ^ (k - 1))
            * (r ^ (a + (k - 1)) * Real.exp (-b * r)) := by
    funext r
    rw [deriv_laguerrePolynomial p β (s * r)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [heq, show (0 : ℝ) = ∑ _k ∈ Finset.range (p + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun k _ => ?_)
  simpa using (tendsto_pow_mul_exp_neg_mul (a + (k - 1)) hb).const_mul _

/-- `r^a · e^{−b r} · (L_p^β)''(s r) → 0` at infinity, for any decay rate `b > 0`. -/
private lemma tendsto_pow_mul_exp_deriv2_laguerre_gen (p a : ℕ) (β s : ℝ) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto
      (fun r : ℝ => r ^ a * Real.exp (-b * r) * deriv^[2] (laguerrePolynomial p β) (s * r))
      Filter.atTop (nhds 0) := by
  have heq : (fun r : ℝ => r ^ a * Real.exp (-b * r) * deriv^[2] (laguerrePolynomial p β) (s * r))
      = fun r => ∑ k ∈ Finset.range (p + 1),
          ((-1 : ℝ) ^ k * realBinom (p + β) (p - k) * ((k : ℝ) * (k - 1 : ℝ)) /
              (k.factorial : ℝ) * s ^ (k - 2))
            * (r ^ (a + (k - 2)) * Real.exp (-b * r)) := by
    funext r
    rw [deriv2_laguerrePolynomial p β (s * r)]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [heq, show (0 : ℝ) = ∑ _k ∈ Finset.range (p + 1), (0 : ℝ) from by simp]
  refine tendsto_finsetSum _ (fun k _ => ?_)
  simpa using (tendsto_pow_mul_exp_neg_mul (a + (k - 2)) hb).const_mul _

/-- Buffered Laguerre decay: `r^a · e^{−r/n} · L_p^β(2r/n) · e^{εr} → 0` for `ε < 1/n`. -/
lemma tendsto_pow_exp_laguerre_buffer (n p a : ℕ) (β : ℝ) {ε : ℝ} (_hn : 0 < n)
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto (fun r : ℝ => r ^ a * Real.exp (-r / n) *
        laguerrePolynomial p β (2 * r / n) * Real.exp (ε * r)) Filter.atTop (nhds 0) := by
  have hb : (0 : ℝ) < 1 / (n : ℝ) - ε := by linarith
  refine (tendsto_pow_mul_exp_laguerre_gen p a β (2 / (n : ℝ)) hb).congr (fun r => ?_)
  rw [show (2 / (n : ℝ)) * r = 2 * r / n from by ring,
    show Real.exp (-(1 / (n : ℝ) - ε) * r) = Real.exp (-r / n) * Real.exp (ε * r) from by
      rw [← Real.exp_add]; congr 1; ring]
  ring

/-- Buffered Laguerre-derivative decay: `r^a · e^{−r/n} · (L_p^β)'(2r/n) · e^{εr} → 0`. -/
lemma tendsto_pow_exp_deriv_laguerre_buffer (n p a : ℕ) (β : ℝ) {ε : ℝ} (_hn : 0 < n)
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto (fun r : ℝ => r ^ a * Real.exp (-r / n) *
        deriv (laguerrePolynomial p β) (2 * r / n) * Real.exp (ε * r)) Filter.atTop (nhds 0) := by
  have hb : (0 : ℝ) < 1 / (n : ℝ) - ε := by linarith
  refine (tendsto_pow_mul_exp_deriv_laguerre_gen p a β (2 / (n : ℝ)) hb).congr (fun r => ?_)
  rw [show (2 / (n : ℝ)) * r = 2 * r / n from by ring,
    show Real.exp (-(1 / (n : ℝ) - ε) * r) = Real.exp (-r / n) * Real.exp (ε * r) from by
      rw [← Real.exp_add]; congr 1; ring]
  ring

/-- Buffered Laguerre-second-derivative decay:
    `r^a · e^{−r/n} · (L_p^β)''(2r/n) · e^{εr} → 0`. -/
lemma tendsto_pow_exp_deriv2_laguerre_buffer (n p a : ℕ) (β : ℝ) {ε : ℝ} (_hn : 0 < n)
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto (fun r : ℝ => r ^ a * Real.exp (-r / n) *
        deriv^[2] (laguerrePolynomial p β) (2 * r / n) * Real.exp (ε * r))
      Filter.atTop (nhds 0) := by
  have hb : (0 : ℝ) < 1 / (n : ℝ) - ε := by linarith
  refine (tendsto_pow_mul_exp_deriv2_laguerre_gen p a β (2 / (n : ℝ)) hb).congr (fun r => ?_)
  rw [show (2 / (n : ℝ)) * r = 2 * r / n from by ring,
    show Real.exp (-(1 / (n : ℝ) - ε) * r) = Real.exp (-r / n) * Real.exp (ε * r) from by
      rw [← Real.exp_add]; congr 1; ring]
  ring

/-- **The radial wavefunction decays exponentially**:
    `R_{nℓ}(r) · e^{εr} → 0` for `ε < 1/n`. -/
theorem tendsto_hydrogenRadial_mul_exp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {ε : ℝ}
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto (fun r : ℝ => hydrogenRadialWavefunction n ℓ hn r * Real.exp (ε * r))
      Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : (fun r : ℝ => hydrogenRadialWavefunction n ℓ hn r * Real.exp (ε * r))
      = fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
          r ^ ℓ * Real.exp (-r / n) *
            laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r)) := by
    funext r
    rw [hydrogenRadial_eq_factored n ℓ hn]
    ring
  rw [heq]
  simpa using (tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) ℓ (2 * ℓ + 1) hn' hε).const_mul
    (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ)

/-- **The radial wavefunction's first derivative decays exponentially**:
    `R_{nℓ}'(r) · e^{εr} → 0` for `ε < 1/n`. -/
theorem tendsto_deriv_hydrogenRadial_mul_exp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {ε : ℝ}
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto (fun r : ℝ => deriv (hydrogenRadialWavefunction n ℓ hn) r * Real.exp (ε * r))
      Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : (fun r : ℝ => deriv (hydrogenRadialWavefunction n ℓ hn) r * Real.exp (ε * r))
      = fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
          (ℓ : ℝ) * (r ^ (ℓ - 1) * Real.exp (-r / n) *
            laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r))
          + (-(1 / (n : ℝ))) * (r ^ ℓ * Real.exp (-r / n) *
            laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r))
          + (2 / (n : ℝ)) * (r ^ ℓ * Real.exp (-r / n) *
            deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n)
              * Real.exp (ε * r))) := by
    funext r
    rw [deriv_hydrogenRadial n ℓ hn]
    ring
  rw [heq]
  have h1 := tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) (ℓ - 1) (2 * ℓ + 1) hn' hε
  have h2 := tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) ℓ (2 * ℓ + 1) hn' hε
  have h3 := tendsto_pow_exp_deriv_laguerre_buffer n (n - ℓ - 1) ℓ (2 * ℓ + 1) hn' hε
  have hsum := ((h1.const_mul (ℓ : ℝ)).add (h2.const_mul (-(1 / (n : ℝ))))).add
    (h3.const_mul (2 / (n : ℝ)))
  simpa using hsum.const_mul (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ)

/-- **The radial wavefunction's second derivative decays exponentially**:
    `R_{nℓ}''(r) · e^{εr} → 0` for `ε < 1/n`. -/
theorem tendsto_deriv2_hydrogenRadial_mul_exp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {ε : ℝ}
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto
      (fun r : ℝ => deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r * Real.exp (ε * r))
      Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : (fun r : ℝ =>
        deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r * Real.exp (ε * r))
      = fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
          (((((4 / (n : ℝ) ^ 2) * (r ^ ℓ * Real.exp (-r / n) *
              deriv^[2] (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n) * Real.exp (ε * r))
            + (4 * (ℓ : ℝ) / (n : ℝ)) * (r ^ (ℓ - 1) * Real.exp (-r / n) *
              deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n) * Real.exp (ε * r)))
            + (-(4 / (n : ℝ) ^ 2)) * (r ^ ℓ * Real.exp (-r / n) *
              deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n) * Real.exp (ε * r)))
            + ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ)) * (r ^ (ℓ - 2) * Real.exp (-r / n) *
              laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r)))
            + (-(2 * (ℓ : ℝ) / (n : ℝ))) * (r ^ (ℓ - 1) * Real.exp (-r / n) *
              laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r)))
            + (1 / (n : ℝ) ^ 2) * (r ^ ℓ * Real.exp (-r / n) *
              laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r))) := by
    funext r
    have hid : deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r
        = deriv^[2] (hydrogenRadialWavefunction n ℓ hn) r := rfl
    rw [hid, deriv2_hydrogenRadial n ℓ hn]
    ring
  rw [heq]
  have h1 := tendsto_pow_exp_deriv2_laguerre_buffer n (n - ℓ - 1) ℓ (2 * ℓ + 1) hn' hε
  have h2 := tendsto_pow_exp_deriv_laguerre_buffer n (n - ℓ - 1) (ℓ - 1) (2 * ℓ + 1) hn' hε
  have h3 := tendsto_pow_exp_deriv_laguerre_buffer n (n - ℓ - 1) ℓ (2 * ℓ + 1) hn' hε
  have h4 := tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) (ℓ - 2) (2 * ℓ + 1) hn' hε
  have h5 := tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) (ℓ - 1) (2 * ℓ + 1) hn' hε
  have h6 := tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) ℓ (2 * ℓ + 1) hn' hε
  have hsum := (((((h1.const_mul (4 / (n : ℝ) ^ 2)).add
    (h2.const_mul (4 * (ℓ : ℝ) / (n : ℝ)))).add
    (h3.const_mul (-(4 / (n : ℝ) ^ 2)))).add
    (h4.const_mul ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ)))).add
    (h5.const_mul (-(2 * (ℓ : ℝ) / (n : ℝ))))).add
    (h6.const_mul (1 / (n : ℝ) ^ 2))
  simpa using hsum.const_mul (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ)

/-! ## Boundary conditions -/

/-- **Regularity at r = 0**: χ_{nℓ}(r) ~ r^{ℓ+1} as r → 0.

    The reduced wavefunction vanishes at the origin as r^{ℓ+1}.
    This eliminates the irregular solution r^{−ℓ} which would
    make the wavefunction non-normalisable.

    **Discharge route:** Direct from the definition:
    χ(r) = r · R(r) = r · N · (2r/n)^ℓ · e^{−r/n} · L(2r/n)
    Since L(0) = L_p^α(0) = C(p+α, p) ≠ 0, we get χ(r) ~ r^{ℓ+1}. -/
theorem radial_boundary_r_zero (n : ℕ) (ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Filter.Tendsto (fun r => hydrogenReducedWavefunction n ℓ hn r / r ^ (ℓ + 1))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ *
        laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) 0)) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set g : ℝ → ℝ := fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ *
    Real.exp (-r / n) * laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) with hg_def
  have hL : Continuous (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) :=
    (laguerre_smooth _ _).continuous
  -- g is continuous at 0.
  have hg : ContinuousAt g 0 := by
    rw [hg_def]
    apply ContinuousAt.mul
    · exact continuousAt_const.mul (by fun_prop)
    · exact hL.continuousAt.comp (by fun_prop)
  -- The value of g at 0 is the claimed limit (exp 0 = 1, L evaluated at 0).
  have hg0 : g 0 = radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ *
      laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) 0 := by
    rw [hg_def]; simp
  -- For r > 0 the quotient equals g r (the r^{ℓ+1} cancels exactly).
  have heq : (fun r => hydrogenReducedWavefunction n ℓ hn r / r ^ (ℓ + 1))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] g := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [Set.mem_Ioi] at hr
    have _hrne : r ≠ 0 := ne_of_gt hr
    rw [hg_def]
    unfold hydrogenReducedWavefunction hydrogenRadialWavefunction
    have h2n : (2 * r / (n : ℝ)) ^ ℓ = (2 / (n : ℝ)) ^ ℓ * r ^ ℓ := by
      rw [← mul_pow]; congr 1; ring
    rw [h2n]
    field_simp
    ring
  rw [← hg0]
  exact (hg.continuousWithinAt).congr' heq.symm

/-- **Decay at r → ∞**: the reduced wavefunction χ_{nℓ}(r) → 0 as r → ∞.

    χ_{nℓ}(r) = N · r^{ℓ+1} e^{−r/n} L_{n−ℓ−1}^{2ℓ+1}(2r/n) is a polynomial in r
    of degree n times e^{−r/n}, and exponential decay dominates polynomial growth,
    so χ → 0. (Note: a literal bound `|χ(r)| ≤ C e^{−r/n}` is *false* — the
    degree-n polynomial prefactor is unbounded; the honest statement is decay to
    zero, equivalently χ = o(e^{−r/n′}) for any n′ < n.)

    The non-polynomial solutions of the radial ODE instead grow like e^{+r/n},
    so this decay is what selects the bound states. -/
theorem radial_boundary_r_infty (n : ℕ) (ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Filter.Tendsto (hydrogenReducedWavefunction n ℓ hn) Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : hydrogenReducedWavefunction n ℓ hn = fun r =>
      radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ *
        (r ^ (ℓ + 1) * Real.exp (-r / n) *
          laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n)) := by
    funext r
    unfold hydrogenReducedWavefunction
    rw [hydrogenRadial_eq_factored n ℓ hn]
    ring
  rw [heq]
  simpa using (tendsto_pow_exp_laguerre n (n - ℓ - 1) (ℓ + 1) (2 * ℓ + 1) hn').const_mul
    (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ)

/-! ## Square-integrability -/

/-- `w_{β+1} · L_p^β · L_p^β` is integrable on `(0, ∞)`. Same monomial-expansion
    skeleton as `laguerreWeight_mul_laguerre_mul_laguerre_integrable`, but the weight
    parameter `β + 1` is one higher than the polynomial parameter `β` (this is the
    combination appearing in the radial `r² dr` norm after the substitution
    `ρ = 2r/n`, where the extra factor of `r` raises the weight by one). -/
private lemma laguerreWeight_shift_mul_sq_integrable (p : ℕ) (β : ℝ) (hβ : -1 < β) :
    IntegrableOn (fun x => laguerreWeight (β + 1) x *
      laguerrePolynomial p β x * laguerrePolynomial p β x) (Set.Ioi 0) := by
  have key : ∀ x : ℝ,
      laguerreWeight (β + 1) x * laguerrePolynomial p β x * laguerrePolynomial p β x
      = ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p + 1),
          (((-1 : ℝ) ^ i * realBinom (p + β) (p - i) / (i.factorial : ℝ))
            * ((-1 : ℝ) ^ j * realBinom (p + β) (p - j) / (j.factorial : ℝ)))
          * (laguerreWeight (β + 1) x * x ^ (i + j)) := by
    intro x
    simp only [laguerrePolynomial]
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hsum : IntegrableOn
      (fun x => ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p + 1),
          (((-1 : ℝ) ^ i * realBinom (p + β) (p - i) / (i.factorial : ℝ))
            * ((-1 : ℝ) ^ j * realBinom (p + β) (p - j) / (j.factorial : ℝ)))
          * (laguerreWeight (β + 1) x * x ^ (i + j))) (Set.Ioi 0) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact Integrable.const_mul (laguerreWeight_mul_pow_integrable (β + 1) (by linarith) (i + j)) _
  exact hsum.congr_fun (fun x _ => (key x).symm) measurableSet_Ioi

/-- **R_{nℓ} ∈ L²(ℝ⁺, r² dr).**

    **Discharge route:** Substitute `r = (n/2) x`. Then
    `R_{nℓ}((n/2)x)² · ((n/2)x)² = N² (n/2)² · x^{2ℓ+2} e^{−x} · L(x)²`,
    which is `w_{2ℓ+2}(x) · L(x)²` up to a constant — integrable by
    `laguerreWeight_shift_mul_sq_integrable`. The scaling `x ↦ (n/2)x`
    preserves integrability on `(0, ∞)`. -/
theorem radial_wavefunction_L2 (n : ℕ) (ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    RadialL2 (hydrogenRadialWavefunction n ℓ hn) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have ha : (0 : ℝ) < (n : ℝ) / 2 := by positivity
  have hβ : (-1 : ℝ) < 2 * ℓ + 1 := by have := Nat.cast_nonneg (α := ℝ) ℓ; linarith
  unfold RadialL2
  -- Change of variables r = (n/2) x.
  have hiff := integrableOn_Ioi_comp_mul_left_iff
    (fun r => hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2) 0 ha
  rw [mul_zero] at hiff
  rw [← hiff]
  -- The scaled integrand is a constant times w_{2ℓ+2} · L².
  have hsq := (laguerreWeight_shift_mul_sq_integrable (n - ℓ - 1) (2 * ℓ + 1) hβ).const_mul
    (radialNormalization n ℓ hn ^ 2 * ((n : ℝ) / 2) ^ 2)
  refine IntegrableOn.congr_fun hsq (fun x hx => ?_) measurableSet_Ioi
  rw [Set.mem_Ioi] at hx
  simp only [hydrogenRadialWavefunction, laguerreWeight, if_pos hx]
  rw [show (2 : ℝ) * ((n : ℝ) / 2 * x) / n = x from by field_simp,
      show -((n : ℝ) / 2 * x) / n = -(x / 2) from by field_simp,
      show (2 * (ℓ : ℝ) + 1) + 1 = ((2 * ℓ + 2 : ℕ) : ℝ) from by push_cast; ring,
      Real.rpow_natCast x (2 * ℓ + 2),
      show Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) from by
        rw [← Real.exp_add]; congr 1; ring]
  ring

/-! ## Orthonormality -/

/-- **Orthonormality of radial wavefunctions.**

    ∫₀^∞ R_{nℓ}(r) R_{n'ℓ}(r) r² dr = δ_{nn'}

    (Same ℓ, different n.)

    **Discharge route:**
    Substitute ρ = 2r/n, reduce to `laguerre_orthogonality` with
    α = 2ℓ+1 and weight ρ^{2ℓ+1} e^{−ρ}. The normalisation constant
    is chosen precisely to give 1. -/
theorem radial_wavefunction_orthonormal (n n' : ℕ) (ℓ : ℕ)
    (hn : ℓ + 1 ≤ n) (hn' : ℓ + 1 ≤ n') (hnn' : n ≠ n') :
    ∫ r in Set.Ioi 0,
      hydrogenRadialWavefunction n ℓ hn r * hydrogenRadialWavefunction n' ℓ hn' r * r ^ 2 = 0 := by
  have hn0 : 0 < n := by omega
  have hn'0 : 0 < n' := by omega
  set Rn := hydrogenRadialWavefunction n ℓ hn with hRndef
  set Rn' := hydrogenRadialWavefunction n' ℓ hn' with hRn'def
  set En : ℝ := -1 / (2 * (n : ℝ) ^ 2) with hEn
  set En' : ℝ := -1 / (2 * (n' : ℝ) ^ 2) with hEn'
  set W : ℝ → ℝ := fun r => Rn r * (r ^ 2 * deriv Rn' r) - Rn' r * (r ^ 2 * deriv Rn r) with hWdef
  set W' : ℝ → ℝ := fun r => 2 * (En - En') * (Rn r * Rn' r * r ^ 2) with hW'def
  -- Continuity facts.
  have cRn : Continuous Rn := (differentiable_hydrogenRadial n ℓ hn).continuous
  have cRn' : Continuous Rn' := (differentiable_hydrogenRadial n' ℓ hn').continuous
  have cdRn : Continuous (deriv Rn) := (differentiable_deriv_hydrogenRadial n ℓ hn).continuous
  have cdRn' : Continuous (deriv Rn') := (differentiable_deriv_hydrogenRadial n' ℓ hn').continuous
  -- Eigenvalues are distinct.
  have hEne : En ≠ En' := by
    rcases lt_or_gt_of_ne hnn' with h | h
    · have hlt := hydrogenEigenvalue_strictMono (by omega : 1 ≤ n) (by omega : 1 ≤ n') h
      simp only [hydrogenEigenvalue] at hlt
      exact ne_of_lt hlt
    · have hlt := hydrogenEigenvalue_strictMono (by omega : 1 ≤ n') (by omega : 1 ≤ n) h
      simp only [hydrogenEigenvalue] at hlt
      exact (ne_of_lt hlt).symm
  -- W' is the derivative of W on (0, ∞).
  have hW_deriv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt W (W' r) r := by
    intro r hr
    rw [Set.mem_Ioi] at hr
    have hrne : r ≠ 0 := ne_of_gt hr
    have hRnd : HasDerivAt Rn (deriv Rn r) r := (differentiable_hydrogenRadial n ℓ hn r).hasDerivAt
    have hRn'd : HasDerivAt Rn' (deriv Rn' r) r :=
      (differentiable_hydrogenRadial n' ℓ hn' r).hasDerivAt
    have hdRn : HasDerivAt (deriv Rn) (deriv^[2] Rn r) r :=
      (differentiable_deriv_hydrogenRadial n ℓ hn r).hasDerivAt
    have hdRn' : HasDerivAt (deriv Rn') (deriv^[2] Rn' r) r :=
      (differentiable_deriv_hydrogenRadial n' ℓ hn' r).hasDerivAt
    have hr2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have hg' : HasDerivAt (fun r => r ^ 2 * deriv Rn' r)
        (2 * r * deriv Rn' r + r ^ 2 * deriv^[2] Rn' r) r := hr2.mul hdRn'
    have hg : HasDerivAt (fun r => r ^ 2 * deriv Rn r)
        (2 * r * deriv Rn r + r ^ 2 * deriv^[2] Rn r) r := hr2.mul hdRn
    -- Eigenvalue equations, solved for the second derivatives.
    have heqn := radial_eigenvalue_eq n ℓ hn r hr
    have heqn' := radial_eigenvalue_eq n' ℓ hn' r hr
    rw [← hRndef] at heqn
    rw [← hRn'def] at heqn'
    simp only [radialHamiltonian, hydrogenEigenvalue, ← hEn] at heqn
    simp only [radialHamiltonian, hydrogenEigenvalue, ← hEn'] at heqn'
    have hX : deriv^[2] Rn r =
        -2 * (En * Rn r + (1 / r) * deriv Rn r
          - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2)) * Rn r + (1 / r) * Rn r) := by
      linear_combination -2 * heqn
    have hX' : deriv^[2] Rn' r =
        -2 * (En' * Rn' r + (1 / r) * deriv Rn' r
          - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2)) * Rn' r + (1 / r) * Rn' r) := by
      linear_combination -2 * heqn'
    convert (hRnd.mul hg').sub (hRn'd.mul hg) using 1
    rw [hW'def, hX, hX']
    field_simp
    ring
  -- W is continuous and vanishes at 0.
  have hWcont : Continuous W := by rw [hWdef]; fun_prop
  have hW0 : W 0 = 0 := by rw [hWdef]; simp
  -- W → 0 at infinity.
  have hlim : Filter.Tendsto W Filter.atTop (nhds 0) := by
    rw [hWdef]
    have t1 := (tendsto_hydrogenRadial_atTop n ℓ hn).mul
      (tendsto_pow_deriv_hydrogenRadial n' ℓ 2 hn')
    have t2 := (tendsto_hydrogenRadial_atTop n' ℓ hn').mul
      (tendsto_pow_deriv_hydrogenRadial n ℓ 2 hn)
    simpa using t1.sub t2
  -- W' is integrable on (0, ∞) (Cauchy–Schwarz: r·R ∈ L²).
  have hmemLp : ∀ (m : ℕ) (hm : ℓ + 1 ≤ m),
      MemLp (fun r => hydrogenRadialWavefunction m ℓ hm r * r) 2 (volume.restrict (Set.Ioi 0)) := by
    intro m hm
    refine (memLp_two_iff_integrable_sq ?_).2 ?_
    · exact ((differentiable_hydrogenRadial m ℓ hm).continuous.mul
        continuous_id).aestronglyMeasurable
    · exact IntegrableOn.congr_fun (radial_wavefunction_L2 m ℓ hm)
        (fun r _ => by ring) measurableSet_Ioi
  have hWint : IntegrableOn W' (Set.Ioi 0) := by
    have h := ((hmemLp n hn).integrable_mul (hmemLp n' hn')).const_mul (2 * (En - En'))
    refine h.congr (Filter.Eventually.of_forall (fun r => ?_))
    simp only [Pi.mul_apply, hW'def]
    ring
  -- FTC on (0, ∞): ∫ W' = W(∞) − W(0) = 0.
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hWcont.continuousWithinAt hW_deriv hWint hlim
  rw [hW0, sub_zero] at hFTC
  -- ∫ W' = 2(En−En')·∫ RₙRₙ'r², so the integral vanishes.
  rw [hW'def] at hFTC
  rw [integral_const_mul] at hFTC
  have hc : 2 * (En - En') ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.2 hEne)
  exact (mul_eq_zero.1 hFTC).resolve_left hc

/-- **Unit norm.**
    ∫₀^∞ |R_{nℓ}(r)|² r² dr = 1.

    **Discharge route:** Substitute `r = (n/2) x`. The integral becomes
    `(n/2) · N² (n/2)² · ∫ x · x^{2ℓ+1} e^{−x} L_{n−ℓ−1}^{2ℓ+1}(x)² dx`,
    and the inner integral is `laguerre_x_norm_sq` evaluated to
    `2n · (n+ℓ)! / (n−ℓ−1)!`. The normalisation constant `N` was chosen so the
    product collapses to `1`. -/
theorem radial_wavefunction_norm (n : ℕ) (ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ∫ r in Set.Ioi 0, hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2 = 1 := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hb : (0 : ℝ) < (n : ℝ) / 2 := by positivity
  have hβ : (-1 : ℝ) < 2 * ℓ + 1 := by have := Nat.cast_nonneg (α := ℝ) ℓ; linarith
  have hF1 : ((n - ℓ - 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF2 : ((n + ℓ).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc1 : ((n - ℓ - 1 : ℕ) : ℝ) = (n : ℝ) - ℓ - 1 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega : ℓ + 1 ≤ n)]; push_cast; ring
  -- Change of variables r = (n/2) x.
  have hcv := integral_comp_mul_left_Ioi
    (fun r => hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2) 0 hb
  simp only [mul_zero, smul_eq_mul] at hcv
  have key : (n : ℝ) / 2 *
      (∫ x in Set.Ioi (0 : ℝ), hydrogenRadialWavefunction n ℓ hn ((n : ℝ) / 2 * x) ^ 2 *
        ((n : ℝ) / 2 * x) ^ 2)
      = ∫ r in Set.Ioi (0 : ℝ), hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2 := by
    rw [hcv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), one_mul]
  -- The scaled integrand is a constant times x · w_{2ℓ+1} · L².
  have hS : (∫ x in Set.Ioi (0 : ℝ), hydrogenRadialWavefunction n ℓ hn ((n : ℝ) / 2 * x) ^ 2 *
        ((n : ℝ) / 2 * x) ^ 2)
      = radialNormalization n ℓ hn ^ 2 * ((n : ℝ) / 2) ^ 2 *
        ∫ x in Set.Ioi (0 : ℝ), laguerreWeight (2 * ℓ + 1) x * x *
          (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) x) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Set.mem_Ioi] at hx
    simp only [hydrogenRadialWavefunction, laguerreWeight, if_pos hx]
    rw [show (2 : ℝ) * ((n : ℝ) / 2 * x) / n = x from by field_simp,
        show -((n : ℝ) / 2 * x) / n = -(x / 2) from by field_simp,
        show (2 * (ℓ : ℝ) + 1) = ((2 * ℓ + 1 : ℕ) : ℝ) from by push_cast; ring,
        Real.rpow_natCast x (2 * ℓ + 1),
        show Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) from by
          rw [← Real.exp_add]; congr 1; ring]
    ring
  -- The normalisation constant squared.
  have hN2 : radialNormalization n ℓ hn ^ 2 =
      (2 / (n : ℝ)) ^ 3 * ((n - ℓ - 1).factorial : ℝ)
        / (2 * (n : ℝ) * ((n + ℓ).factorial : ℝ)) := by
    unfold radialNormalization; rw [Real.sq_sqrt (by positivity)]
  -- Evaluate the Laguerre moment and simplify the coefficient / Gamma factor.
  have hco : 2 * ((n - ℓ - 1 : ℕ) : ℝ) + (2 * (ℓ : ℝ) + 1) + 1 = 2 * n := by rw [hc1]; ring
  have hgam : Real.Gamma (((n - ℓ - 1 : ℕ) : ℝ) + (2 * (ℓ : ℝ) + 1) + 1)
      = ((n + ℓ).factorial : ℝ) := by
    rw [show (((n - ℓ - 1 : ℕ) : ℝ) + (2 * (ℓ : ℝ) + 1) + 1) = ((n + ℓ : ℕ) : ℝ) + 1 from by
      rw [hc1]; push_cast; ring, Real.Gamma_nat_eq_factorial]
  rw [← key, hS, laguerre_x_norm_sq (2 * ℓ + 1) hβ (n - ℓ - 1), hco, hgam, hN2]
  field_simp

/-! ## Uniqueness of the bound state at a fixed eigenvalue -/

/-- **No degeneracy at E_n.** Any (twice-differentiable on `(0,∞)`) solution `ψ` of the
    radial equation at energy `E_n` is linearly dependent on `R_{nℓ}`: if the Wronskian
    `ψ R' − ψ' R` vanishes at one point `r₀ > 0`, it vanishes everywhere on `(0,∞)`.

    This is Abel's identity for the radial operator: the weighted Wronskian
    `Z(r) = r²(ψ R' − ψ' R)` has derivative `2(E_n − E_n)·r²ψR = 0`, hence is constant;
    vanishing at `r₀` forces `Z ≡ 0`, and `r² ≠ 0` gives `ψ R' = ψ' R` throughout.

    It is the 1-dimensionality of the eigenspace at `E_n` — the no-degeneracy fact
    that, together with the (now proved) quantization `→` direction
    (`reduced_radial_L2_quantized`), would give that every negative-energy bound state
    is a scalar multiple of some `R_{nℓ}`. -/
theorem radial_eigenfunction_unique (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (heq : ∀ r, 0 < r → radialHamiltonian ℓ ψ r = hydrogenEigenvalue n (by omega) * ψ r)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hW0 : ψ r₀ * deriv (hydrogenRadialWavefunction n ℓ hn) r₀
      = deriv ψ r₀ * hydrogenRadialWavefunction n ℓ hn r₀) :
    ∀ r, 0 < r → ψ r * deriv (hydrogenRadialWavefunction n ℓ hn) r
      = deriv ψ r * hydrogenRadialWavefunction n ℓ hn r := by
  set R := hydrogenRadialWavefunction n ℓ hn with hRdef
  set Z : ℝ → ℝ := fun r => ψ r * (r ^ 2 * deriv R r) - R r * (r ^ 2 * deriv ψ r) with hZdef
  -- Z has derivative 0 on (0, ∞).
  have hZderiv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt Z 0 r := by
    intro r hr
    rw [Set.mem_Ioi] at hr
    have hrne : r ≠ 0 := ne_of_gt hr
    have hRd : HasDerivAt R (deriv R r) r := (differentiable_hydrogenRadial n ℓ hn r).hasDerivAt
    have hdR : HasDerivAt (deriv R) (deriv^[2] R r) r :=
      (differentiable_deriv_hydrogenRadial n ℓ hn r).hasDerivAt
    have hr2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
    have hgR : HasDerivAt (fun r => r ^ 2 * deriv R r)
        (2 * r * deriv R r + r ^ 2 * deriv^[2] R r) r := hr2.mul hdR
    have hgψ : HasDerivAt (fun r => r ^ 2 * deriv ψ r)
        (2 * r * deriv ψ r + r ^ 2 * deriv^[2] ψ r) r := hr2.mul (hψ2 r hr)
    have heqψ := heq r hr
    have heqR := radial_eigenvalue_eq n ℓ hn r hr
    rw [← hRdef] at heqR
    simp only [radialHamiltonian, hydrogenEigenvalue] at heqψ heqR
    have hXψ : deriv^[2] ψ r =
        -2 * (-1 / (2 * (n : ℝ) ^ 2) * ψ r + (1 / r) * deriv ψ r
          - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2)) * ψ r + (1 / r) * ψ r) := by
      linear_combination -2 * heqψ
    have hXR : deriv^[2] R r =
        -2 * (-1 / (2 * (n : ℝ) ^ 2) * R r + (1 / r) * deriv R r
          - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2)) * R r + (1 / r) * R r) := by
      linear_combination -2 * heqR
    convert ((hψ1 r hr).mul hgR).sub (hRd.mul hgψ) using 1
    rw [hXψ, hXR]
    field_simp
    ring
  -- Hence Z is constant on (0, ∞); it equals Z r₀ = 0.
  have hZr0 : Z r₀ = 0 := by
    have hw : ψ r₀ * deriv R r₀ - deriv ψ r₀ * R r₀ = 0 := by rw [hW0]; ring
    change ψ r₀ * (r₀ ^ 2 * deriv R r₀) - R r₀ * (r₀ ^ 2 * deriv ψ r₀) = 0
    linear_combination r₀ ^ 2 * hw
  intro r hr
  have hZeq : Z r = Z r₀ := by
    have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := Z) (f' := fun _ => (0 : ℝ)) (s := Set.Ioi 0) (C := 0)
      (fun x hx => (hZderiv x hx).hasDerivWithinAt) (fun x _ => by simp) (convex_Ioi 0)
      hr₀ (Set.mem_Ioi.2 hr)
    simpa [sub_eq_zero] using hb
  -- Z r = 0 and r² ≠ 0 give the Wronskian identity.
  have hrne : (r : ℝ) ^ 2 ≠ 0 := by positivity
  have hZr : ψ r * (r ^ 2 * deriv R r) - R r * (r ^ 2 * deriv ψ r) = 0 := by
    rw [← hZr0]; exact hZeq
  have : r ^ 2 * (ψ r * deriv R r - deriv ψ r * R r) = 0 := by linear_combination hZr
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hrne
  · linear_combination h

end QuantumMechanics.Hydrogen.RadialEq

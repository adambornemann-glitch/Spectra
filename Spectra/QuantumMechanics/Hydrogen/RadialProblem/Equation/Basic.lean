/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Orthogonality
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Complete
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.GenFun
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Kummer
import Mathlib.Analysis.ODE.Gronwall
/-!
# The Radial Equation and Eigenvalue Quantization

The radial Schrödinger equation for the hydrogen atom and the derivation
of the energy eigenvalues E_n = −1/(2n²) (in atomic units).

## Proof of quantization (mathematical structure)

1. **Substitution.** Set ρ = 2κr where κ = √(−2E), and u(ρ) = e^{ρ/2} ρ^{−ℓ−1} χ(r).
2. **Transformed ODE.** The equation for u becomes the associated Laguerre ODE:
     ρ u'' + (2ℓ + 2 − ρ) u' + (n − ℓ − 1) u = 0
   where n = 1/(2κ) (a parameter, not yet an integer).
3. **Polynomial condition.** Solutions are:
   - Polynomial (= L_{n−ℓ−1}^{2ℓ+1}) when n − ℓ − 1 is a non-negative integer.
   - Non-polynomial (divergent as ρ → ∞) otherwise.
4. **Square-integrability.** Only polynomial solutions give χ ∈ L²(ℝ⁺).
   This forces n ∈ ℕ with n ≥ ℓ + 1.
5. **Energy quantization.** E = −κ²/2 = −1/(2n²).

## Main definitions

* `hydrogenRadialWavefunction` — R_{nℓ}(r) = N_{nℓ} r^ℓ e^{−r/n} L_{n−ℓ−1}^{2ℓ+1}(2r/n).
* `hydrogenEigenvalue` — E_n = −1/(2n²).
* `radialNormalization` — the normalisation constant N_{nℓ}.

## Main statements

* `radial_eigenvalue_eq` — H_ℓ R_{nℓ} = E_n R_{nℓ}.
* `radial_quantization` — L² solutions exist iff E = E_n for some n ≥ ℓ+1.
* `radial_wavefunction_orthonormal` — ∫ R_{nℓ} R_{n'ℓ} r² dr = δ_{nn'}.
* `radial_completeness` — {R_{nℓ}}_{n≥ℓ+1} complete in discrete subspace.
* `radial_continuum` — for E ≥ 0, all solutions are bounded (continuous spectrum).

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

    **Relation to my original paper:**
    I used the Laplace method (complex contour integrals) to derive these.
    Modern textbooks use the Frobenius method. Both arrive at the same
    Laguerre polynomials. -/
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
  set A := radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ with hA
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with hLdef
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
  have hcd : ContDiff ℝ ⊤ (fun y : ℝ => ∑ k ∈ Finset.range (p + 1),
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
  set A := radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ with hA
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with hLdef
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
private lemma tendsto_pow_mul_exp_neg_div (j m : ℕ) (hm : 0 < m) :
    Filter.Tendsto (fun r : ℝ => r ^ j * Real.exp (-r / m)) Filter.atTop (nhds 0) := by
  have hb : (0 : ℝ) < 1 / (m : ℝ) := by
    have : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    positivity
  refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j : ℝ) (1 / (m : ℝ)) hb).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
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
private lemma differentiable_hydrogenRadial (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Differentiable ℝ (hydrogenRadialWavefunction n ℓ hn) := by
  rw [hydrogenRadial_eq_factored n ℓ hn]
  have hL : Differentiable ℝ (fun x : ℝ => laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)) :=
    ((laguerre_smooth _ _).differentiable (by simp)).comp (by fun_prop)
  fun_prop

/-- The radial wavefunction is continuous on all of `ℝ` (public wrapper around the
    private differentiability lemma, for use when lifting `R_{nℓ}` into `L²`). -/
theorem continuous_hydrogenRadialWavefunction (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Continuous (hydrogenRadialWavefunction n ℓ hn) :=
  (differentiable_hydrogenRadial n ℓ hn).continuous

/-- The derivative of the radial wavefunction is differentiable everywhere
    (so the second derivative exists pointwise as `HasDerivAt`). -/
private lemma differentiable_deriv_hydrogenRadial (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Differentiable ℝ (deriv (hydrogenRadialWavefunction n ℓ hn)) := by
  rw [deriv_hydrogenRadial n ℓ hn]
  have hL : Differentiable ℝ (fun x : ℝ => laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)) :=
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
  have heq : (fun r => hydrogenReducedWavefunction n ℓ hn r / r ^ (ℓ + 1)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] g := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [Set.mem_Ioi] at hr
    have hrne : r ≠ 0 := ne_of_gt hr
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
    · exact ((differentiable_hydrogenRadial m ℓ hm).continuous.mul continuous_id).aestronglyMeasurable
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
      (2 / (n : ℝ)) ^ 3 * ((n - ℓ - 1).factorial : ℝ) / (2 * (n : ℝ) * ((n + ℓ).factorial : ℝ)) := by
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
    show ψ r₀ * (r₀ ^ 2 * deriv R r₀) - R r₀ * (r₀ ^ 2 * deriv ψ r₀) = 0
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

/-! ## Reduced-equation transform and the analytic quantization core

The quantization argument is cleanest for the *reduced* wavefunction `χ = r·ψ`,
which obeys a Schrödinger-form equation with no first-derivative term:
`χ''(r) = (ℓ(ℓ+1)/r² − 2/r − 2E)·χ(r)`.
The lemmas below carry out the (fully mechanical) transform `ψ ↦ χ`, the
`κ = √(−2E)` algebra, and the `κ ↔ Eₙ` dictionary. The single remaining analytic
input — that square-integrability quantizes the decay rate — is isolated as the
documented gap lemmas `reduced_radial_L2_quantized` and `reduced_radial_continuum`
(see their docstrings for why this needs confluent-hypergeometric / Coulomb-wave
asymptotics not yet available in Mathlib). -/

/-- First derivative of `χ = r·ψ`, valid at every `r`. -/
private lemma hasDerivAt_reducedMul (ψ : ℝ → ℝ) {r : ℝ}
    (hψ : HasDerivAt ψ (deriv ψ r) r) :
    HasDerivAt (fun s => s * ψ s) (ψ r + r * deriv ψ r) r := by
  have h : HasDerivAt (fun s => s * ψ s) (1 * ψ r + r * deriv ψ r) r :=
    (hasDerivAt_id' (x := r)).mul hψ
  rwa [one_mul] at h

/-- Closed form of `deriv (r·ψ)` where `ψ` is differentiable at `r`. -/
private lemma deriv_reducedMul (ψ : ℝ → ℝ) {r : ℝ}
    (hψ : HasDerivAt ψ (deriv ψ r) r) :
    deriv (fun s => s * ψ s) r = ψ r + r * deriv ψ r :=
  (hasDerivAt_reducedMul ψ hψ).deriv

/-- On `(0,∞)` the derivative of `χ = r·ψ` agrees with the explicit closed form. -/
private lemma deriv_reducedMul_eventuallyEq (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) {r : ℝ} (hr : 0 < r) :
    deriv (fun s => s * ψ s) =ᶠ[nhds r] (fun s => ψ s + s * deriv ψ s) := by
  have hmem : Set.Ioi (0 : ℝ) ∈ nhds r := isOpen_Ioi.mem_nhds hr
  filter_upwards [hmem] with x hx
  exact deriv_reducedMul ψ (hψ1 x hx)

/-- Second derivative of `χ = r·ψ` exists at `r>0`. -/
private lemma hasDerivAt_deriv_reducedMul (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (fun s => s * ψ s))
      (2 * deriv ψ r + r * deriv^[2] ψ r) r := by
  have hbase : HasDerivAt (fun s => ψ s + s * deriv ψ s)
      (deriv ψ r + (deriv ψ r + r * deriv^[2] ψ r)) r := by
    have h1 : HasDerivAt ψ (deriv ψ r) r := hψ1 r hr
    have h2 : HasDerivAt (fun s => s * deriv ψ s) (deriv ψ r + r * deriv^[2] ψ r) r := by
      have h2' : HasDerivAt (fun s => s * deriv ψ s) (1 * deriv ψ r + r * deriv^[2] ψ r) r :=
        (hasDerivAt_id' (x := r)).mul (hψ2 r hr)
      rwa [one_mul] at h2'
    exact h1.add h2
  have hee := deriv_reducedMul_eventuallyEq ψ hψ1 hr
  have : HasDerivAt (deriv (fun s => s * ψ s))
      (deriv ψ r + (deriv ψ r + r * deriv^[2] ψ r)) r :=
    hbase.congr_of_eventuallyEq hee
  convert this using 1
  ring

/-- Closed form of `deriv^[2] (r·ψ)` at `r>0`. -/
private lemma deriv2_reducedMul (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s * ψ s) r = 2 * deriv ψ r + r * deriv^[2] ψ r := by
  show deriv (deriv (fun s => s * ψ s)) r = _
  exact (hasDerivAt_deriv_reducedMul ψ hψ1 hψ2 hr).deriv

/-- **The reduced radial equation.** If `ψ` is a `C²` classical solution of
    `H_ℓ ψ = E ψ` on `(0,∞)`, then `χ = r·ψ` solves the first-derivative-free form
    `χ''(r) = (ℓ(ℓ+1)/r² − 2/r − 2E)·χ(r)`. -/
lemma reduced_ode (ℓ : ℕ) (E : ℝ) (ψ : ℝ → ℝ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (heq : ∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s * ψ s) r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * (r * ψ r) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [deriv2_reducedMul ψ hψ1 hψ2 hr]
  have he := heq r hr
  simp only [radialHamiltonian] at he
  have hX : deriv^[2] ψ r =
      -2 * (E * ψ r + (1 / r) * deriv ψ r
        - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2)) * ψ r + (1 / r) * ψ r) := by
    linear_combination -2 * he
  rw [hX]
  field_simp
  ring

/-- `RadialL2 ψ` says exactly that the reduced wavefunction `χ = r·ψ` is in
    `L²((0,∞), dr)`. -/
private lemma reduced_integrableOn_sq (ψ : ℝ → ℝ) (h : RadialL2 ψ) :
    IntegrableOn (fun r => (r * ψ r) ^ 2) (Set.Ioi 0) := by
  unfold RadialL2 at h
  exact h.congr_fun (fun x _ => by ring) measurableSet_Ioi

/-- Nondegeneracy transfers: a point `r>0` with `ψ ≠ 0` gives one with `χ = r·ψ ≠ 0`. -/
private lemma reduced_nonzero (ψ : ℝ → ℝ) (h : ∃ r, 0 < r ∧ ψ r ≠ 0) :
    ∃ r, 0 < r ∧ r * ψ r ≠ 0 := by
  obtain ⟨r, hr, hψ⟩ := h
  exact ⟨r, hr, mul_ne_zero (ne_of_gt hr) hψ⟩

/-- For `E < 0`, the decay rate `κ = √(−2E)` is positive with `κ² = −2E`. -/
private lemma kappa_pos_sq (E : ℝ) (hE : E < 0) :
    0 < Real.sqrt (-2 * E) ∧ Real.sqrt (-2 * E) ^ 2 = -2 * E := by
  have hpos : 0 < -2 * E := by linarith
  exact ⟨Real.sqrt_pos.mpr hpos, Real.sq_sqrt (le_of_lt hpos)⟩

/-- The `κ ↔ Eₙ` dictionary: `κ = 1/m` together with `κ² = −2E` forces `E = Eₘ`. -/
private lemma energy_eq_of_kappa (E κ : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hκ2 : κ ^ 2 = -2 * E) (hκm : κ = 1 / (m : ℝ)) :
    E = hydrogenEigenvalue m hm := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hkey : (1 : ℝ) / (m : ℝ) ^ 2 = -2 * E := by
    rw [← hκ2, hκm, div_pow, one_pow]
  unfold hydrogenEigenvalue
  field_simp at hkey ⊢
  linarith

/-! ### The Frobenius/Kummer ansatz `χ = r^{ℓ+1} e^{-κr} w`

The reduced equation is solved by separating the boundary behaviour: a regular
solution has the form `χ = r^{ℓ+1} e^{-κr} w` with `w` analytic. The lemmas below
prove (purely mechanically) that this ansatz solves the reduced radial equation
*iff* `w` solves the confluent (Laguerre/Kummer) ODE. This is the substitution at
the heart of the quantization argument; what remains open is the *asymptotics* of
the Kummer solution `w` (termination ⇔ `L²`), isolated in
`reduced_radial_L2_quantized`. -/

/-- First derivative of the ansatz `χ = r^{ℓ+1} e^{-κr} w`. -/
private lemma deriv_ansatz (ℓ : ℕ) (κ : ℝ) (w : ℝ → ℝ) {r : ℝ}
    (hw : HasDerivAt w (deriv w r) r) :
    deriv (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r
      = ((ℓ : ℝ) + 1) * r ^ ℓ * Real.exp (-κ * r) * w r
        - κ * r ^ (ℓ + 1) * Real.exp (-κ * r) * w r
        + r ^ (ℓ + 1) * Real.exp (-κ * r) * deriv w r := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (ℓ + 1)) (((ℓ : ℝ) + 1) * r ^ ℓ) r := by
    simpa using hasDerivAt_pow (ℓ + 1) r
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-κ * s)) (Real.exp (-κ * r) * (-κ)) r := by
    have hin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) r := by
      simpa using (hasDerivAt_id r).const_mul (-κ)
    simpa using hin.exp
  have key : HasDerivAt (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) _ r :=
    (hpow.mul hexp).mul hw
  rw [key.deriv]
  simp only [Pi.mul_apply]
  ring

/-- Second derivative of the ansatz `χ = r^{ℓ+1} e^{-κr} w` (raw expanded form). -/
private lemma deriv2_ansatz (ℓ : ℕ) (κ : ℝ) (w : ℝ → ℝ)
    (hw1 : ∀ s, 0 < s → HasDerivAt w (deriv w s) s)
    (hw2 : ∀ s, 0 < s → HasDerivAt (deriv w) (deriv^[2] w s) s)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r
      = Real.exp (-κ * r) * (
          (ℓ : ℝ) * ((ℓ : ℝ) + 1) * r ^ (ℓ - 1) * w r
          - 2 * κ * ((ℓ : ℝ) + 1) * r ^ ℓ * w r
          + 2 * ((ℓ : ℝ) + 1) * r ^ ℓ * deriv w r
          + κ ^ 2 * r ^ (ℓ + 1) * w r
          - 2 * κ * r ^ (ℓ + 1) * deriv w r
          + r ^ (ℓ + 1) * deriv^[2] w r) := by
  have hD1eq : deriv (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) =ᶠ[nhds r]
      (fun x => ((ℓ : ℝ) + 1) * x ^ ℓ * Real.exp (-κ * x) * w x
        - κ * x ^ (ℓ + 1) * Real.exp (-κ * x) * w x
        + x ^ (ℓ + 1) * Real.exp (-κ * x) * deriv w x) := by
    have hmem : Set.Ioi (0 : ℝ) ∈ nhds r := isOpen_Ioi.mem_nhds hr
    filter_upwards [hmem] with x hx
    exact deriv_ansatz ℓ κ w (hw1 x hx)
  have hpowℓ : HasDerivAt (fun s : ℝ => s ^ ℓ) ((ℓ : ℝ) * r ^ (ℓ - 1)) r := by
    simpa using hasDerivAt_pow ℓ r
  have hpowℓ1 : HasDerivAt (fun s : ℝ => s ^ (ℓ + 1)) (((ℓ : ℝ) + 1) * r ^ ℓ) r := by
    simpa using hasDerivAt_pow (ℓ + 1) r
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-κ * s)) (Real.exp (-κ * r) * (-κ)) r := by
    have hin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) r := by
      simpa using (hasDerivAt_id r).const_mul (-κ)
    simpa using hin.exp
  have hw := hw1 r hr
  have hw2' := hw2 r hr
  have hD1 : HasDerivAt
      (fun x => ((ℓ : ℝ) + 1) * x ^ ℓ * Real.exp (-κ * x) * w x
        - κ * x ^ (ℓ + 1) * Real.exp (-κ * x) * w x
        + x ^ (ℓ + 1) * Real.exp (-κ * x) * deriv w x) _ r :=
    ((((hpowℓ.const_mul ((ℓ : ℝ) + 1)).mul hexp).mul hw).sub
      (((hpowℓ1.const_mul κ).mul hexp).mul hw)).add
      ((hpowℓ1.mul hexp).mul hw2')
  show deriv (deriv (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s)) r = _
  rw [hD1eq.deriv_eq, hD1.deriv]
  simp only [Pi.mul_apply]
  ring

/-- **The Laguerre/Kummer residual identity.** For the ansatz `χ = r^{ℓ+1} e^{-κr} w`,
    the reduced-equation residual factors through the Laguerre/Kummer operator on `w`:
    `χ''(r) − (ℓ(ℓ+1)/r² − 2/r + κ²)·χ(r)`
      `= e^{-κr} r^ℓ · (r·w'' + (2ℓ+2 − 2κr)·w' + (2 − 2(ℓ+1)κ)·w)`.
    Since `e^{-κr} r^ℓ ≠ 0` for `r > 0`, the ansatz solves the reduced radial
    equation iff `w` solves the confluent (Laguerre) ODE
    `ρ v'' + (2ℓ+2 − ρ) v' + (1/κ − ℓ − 1) v = 0` (in the variable `ρ = 2κr`). -/
lemma laguerre_ansatz_residual (ℓ : ℕ) (κ : ℝ) (w : ℝ → ℝ)
    (hw1 : ∀ s, 0 < s → HasDerivAt w (deriv w s) s)
    (hw2 : ∀ s, 0 < s → HasDerivAt (deriv w) (deriv^[2] w s) s)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r
      - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2)
        * (r ^ (ℓ + 1) * Real.exp (-κ * r) * w r)
      = Real.exp (-κ * r) * r ^ ℓ
        * (r * deriv^[2] w r + (2 * (ℓ : ℝ) + 2 - 2 * κ * r) * deriv w r
           + (2 - 2 * ((ℓ : ℝ) + 1) * κ) * w r) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [deriv2_ansatz ℓ κ w hw1 hw2 hr]
  rcases lt_or_ge ℓ 2 with hℓ | hℓ
  · interval_cases ℓ <;> · field_simp; ring
  · obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 2 := ⟨ℓ - 2, by omega⟩
    rw [show k + 2 - 1 = k + 1 from rfl]
    field_simp
    push_cast
    ring

/-- **The Kummer bridge.** The ansatz `χ = r^{ℓ+1} e^{-κr} w` solves the reduced
    radial equation `χ'' = (ℓ(ℓ+1)/r² − 2/r + κ²)·χ` at `r > 0` *iff* `w` solves
    the confluent (Laguerre) ODE there, written in the variable `r`:
    `r·w'' + (2ℓ+2 − 2κr)·w' + (2 − 2(ℓ+1)κ)·w = 0`. This is the exact substitution
    underlying `reduced_radial_L2_quantized`; only the *asymptotics* of `w` remain. -/
lemma laguerre_ansatz_reduced_iff (ℓ : ℕ) (κ : ℝ) (w : ℝ → ℝ)
    (hw1 : ∀ s, 0 < s → HasDerivAt w (deriv w s) s)
    (hw2 : ∀ s, 0 < s → HasDerivAt (deriv w) (deriv^[2] w s) s)
    {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r
        = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2)
          * (r ^ (ℓ + 1) * Real.exp (-κ * r) * w r)
      ↔ r * deriv^[2] w r + (2 * (ℓ : ℝ) + 2 - 2 * κ * r) * deriv w r
          + (2 - 2 * ((ℓ : ℝ) + 1) * κ) * w r = 0 := by
  have hfac : Real.exp (-κ * r) * r ^ ℓ ≠ 0 := by positivity
  rw [← sub_eq_zero (a := deriv^[2] (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s) r),
    laguerre_ansatz_residual ℓ κ w hw1 hw2 hr, mul_eq_zero]
  exact or_iff_right hfac

/-- **Non-`L²` from a positive lower bound at infinity.** If `|χ(r)| ≥ A > 0` for all large `r`,
    then `χ` is not square-integrable on `(0,∞)`: `χ(r)² ≥ A² > 0` on the infinite-measure set
    `(max R 1, ∞)`. This is the mechanism by which exponential growth of the Kummer factor
    (`Spectra.Kummer.kummerM_abs_exp_lower`) breaks normalisability of a non-terminating solution. -/
lemma not_radialL2_of_eventually_ge (χ : ℝ → ℝ) {A R : ℝ} (hA : 0 < A)
    (hlb : ∀ r, R ≤ r → A ≤ |χ r|) :
    ¬ IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0) := by
  intro hint
  have hc0 : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hint2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi (max R 1)) :=
    hint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hc0))
  have hbound : ∀ r ∈ Set.Ioi (max R 1), A ^ 2 ≤ χ r ^ 2 := by
    intro r hr
    rw [Set.mem_Ioi] at hr
    have hrR : R ≤ r := le_of_lt (lt_of_le_of_lt (le_max_left R 1) hr)
    nlinarith [hlb r hrR, hA, abs_nonneg (χ r), sq_abs (χ r)]
  have hconst : IntegrableOn (fun _ : ℝ => A ^ 2) (Set.Ioi (max R 1)) :=
    hint2.mono' aestronglyMeasurable_const
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hbound r hr))
  rw [integrableOn_const_iff] at hconst
  rcases hconst with h | h
  · rw [enorm_eq_zero] at h; nlinarith [hA, h]
  · rw [Real.volume_Ioi] at h; exact absurd h (lt_irrefl _)

/-! ### The explicit regular solution `φ = r^{ℓ+1} e^{−κr} M(a, 2ℓ+2, 2κr)`

The analytic core of `reduced_radial_L2_quantized`: the confluent-hypergeometric
(Kummer) machinery of `Spectra.Kummer` is assembled into the regular solution `φ`
of the reduced radial equation, whose growth at `∞` (unless the series terminates)
breaks square-integrability. -/

/-- The regular-at-`0` solution `φ(r) = r^{ℓ+1} e^{−κr} M(ℓ+1−1/κ, 2ℓ+2, 2κr)` of the reduced
radial equation. -/
noncomputable def kummerRadial (ℓ : ℕ) (κ : ℝ) : ℝ → ℝ :=
  fun r => r ^ (ℓ + 1) * Real.exp (-κ * r) *
    kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r)

/-! ### Chain-rule derivatives of `w(s) = M(a,b,2κs)` -/

private lemma kummerComp_hasDerivAt (a b κ : ℝ) (hb : 0 < b) (r : ℝ) :
    HasDerivAt (fun s => kummerM a b (2 * κ * s)) (2 * κ * deriv (kummerM a b) (2 * κ * r)) r := by
  have h1 : HasDerivAt (kummerM a b) (deriv (kummerM a b) (2 * κ * r)) (2 * κ * r) :=
    (kummerM_hasDerivAt a b hb (2 * κ * r)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => 2 * κ * s) (2 * κ) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * κ)
  have hc : HasDerivAt (fun s => kummerM a b (2 * κ * s))
      (deriv (kummerM a b) (2 * κ * r) * (2 * κ)) r := h1.comp r h2
  convert hc using 1
  ring

private lemma kummerComp_deriv (a b κ : ℝ) (hb : 0 < b) (r : ℝ) :
    deriv (fun s => kummerM a b (2 * κ * s)) r = 2 * κ * deriv (kummerM a b) (2 * κ * r) :=
  (kummerComp_hasDerivAt a b κ hb r).deriv

private lemma kummerComp_hasDerivAt2 (a b κ : ℝ) (hb : 0 < b) (r : ℝ) :
    HasDerivAt (deriv (fun s => kummerM a b (2 * κ * s)))
      (4 * κ ^ 2 * deriv (deriv (kummerM a b)) (2 * κ * r)) r := by
  have hfun : deriv (fun s => kummerM a b (2 * κ * s))
      = fun s => 2 * κ * deriv (kummerM a b) (2 * κ * s) :=
    funext (fun s => kummerComp_deriv a b κ hb s)
  rw [hfun]
  have h1 : HasDerivAt (deriv (kummerM a b)) (deriv (deriv (kummerM a b)) (2 * κ * r)) (2 * κ * r) :=
    (kummerM_hasDerivAt2 a b hb (2 * κ * r)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => 2 * κ * s) (2 * κ) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * κ)
  have hc : HasDerivAt (fun s => 2 * κ * deriv (kummerM a b) (2 * κ * s))
      (2 * κ * (deriv (deriv (kummerM a b)) (2 * κ * r) * (2 * κ))) r :=
    (h1.comp r h2).const_mul (2 * κ)
  convert hc using 1
  ring

private lemma kummerComp_deriv2 (a b κ : ℝ) (hb : 0 < b) (r : ℝ) :
    deriv^[2] (fun s => kummerM a b (2 * κ * s)) r
      = 4 * κ ^ 2 * deriv (deriv (kummerM a b)) (2 * κ * r) := by
  show deriv (deriv (fun s => kummerM a b (2 * κ * s))) r = _
  exact (kummerComp_hasDerivAt2 a b κ hb r).deriv

/-! ### Part A: `φ` solves the reduced radial ODE -/

theorem kummerRadial_solves (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) {r : ℝ} (hr : 0 < r) :
    deriv^[2] (kummerRadial ℓ κ) r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * kummerRadial ℓ κ r := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  set a := (ℓ : ℝ) + 1 - 1 / κ with ha_def
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  set w := fun s => kummerM a b (2 * κ * s) with hw_def
  have hw1 : ∀ s, 0 < s → HasDerivAt w (deriv w s) s := by
    intro s _
    rw [hw_def, kummerComp_deriv a b κ hb s]
    exact kummerComp_hasDerivAt a b κ hb s
  have hw2 : ∀ s, 0 < s → HasDerivAt (deriv w) (deriv^[2] w s) s := by
    intro s _
    rw [hw_def, kummerComp_deriv2 a b κ hb s]
    exact kummerComp_hasDerivAt2 a b κ hb s
  have hφ : kummerRadial ℓ κ = fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) * w s := by
    funext s; rw [kummerRadial, hw_def]
  rw [hφ]
  rw [laguerre_ansatz_reduced_iff ℓ κ w hw1 hw2 hr]
  rw [hw_def, kummerComp_deriv2 a b κ hb r, kummerComp_deriv a b κ hb r]
  have hdict : (2 : ℝ) - 2 * ((ℓ : ℝ) + 1) * κ = -2 * κ * a := by
    rw [ha_def]; field_simp; ring
  rw [hdict]
  linear_combination (2 * κ) * kummerM_ode a b hb (2 * κ * r)

/-! ### Differentiability / continuity of `M` and `φ` -/

private lemma kummerM_differentiable (a b : ℝ) (hb : 0 < b) : Differentiable ℝ (kummerM a b) :=
  fun z => (kummerM_hasDerivAt a b hb z).differentiableAt

private lemma kummerM_deriv_differentiable (a b : ℝ) (hb : 0 < b) :
    Differentiable ℝ (deriv (kummerM a b)) :=
  fun z => (kummerM_hasDerivAt2 a b hb z).differentiableAt

private lemma kummerM_continuous (a b : ℝ) (hb : 0 < b) : Continuous (kummerM a b) :=
  (kummerM_differentiable a b hb).continuous

private lemma kummerRadial_eq (ℓ : ℕ) (κ : ℝ) :
    kummerRadial ℓ κ = fun r => r ^ (ℓ + 1) * Real.exp (-κ * r) *
      kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r) := rfl

private lemma kummerRadial_factor (ℓ : ℕ) (κ : ℝ) (r : ℝ) :
    kummerRadial ℓ κ r = r ^ (ℓ + 1) *
      (Real.exp (-κ * r) * kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r)) := by
  rw [kummerRadial]; ring

private lemma kummerRadial_differentiable (ℓ : ℕ) (κ : ℝ) :
    Differentiable ℝ (kummerRadial ℓ κ) := by
  set a := (ℓ : ℝ) + 1 - 1 / κ
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  rw [kummerRadial_eq]
  have hM : Differentiable ℝ (fun r : ℝ => kummerM a b (2 * κ * r)) :=
    (kummerM_differentiable a b hb).comp (by fun_prop)
  exact (((differentiable_id.pow (ℓ + 1)).mul (Real.differentiable_exp.comp (by fun_prop))).mul hM)

private lemma kummerRadial_continuous (ℓ : ℕ) (κ : ℝ) : Continuous (kummerRadial ℓ κ) :=
  (kummerRadial_differentiable ℓ κ).continuous

/-- Closed form of `deriv φ`. -/
private lemma kummerRadial_deriv_eq (ℓ : ℕ) (κ : ℝ) :
    deriv (kummerRadial ℓ κ) = fun r =>
      ((ℓ : ℝ) + 1) * r ^ ℓ * Real.exp (-κ * r) *
          kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r)
      + r ^ (ℓ + 1) * (Real.exp (-κ * r) * (-κ)) *
          kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * r)
      + r ^ (ℓ + 1) * Real.exp (-κ * r) *
          (2 * κ * deriv (kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2)) (2 * κ * r)) := by
  have hb : (0 : ℝ) < 2 * (ℓ : ℝ) + 2 := by positivity
  funext r
  have hp : HasDerivAt (fun s : ℝ => s ^ (ℓ + 1)) (((ℓ : ℝ) + 1) * r ^ ℓ) r := by
    simpa using hasDerivAt_pow (ℓ + 1) r
  have he : HasDerivAt (fun s : ℝ => Real.exp (-κ * s)) (Real.exp (-κ * r) * (-κ)) r := by
    have hin : HasDerivAt (fun s : ℝ => -κ * s) (-κ) r := by
      simpa using (hasDerivAt_id r).const_mul (-κ)
    simpa using hin.exp
  have hwc : HasDerivAt
      (fun s => kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * s))
      (2 * κ * deriv (kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2)) (2 * κ * r)) r :=
    kummerComp_hasDerivAt ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) κ hb r
  have hF : HasDerivAt (fun s => s ^ (ℓ + 1) * Real.exp (-κ * s) *
      kummerM ((ℓ : ℝ) + 1 - 1 / κ) (2 * (ℓ : ℝ) + 2) (2 * κ * s)) _ r :=
    (hp.mul he).mul hwc
  rw [kummerRadial_eq, hF.deriv]
  simp only [Pi.mul_apply]
  ring

private lemma kummerRadial_deriv_differentiable (ℓ : ℕ) (κ : ℝ) :
    Differentiable ℝ (deriv (kummerRadial ℓ κ)) := by
  set a := (ℓ : ℝ) + 1 - 1 / κ
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  rw [kummerRadial_deriv_eq]
  have hM : Differentiable ℝ (fun r : ℝ => kummerM a b (2 * κ * r)) :=
    (kummerM_differentiable a b hb).comp (by fun_prop)
  have hM' : Differentiable ℝ (fun r : ℝ => deriv (kummerM a b) (2 * κ * r)) :=
    (kummerM_deriv_differentiable a b hb).comp (by fun_prop)
  fun_prop

/-! ### Part B: behaviour of `φ` near `0` and at `∞` -/

private lemma kummerRadial_zero (ℓ : ℕ) (κ : ℝ) : kummerRadial ℓ κ 0 = 0 := by
  rw [kummerRadial]; simp

private lemma kummerRadial_tendsto_zero (ℓ : ℕ) (κ : ℝ) :
    Filter.Tendsto (kummerRadial ℓ κ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h := ((kummerRadial_continuous ℓ κ).tendsto 0)
  rw [kummerRadial_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `1/2 r^{ℓ+1} ≤ φ(r) ≤ 2 r^{ℓ+1}` and `φ(r) > 0` for small `r > 0`. -/
private lemma kummerRadial_near_zero (ℓ : ℕ) (κ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r, 0 < r → r < δ →
      (1 / 2) * r ^ (ℓ + 1) ≤ kummerRadial ℓ κ r ∧
      kummerRadial ℓ κ r ≤ 2 * r ^ (ℓ + 1) ∧ 0 < kummerRadial ℓ κ r := by
  set a := (ℓ : ℝ) + 1 - 1 / κ
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  have ht : Filter.Tendsto (fun r => Real.exp (-κ * r) * kummerM a b (2 * κ * r)) (nhds 0)
      (nhds 1) := by
    have hc : Continuous (fun r => Real.exp (-κ * r) * kummerM a b (2 * κ * r)) :=
      (Real.continuous_exp.comp (by fun_prop)).mul ((kummerM_continuous a b hb).comp (by fun_prop))
    have := hc.tendsto 0
    simpa using this
  have key : ∀ᶠ r in nhds (0 : ℝ),
      1 / 2 < Real.exp (-κ * r) * kummerM a b (2 * κ * r) ∧
      Real.exp (-κ * r) * kummerM a b (2 * κ * r) < 2 := by
    filter_upwards [ht.eventually (Ioo_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)
      (by norm_num : (1 : ℝ) < 2))] with r hr using ⟨hr.1, hr.2⟩
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨δ, hδ, hball⟩ := key
  refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
  have hmem : dist r 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; exact hrδ
  obtain ⟨hlo, hhi⟩ := hball hmem
  have hpow : 0 < r ^ (ℓ + 1) := by positivity
  have hfac := kummerRadial_factor ℓ κ r
  rw [show ((ℓ : ℝ) + 1 - 1 / κ) = a from rfl, show (2 * (ℓ : ℝ) + 2) = b from rfl] at hfac
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]; nlinarith [hlo, hpow]
  · rw [hfac]; nlinarith [hhi, hpow]
  · rw [hfac]; nlinarith [hlo, hpow]

/-- `|φ(r)| ≥ C > 0` for all large `r`, when the Kummer series does not terminate. -/
private lemma kummerRadial_growth (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (ha : ∀ p : ℕ, (ℓ : ℝ) + 1 - 1 / κ ≠ -(p : ℝ)) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r, R ≤ r → C ≤ |kummerRadial ℓ κ r| := by
  set a := (ℓ : ℝ) + 1 - 1 / κ with ha_def
  set b := 2 * (ℓ : ℝ) + 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  obtain ⟨C, R₀, hC, hlb⟩ := kummerM_abs_exp_lower a b hb ha
  refine ⟨C, max 1 (R₀ / (2 * κ)), hC, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrR : R₀ / (2 * κ) ≤ r := le_trans (le_max_right _ _) hr
  have h2κ : 0 < 2 * κ := by positivity
  have hρ : R₀ ≤ 2 * κ * r := by
    rw [div_le_iff₀ h2κ] at hrR; linarith [hrR]
  have hMlb : C * Real.exp (2 * κ * r / 2) ≤ |kummerM a b (2 * κ * r)| := hlb _ hρ
  have hexp : Real.exp (2 * κ * r / 2) = Real.exp (κ * r) := by congr 1; ring
  rw [hexp] at hMlb
  have hfac := kummerRadial_factor ℓ κ r
  rw [show ((ℓ : ℝ) + 1 - 1 / κ) = a from rfl, show (2 * (ℓ : ℝ) + 2) = b from rfl] at hfac
  rw [hfac]
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < r ^ (ℓ + 1)),
    abs_of_pos (Real.exp_pos _)]
  have hpow1 : 1 ≤ r ^ (ℓ + 1) := one_le_pow₀ hr1
  have hexpn : 0 ≤ Real.exp (-κ * r) := (Real.exp_pos _).le
  have hkey : Real.exp (-κ * r) * (C * Real.exp (κ * r)) = C := by
    rw [show Real.exp (-κ * r) * (C * Real.exp (κ * r))
        = C * (Real.exp (-κ * r) * Real.exp (κ * r)) from by ring,
      ← Real.exp_add, show -κ * r + κ * r = 0 from by ring, Real.exp_zero, mul_one]
  have step1 : Real.exp (-κ * r) * (C * Real.exp (κ * r))
      ≤ Real.exp (-κ * r) * |kummerM a b (2 * κ * r)| :=
    mul_le_mul_of_nonneg_left hMlb hexpn
  have hMnn : 0 ≤ Real.exp (-κ * r) * |kummerM a b (2 * κ * r)| :=
    mul_nonneg hexpn (abs_nonneg _)
  calc C = Real.exp (-κ * r) * (C * Real.exp (κ * r)) := hkey.symm
    _ ≤ Real.exp (-κ * r) * |kummerM a b (2 * κ * r)| := step1
    _ ≤ r ^ (ℓ + 1) * (Real.exp (-κ * r) * |kummerM a b (2 * κ * r)|) := by
          nlinarith [hpow1, hMnn]

/-! ### Part C: the Wronskian `W = χ φ' − χ' φ` vanishes -/

/-- The Wronskian of `χ` (a solution of the reduced equation) and `φ = kummerRadial` has
zero derivative on `(0,∞)`. -/
private lemma wronskian_hasDerivAt_zero (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s) 0 r := by
  have hχd : HasDerivAt χ (deriv χ r) r := hχ1 r hr
  have hχd2 : HasDerivAt (deriv χ) (deriv^[2] χ r) r := hχ2 r hr
  have hφd : HasDerivAt (kummerRadial ℓ κ) (deriv (kummerRadial ℓ κ) r) r :=
    (kummerRadial_differentiable ℓ κ r).hasDerivAt
  have hφd2 : HasDerivAt (deriv (kummerRadial ℓ κ)) (deriv^[2] (kummerRadial ℓ κ) r) r :=
    (kummerRadial_deriv_differentiable ℓ κ r).hasDerivAt
  have h1 : HasDerivAt (fun s => χ s * deriv (kummerRadial ℓ κ) s)
      (deriv χ r * deriv (kummerRadial ℓ κ) r + χ r * deriv^[2] (kummerRadial ℓ κ) r) r :=
    hχd.mul hφd2
  have h2 : HasDerivAt (fun s => deriv χ s * kummerRadial ℓ κ s)
      (deriv^[2] χ r * kummerRadial ℓ κ r + deriv χ r * deriv (kummerRadial ℓ κ) r) r :=
    hχd2.mul hφd
  convert h1.sub h2 using 1
  rw [hode r hr, kummerRadial_solves ℓ κ hκ hr]
  ring

/-- The Wronskian is constant on `(0,∞)`. -/
private lemma wronskian_const (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    {r₀ s : ℝ} (hr₀ : 0 < r₀) (hs : 0 < s) :
    χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s
      = χ r₀ * deriv (kummerRadial ℓ κ) r₀ - deriv χ r₀ * kummerRadial ℓ κ r₀ := by
  set W : ℝ → ℝ := fun s => χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s
    with hWdef
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := W) (f' := fun _ => (0 : ℝ)) (s := Set.Ioi 0) (C := 0)
    (fun x hx => (wronskian_hasDerivAt_zero ℓ κ hκ χ hχ1 hχ2 hode hx).hasDerivWithinAt)
    (fun x _ => by simp) (convex_Ioi 0) hr₀ (Set.mem_Ioi.2 hs)
  simpa [hWdef, sub_eq_zero] using hb

/-- **Reduction-of-order lower bound.** `φ(r)·∫_r^d ds/φ(s)² ≥ 1/(8·2^{2ℓ+2})` for small `r`,
using only that `(1/2)r^{ℓ+1} ≤ φ ≤ 2 r^{ℓ+1}` near `0`. The integral is bounded below by its
restriction to `[r,2r]` (length × minimum), avoiding any explicit power integral. -/
private lemma reduction_order_lower (ℓ : ℕ) (κ : ℝ) {d : ℝ}
    (hbpos : ∀ s, 0 < s → s ≤ d → 0 < kummerRadial ℓ κ s)
    (hbub : ∀ s, 0 < s → s ≤ d → kummerRadial ℓ κ s ≤ 2 * s ^ (ℓ + 1))
    {r : ℝ} (hr : 0 < r) (h2r : 2 * r ≤ d) (hr1 : r ≤ 1)
    (hblb : (1 / 2) * r ^ (ℓ + 1) ≤ kummerRadial ℓ κ r) :
    1 / (8 * 2 ^ (2 * ℓ + 2)) ≤
      kummerRadial ℓ κ r * ∫ s in r..d, 1 / (kummerRadial ℓ κ s) ^ 2 := by
  have hrd : r ≤ d := le_trans (by linarith) h2r
  have hr2r : r ≤ 2 * r := by linarith
  set f := fun s => 1 / (kummerRadial ℓ κ s) ^ 2 with hf
  have hfnn : ∀ s, 0 ≤ f s := fun s => by rw [hf]; positivity
  have hcont : ContinuousOn f (Set.uIcc r d) := by
    rw [hf]
    apply ContinuousOn.div continuousOn_const ((kummerRadial_continuous ℓ κ).pow 2).continuousOn
    intro s hs
    rw [Set.uIcc_of_le hrd] at hs
    exact pow_ne_zero 2 (ne_of_gt (hbpos s (lt_of_lt_of_le hr hs.1) hs.2))
  have hsub1 : Set.uIcc r (2 * r) ⊆ Set.uIcc r d :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [Set.uIcc_of_le hrd]; exact ⟨hr2r, h2r⟩)
  have hsub2 : Set.uIcc (2 * r) d ⊆ Set.uIcc r d :=
    Set.uIcc_subset_uIcc (by rw [Set.uIcc_of_le hrd]; exact ⟨hr2r, h2r⟩) Set.right_mem_uIcc
  have hii_1 : IntervalIntegrable f volume r (2 * r) := (hcont.mono hsub1).intervalIntegrable
  have hii_2 : IntervalIntegrable f volume (2 * r) d := (hcont.mono hsub2).intervalIntegrable
  have hsplit : (∫ s in r..(2 * r), f s) + ∫ s in (2 * r)..d, f s = ∫ s in r..d, f s :=
    intervalIntegral.integral_add_adjacent_intervals hii_1 hii_2
  have htail : 0 ≤ ∫ s in (2 * r)..d, f s := intervalIntegral.integral_nonneg h2r (fun s _ => hfnn s)
  have hΦ1 : (∫ s in r..(2 * r), f s) ≤ ∫ s in r..d, f s := by rw [← hsplit]; linarith
  set c₁ := 1 / (4 * (2 * r) ^ (2 * ℓ + 2)) with hc₁
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  have hptwise : ∀ s ∈ Set.Icc r (2 * r), c₁ ≤ f s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr hs.1
    have hsd : s ≤ d := le_trans hs.2 h2r
    have hφs : kummerRadial ℓ κ s ≤ 2 * (2 * r) ^ (ℓ + 1) := by
      refine le_trans (hbub s hs0 hsd) ?_
      have hp : s ^ (ℓ + 1) ≤ (2 * r) ^ (ℓ + 1) := pow_le_pow_left₀ (le_of_lt hs0) hs.2 _
      linarith
    have hφspos : 0 < kummerRadial ℓ κ s := hbpos s hs0 hsd
    have hsq : (kummerRadial ℓ κ s) ^ 2 ≤ 4 * (2 * r) ^ (2 * ℓ + 2) := by
      have h1 : (kummerRadial ℓ κ s) ^ 2 ≤ (2 * (2 * r) ^ (ℓ + 1)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hφspos) hφs 2
      rwa [show (2 * (2 * r) ^ (ℓ + 1)) ^ 2 = 4 * (2 * r) ^ (2 * ℓ + 2) from by
        rw [mul_pow, ← pow_mul]; ring_nf] at h1
    rw [hf, hc₁]
    exact one_div_le_one_div_of_le (by positivity) hsq
  have hintc : (2 * r - r) * c₁ ≤ ∫ s in r..(2 * r), f s := by
    have hmono := intervalIntegral.integral_mono_on hr2r intervalIntegrable_const hii_1 hptwise
    rwa [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hΦlb : (2 * r - r) * c₁ ≤ ∫ s in r..d, f s := le_trans hintc hΦ1
  have hφrpos : 0 < kummerRadial ℓ κ r := hbpos r hr hrd
  have hpow_le : r ^ (2 * ℓ + 2) ≤ r ^ (ℓ + 2) := by
    have hsplit : r ^ (2 * ℓ + 2) = r ^ (ℓ + 2) * r ^ ℓ := by rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have hrℓ : r ^ ℓ ≤ 1 := pow_le_one₀ (le_of_lt hr) hr1
    nlinarith [pow_nonneg (le_of_lt hr) (ℓ + 2), hrℓ]
  calc 1 / (8 * 2 ^ (2 * ℓ + 2))
      ≤ (1 / 2 * r ^ (ℓ + 1)) * ((2 * r - r) * c₁) := by
        have hX : (1 / 2 * r ^ (ℓ + 1)) * ((2 * r - r) * c₁)
            = r ^ (ℓ + 2) / (8 * 2 ^ (2 * ℓ + 2) * r ^ (2 * ℓ + 2)) := by
          rw [hc₁, show (2 * r) ^ (2 * ℓ + 2) = 2 ^ (2 * ℓ + 2) * r ^ (2 * ℓ + 2) from by
            rw [mul_pow]]
          have hrne : r ≠ 0 := ne_of_gt hr
          field_simp
          ring
        rw [hX, le_div_iff₀ (by positivity)]
        rw [show (1 : ℝ) / (8 * 2 ^ (2 * ℓ + 2)) * (8 * 2 ^ (2 * ℓ + 2) * r ^ (2 * ℓ + 2))
          = r ^ (2 * ℓ + 2) from by field_simp]
        exact hpow_le
    _ ≤ kummerRadial ℓ κ r * ∫ s in r..d, f s :=
        mul_le_mul hblb hΦlb (le_of_lt (mul_pos (by linarith) hc₁pos)) (le_of_lt hφrpos)

/-- **Reduction-of-order FTC identity.** With `W₀` the (constant) Wronskian
`χ φ' − χ' φ`, integrating `(χ/φ)' = -W₀/φ²` gives
`χ(r) − φ(r)·(χ(d)/φ(d)) = W₀·(φ(r)·∫_r^d ds/φ²)`. -/
private lemma reduction_order_ftc (ℓ : ℕ) (κ : ℝ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    {d : ℝ} (W₀ : ℝ)
    (hW₀ : ∀ s, 0 < s →
      χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s = W₀)
    (hbpos : ∀ s, 0 < s → s ≤ d → 0 < kummerRadial ℓ κ s)
    {r : ℝ} (hr : 0 < r) (hrd : r < d) :
    χ r - kummerRadial ℓ κ r * (χ d / kummerRadial ℓ κ d)
      = W₀ * (kummerRadial ℓ κ r * ∫ s in r..d, 1 / (kummerRadial ℓ κ s) ^ 2) := by
  have hrd' : r ≤ d := le_of_lt hrd
  have hxpos : ∀ x ∈ Set.uIcc r d, 0 < x := by
    intro x hx; rw [Set.uIcc_of_le hrd'] at hx; exact lt_of_lt_of_le hr hx.1
  have hφpos : ∀ x ∈ Set.uIcc r d, 0 < kummerRadial ℓ κ x := by
    intro x hx
    have hx' := hx; rw [Set.uIcc_of_le hrd'] at hx'
    exact hbpos x (hxpos x hx) hx'.2
  have hφrne : kummerRadial ℓ κ r ≠ 0 := ne_of_gt (hbpos r hr hrd')
  have hφdne : kummerRadial ℓ κ d ≠ 0 := ne_of_gt (hbpos d (lt_trans hr hrd) le_rfl)
  set rawf := fun x => (deriv χ x * kummerRadial ℓ κ x - χ x * deriv (kummerRadial ℓ κ) x) /
    (kummerRadial ℓ κ x) ^ 2 with hrawf
  have hderiv : ∀ x ∈ Set.uIcc r d, HasDerivAt (fun s => χ s / kummerRadial ℓ κ s) (rawf x) x := by
    intro x hx
    exact (hχ1 x (hxpos x hx)).div ((kummerRadial_differentiable ℓ κ x).hasDerivAt)
      (ne_of_gt (hφpos x hx))
  have hint : IntervalIntegrable rawf volume r d := by
    rw [hrawf]
    have hχc : ContinuousOn χ (Set.uIcc r d) :=
      fun x hx => (hχ1 x (hxpos x hx)).continuousAt.continuousWithinAt
    have hdχc : ContinuousOn (deriv χ) (Set.uIcc r d) :=
      fun x hx => (hχ2 x (hxpos x hx)).continuousAt.continuousWithinAt
    have hφc : ContinuousOn (kummerRadial ℓ κ) (Set.uIcc r d) :=
      (kummerRadial_continuous ℓ κ).continuousOn
    have hdφc : ContinuousOn (deriv (kummerRadial ℓ κ)) (Set.uIcc r d) :=
      (kummerRadial_deriv_differentiable ℓ κ).continuous.continuousOn
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div ((hdχc.mul hφc).sub (hχc.mul hdφc))
      ((hφc.pow 2))
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (hφpos x hx))
  have hFTC : ∫ s in r..d, rawf s = χ d / kummerRadial ℓ κ d - χ r / kummerRadial ℓ κ r :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr : Set.EqOn rawf (fun s => -W₀ * (1 / (kummerRadial ℓ κ s) ^ 2)) (Set.uIcc r d) := by
    intro s hs
    have hnum : deriv χ s * kummerRadial ℓ κ s - χ s * deriv (kummerRadial ℓ κ) s = -W₀ := by
      have := hW₀ s (hxpos s hs); linarith
    rw [hrawf]
    simp only
    rw [hnum]; ring
  have hΦ : ∫ s in r..d, rawf s = -W₀ * ∫ s in r..d, 1 / (kummerRadial ℓ κ s) ^ 2 := by
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  rw [hΦ] at hFTC
  -- rearrange
  have key : χ r - kummerRadial ℓ κ r * (χ d / kummerRadial ℓ κ d)
      = kummerRadial ℓ κ r *
        (χ r / kummerRadial ℓ κ r - χ d / kummerRadial ℓ κ d) := by
    field_simp
  rw [key, show χ r / kummerRadial ℓ κ r - χ d / kummerRadial ℓ κ d
    = W₀ * ∫ s in r..d, 1 / (kummerRadial ℓ κ s) ^ 2 from by linarith [hFTC]]
  ring

/-- **The Wronskian vanishes.** A square-integrable-near-`0` solution `χ` with `χ → 0` at `0⁺`
has zero Wronskian with the regular solution `φ`: `χ φ' − χ' φ ≡ 0`. -/
private lemma wronskian_zero (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    (hχ0 : Filter.Tendsto χ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ s, 0 < s → χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s = 0 := by
  obtain ⟨δ, hδ, hbounds⟩ := kummerRadial_near_zero ℓ κ
  set δ' := δ / 2 with hδ'def
  have hδ'pos : 0 < δ' := by rw [hδ'def]; linarith
  have hδ'lt : δ' < δ := by rw [hδ'def]; linarith
  have hbpos : ∀ s, 0 < s → s ≤ δ' → 0 < kummerRadial ℓ κ s :=
    fun s hs0 hsd => (hbounds s hs0 (lt_of_le_of_lt hsd hδ'lt)).2.2
  have hbub : ∀ s, 0 < s → s ≤ δ' → kummerRadial ℓ κ s ≤ 2 * s ^ (ℓ + 1) :=
    fun s hs0 hsd => (hbounds s hs0 (lt_of_le_of_lt hsd hδ'lt)).2.1
  set W₀ := χ δ' * deriv (kummerRadial ℓ κ) δ' - deriv χ δ' * kummerRadial ℓ κ δ' with hW₀def
  have hWconst : ∀ s, 0 < s →
      χ s * deriv (kummerRadial ℓ κ) s - deriv χ s * kummerRadial ℓ κ s = W₀ :=
    fun s hs => wronskian_const ℓ κ hκ χ hχ1 hχ2 hode hδ'pos hs
  suffices hW₀ : W₀ = 0 by
    intro s hs; rw [hWconst s hs]; exact hW₀
  by_contra hW₀ne
  set ρ := min (δ / 4) 1 with hρdef
  have hρpos : 0 < ρ := lt_min (by linarith) one_pos
  have hAtend : Filter.Tendsto
      (fun r => χ r - kummerRadial ℓ κ r * (χ δ' / kummerRadial ℓ κ δ'))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h2 := (kummerRadial_tendsto_zero ℓ κ).mul_const (χ δ' / kummerRadial ℓ κ δ')
    simpa using hχ0.sub h2
  have hc0pos : (0 : ℝ) < 1 / (8 * 2 ^ (2 * ℓ + 2)) := by positivity
  have hWc0pos : 0 < |W₀| * (1 / (8 * 2 ^ (2 * ℓ + 2))) := mul_pos (abs_pos.2 hW₀ne) hc0pos
  have hev1 : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |W₀| * (1 / (8 * 2 ^ (2 * ℓ + 2)))
        ≤ |χ r - kummerRadial ℓ κ r * (χ δ' / kummerRadial ℓ κ δ')| := by
    have hmem : Set.Iio ρ ∈ nhds (0 : ℝ) := Iio_mem_nhds hρpos
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with r hr0 hrρ
    rw [Set.mem_Ioi] at hr0
    rw [Set.mem_Iio] at hrρ
    have hrδ4 : r < δ / 4 := lt_of_lt_of_le hrρ (min_le_left _ _)
    have hr_lt_δ' : r < δ' := by rw [hδ'def]; linarith
    have h2r : 2 * r ≤ δ' := by rw [hδ'def]; linarith
    have hr1 : r ≤ 1 := le_of_lt (lt_of_lt_of_le hrρ (min_le_right _ _))
    have hblb : (1 / 2) * r ^ (ℓ + 1) ≤ kummerRadial ℓ κ r :=
      (hbounds r hr0 (lt_trans hr_lt_δ' hδ'lt)).1
    have hA := reduction_order_ftc ℓ κ χ hχ1 hχ2 W₀ hWconst hbpos hr0 hr_lt_δ'
    have hlb := reduction_order_lower ℓ κ hbpos hbub hr0 h2r hr1 hblb
    have hPos : 0 ≤ kummerRadial ℓ κ r * ∫ s in r..δ', 1 / (kummerRadial ℓ κ s) ^ 2 :=
      le_trans (le_of_lt hc0pos) hlb
    rw [hA, abs_mul, abs_of_nonneg hPos]
    exact mul_le_mul_of_nonneg_left hlb (abs_nonneg W₀)
  have hev2 : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      |χ r - kummerRadial ℓ κ r * (χ δ' / kummerRadial ℓ κ δ')|
        < |W₀| * (1 / (8 * 2 ^ (2 * ℓ + 2))) := by
    filter_upwards [hAtend.eventually_mem (Metric.ball_mem_nhds 0 hWc0pos)] with r hr
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hr
    exact hr
  obtain ⟨r, hr1, hr2⟩ := (hev1.and hev2).exists
  linarith

/-! ### Part D: global identification `χ = c₀ φ` and the final contradiction -/

/-- **Forward identification.** If `χ − c₀ φ` and its derivative both vanish at `r₁ > 0`
(and `χ` solves the reduced equation), then `χ = c₀ φ` on `[r₁, ∞)`. This is linear ODE
uniqueness, via Grönwall on the first-order system `(u, u')`. -/
private lemma forward_identification (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    (c₀ : ℝ) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (h0 : χ r₁ - c₀ * kummerRadial ℓ κ r₁ = 0)
    (h0' : deriv χ r₁ - c₀ * deriv (kummerRadial ℓ κ) r₁ = 0) :
    ∀ r, r₁ ≤ r → χ r = c₀ * kummerRadial ℓ κ r := by
  intro r hr
  set V : ℝ → ℝ := fun x => (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 - 2 / x + κ ^ 2 with hVdef
  set u : ℝ → ℝ := fun s => χ s - c₀ * kummerRadial ℓ κ s with hudef
  set du : ℝ → ℝ := fun s => deriv χ s - c₀ * deriv (kummerRadial ℓ κ) s with hdudef
  set F : ℝ → ℝ × ℝ := fun t => (u t, du t) with hFdef
  set M : ℝ := (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r₁ ^ 2 + 2 / r₁ + κ ^ 2 with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  set K : ℝ := M + 1 with hKdef
  have hxpos : ∀ x ∈ Set.Icc r₁ r, 0 < x := fun x hx => lt_of_lt_of_le hr₁ hx.1
  -- continuity of F on [r₁, r]
  have hχcont : ContinuousOn χ (Set.Icc r₁ r) :=
    fun x hx => (hχ1 x (hxpos x hx)).continuousAt.continuousWithinAt
  have hdχcont : ContinuousOn (deriv χ) (Set.Icc r₁ r) :=
    fun x hx => (hχ2 x (hxpos x hx)).continuousAt.continuousWithinAt
  have hφcont : ContinuousOn (kummerRadial ℓ κ) (Set.Icc r₁ r) :=
    (kummerRadial_continuous ℓ κ).continuousOn
  have hdφcont : ContinuousOn (deriv (kummerRadial ℓ κ)) (Set.Icc r₁ r) :=
    (kummerRadial_deriv_differentiable ℓ κ).continuous.continuousOn
  have hcont : ContinuousOn F (Set.Icc r₁ r) :=
    (hχcont.sub (continuousOn_const.mul hφcont)).prodMk
      (hdχcont.sub (continuousOn_const.mul hdφcont))
  -- derivative of F
  have hderiv : ∀ x ∈ Set.Ico r₁ r, HasDerivWithinAt F (du x, V x * u x) (Set.Ici x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₁ hx.1
    have hud : HasDerivAt u (du x) x :=
      (hχ1 x hx0).sub ((kummerRadial_differentiable ℓ κ x).hasDerivAt.const_mul c₀)
    have hdud : HasDerivAt du (V x * u x) x := by
      have hb := (hχ2 x hx0).sub
        ((kummerRadial_deriv_differentiable ℓ κ x).hasDerivAt.const_mul c₀)
      convert hb using 1
      rw [show deriv (deriv (kummerRadial ℓ κ)) x = deriv^[2] (kummerRadial ℓ κ) x from rfl,
        hode x hx0, kummerRadial_solves ℓ κ hκ hx0]
      simp only [hVdef, hudef]
      ring
    exact (hud.prodMk hdud).hasDerivWithinAt
  -- initial condition
  have hinit : F r₁ = 0 := by
    simp only [hFdef, hudef, hdudef, Prod.mk_eq_zero]
    exact ⟨h0, h0'⟩
  -- the norm bound
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
      · linarith [h1, h2, hx2nn, hr1nn, h2xpos, h2r1pos, sq_nonneg κ]
      · linarith [h1, h2, hx2nn, hr1nn, h2xpos, h2r1pos, sq_nonneg κ]
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

/-- **Square-integrable bound states of the reduced radial operator are quantized.**

    If `χ` is a `C²` function on `(0,∞)`, square-integrable there, nonzero at some
    point, regular at the origin (`χ(r) → 0` as `r → 0⁺`, hypothesis `hχ0`), and
    solving the reduced radial equation
    `χ''(r) = (ℓ(ℓ+1)/r² − 2/r + κ²)·χ(r)` with decay rate `κ > 0`,
    then `1/κ` is an integer `m ≥ ℓ+1`, i.e. `κ = 1/m`.

    **Why `hχ0` (the Dirichlet boundary condition) is essential.** Without it the
    statement is *false for `ℓ = 0`*: there the operator `−d²/dr² − 2/r` is in the
    Weyl limit-circle case at `0` (inverse-square coefficient `ℓ(ℓ+1) = 0 < 3/4`),
    so the recessive-at-∞ ("irregular") Coulomb solution `W_{1/κ,1/2}(2κr)` is
    bounded (`→ const ≠ 0`) at the origin and `~ e^{−κr}` at infinity — hence
    globally `L²` for *every* `κ > 0`, including non-quantized `κ`. The condition
    `χ → 0` at `0⁺` excludes it (for `ℓ = 0` the regular solution `~ r → 0`, the
    irregular one `→ const ≠ 0`; for `ℓ ≥ 1` the irregular one `~ r^{−ℓ} → ∞`),
    and is satisfied by every genuine reduced eigenfunction
    `χ_{nℓ} = r·R_{nℓ} ~ r^{ℓ+1} → 0` (`radial_boundary_r_zero`).

    **Proof.** Argue by contradiction: if `κ ≠ 1/m` for every `m ≥ ℓ+1`, then the
    Kummer parameter `a = ℓ+1 − 1/κ` is never a non-positive integer, so the
    regular-at-`0` solution `φ = kummerRadial ℓ κ = r^{ℓ+1} e^{−κr} M(a, 2ℓ+2, 2κr)`
    (which solves the reduced equation, `kummerRadial_solves`, via
    `laguerre_ansatz_reduced_iff` and `Spectra.Kummer.kummerM_ode`) grows like
    `|φ(r)| ≳ r^{ℓ+1}` at infinity (`Spectra.Kummer.kummerM_abs_exp_lower`, packaged
    as `kummerRadial_growth`). The Wronskian `χ φ' − χ' φ` is constant on `(0,∞)`;
    the regularity `χ → 0` at `0⁺` forces it to vanish (`wronskian_zero`, a
    reduction-of-order estimate that bounds `∫ dr/φ²` below by integrating over
    `[r, 2r]`). Linear second-order ODE uniqueness — Grönwall on the first-order
    system `(u, u')` with `u = χ − c₀ φ`, `forward_identification` — then propagates
    `χ = c₀ φ` to all of `(0,∞)`, with `c₀ ≠ 0` since `χ` is nonzero somewhere. Thus
    `|χ(r)| = |c₀|·|φ(r)|` is bounded below by a positive constant at infinity, so
    `χ ∉ L²` (`not_radialL2_of_eventually_ge`), contradicting `hL2`. Hence `a` is a
    non-positive integer, i.e. `κ = 1/m` with `m ≥ ℓ+1`. -/
theorem reduced_radial_L2_quantized (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    (hχ0 : Filter.Tendsto χ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0))
    (hnz : ∃ r, 0 < r ∧ χ r ≠ 0) :
    ∃ m : ℕ, ℓ + 1 ≤ m ∧ κ = 1 / (m : ℝ) := by
  by_contra hcon
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  -- the Kummer parameter `a = ℓ+1−1/κ` does not terminate
  have ha : ∀ p : ℕ, (ℓ : ℝ) + 1 - 1 / κ ≠ -(p : ℝ) := by
    intro p hp
    refine hcon ⟨ℓ + 1 + p, by omega, ?_⟩
    have h1κ : 1 / κ = (ℓ : ℝ) + 1 + (p : ℝ) := by linarith
    have hcast : (((ℓ + 1 + p : ℕ)) : ℝ) = (ℓ : ℝ) + 1 + (p : ℝ) := by push_cast; ring
    rw [hcast, ← h1κ, one_div_one_div]
  -- the Wronskian vanishes
  have hW := wronskian_zero ℓ κ hκ χ hχ1 hχ2 hode hχ0
  -- choose a base point `r₁` (small, below the nonzero point of `χ`)
  obtain ⟨δ, hδ, hbounds⟩ := kummerRadial_near_zero ℓ κ
  obtain ⟨rs, hrs_pos, hrs_ne⟩ := hnz
  set r₁ := min (δ / 2) rs with hr₁def
  have hr₁pos : 0 < r₁ := lt_min (by linarith) hrs_pos
  have hr₁δ : r₁ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hr₁rs : r₁ ≤ rs := min_le_right _ _
  have hφr₁pos : 0 < kummerRadial ℓ κ r₁ := (hbounds r₁ hr₁pos hr₁δ).2.2
  have hφr₁ne : kummerRadial ℓ κ r₁ ≠ 0 := ne_of_gt hφr₁pos
  set c₀ := χ r₁ / kummerRadial ℓ κ r₁ with hc₀def
  -- the two initial conditions for `u = χ − c₀ φ`
  have h0 : χ r₁ - c₀ * kummerRadial ℓ κ r₁ = 0 := by
    rw [hc₀def, div_mul_cancel₀ _ hφr₁ne, sub_self]
  have h0' : deriv χ r₁ - c₀ * deriv (kummerRadial ℓ κ) r₁ = 0 := by
    have hWr := hW r₁ hr₁pos
    rw [hc₀def]; field_simp; linarith [hWr]
  -- global identification `χ = c₀ φ` on `[r₁, ∞)`
  have hident := forward_identification ℓ κ hκ χ hχ1 hχ2 hode c₀ hr₁pos h0 h0'
  -- `c₀ ≠ 0` (else `χ` would vanish at the nonzero point)
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    apply hrs_ne
    rw [hident rs hr₁rs, h, zero_mul]
  -- exponential growth of `φ`, transported to `χ`, breaks square-integrability
  obtain ⟨C, R, hC, hgrow⟩ := kummerRadial_growth ℓ κ hκ ha
  have hlb : ∀ r, max r₁ R ≤ r → |c₀| * C ≤ |χ r| := by
    intro r hr
    have hr_r₁ : r₁ ≤ r := le_trans (le_max_left _ _) hr
    have hr_R : R ≤ r := le_trans (le_max_right _ _) hr
    rw [hident r hr_r₁, abs_mul]
    exact mul_le_mul_of_nonneg_left (hgrow r hr_R) (abs_nonneg c₀)
  exact not_radialL2_of_eventually_ge χ (mul_pos (abs_pos.2 hc₀ne) hC) hlb hL2

/-- **Consistency of the analytic core on the known eigenfunctions.**

    The reduced hydrogen eigenfunction `χ_{mℓ} = r·R_{mℓ}` (for `m ≥ ℓ+1`) solves
    the reduced radial equation `χ'' = (ℓ(ℓ+1)/r² − 2/r + κ²)·χ` with decay rate
    `κ = 1/m`. Combined with `radial_wavefunction_L2` (square-integrability) and
    `radial_wavefunction_norm` (nonvanishing), this exhibits `χ_{mℓ}` as a witness
    satisfying *every* hypothesis of `reduced_radial_L2_quantized`, with the
    expected conclusion `κ = 1/m`. It confirms that the reduced equation
    (`reduced_ode`) and `reduced_radial_L2_quantized`'s hypotheses are correctly stated
    and non-vacuous (a mis-stated reduced ODE would fail to compile here). -/
theorem reduced_eigenfunction_solves (m ℓ : ℕ) (hm : ℓ + 1 ≤ m) {r : ℝ} (hr : 0 < r) :
    deriv^[2] (fun s => s * hydrogenRadialWavefunction m ℓ hm s) r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (m : ℝ)) ^ 2)
        * (r * hydrogenRadialWavefunction m ℓ hm r) := by
  have hψ1 : ∀ s, 0 < s →
      HasDerivAt (hydrogenRadialWavefunction m ℓ hm)
        (deriv (hydrogenRadialWavefunction m ℓ hm) s) s :=
    fun s _ => (differentiable_hydrogenRadial m ℓ hm s).hasDerivAt
  have hψ2 : ∀ s, 0 < s →
      HasDerivAt (deriv (hydrogenRadialWavefunction m ℓ hm))
        (deriv^[2] (hydrogenRadialWavefunction m ℓ hm) s) s :=
    fun s _ => (differentiable_deriv_hydrogenRadial m ℓ hm s).hasDerivAt
  have heq : ∀ s, 0 < s → radialHamiltonian ℓ (hydrogenRadialWavefunction m ℓ hm) s
      = hydrogenEigenvalue m (by omega) * hydrogenRadialWavefunction m ℓ hm s :=
    fun s hs => radial_eigenvalue_eq m ℓ hm s hs
  have h := reduced_ode ℓ (hydrogenEigenvalue m (by omega))
    (hydrogenRadialWavefunction m ℓ hm) hψ1 hψ2 heq hr
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hE : -2 * hydrogenEigenvalue m (by omega) = (1 / (m : ℝ)) ^ 2 := by
    rw [hydrogenEigenvalue]; field_simp
  rw [h, ← hE]; ring

/-! ### Non-existence of `L²` solutions at `E ≥ 0` (continuous spectrum)

Elementary energy/Grönwall machinery for `reduced_radial_continuum`: the potential
`W = ℓ(ℓ+1)/r² − 2/r − 2E` is eventually negative and increasing, the energy
`χ'² − Wχ²` controls the solution, and an `L²` solution is forced to vanish. -/

/-- The reduced-radial potential at energy `E`: `W(r) = ℓ(ℓ+1)/r² − 2/r − 2E`. -/
private noncomputable def contW (ℓ : ℕ) (E : ℝ) : ℝ → ℝ :=
  fun r => (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E

private lemma contW_hasDerivAt (ℓ : ℕ) (E : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (contW ℓ E)
      (-2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 3 + 2 / r ^ 2) r := by
  have hr2 : (r : ℝ) ^ 2 ≠ 0 := by positivity
  have hrne : r ≠ 0 := ne_of_gt hr
  have h1 : HasDerivAt (fun s : ℝ => (ℓ : ℝ) * ((ℓ : ℝ) + 1) / s ^ 2)
      (((0 : ℝ) * r ^ 2 - (ℓ : ℝ) * ((ℓ : ℝ) + 1) * (2 * r ^ (2 - 1))) / (r ^ 2) ^ 2) r :=
    (hasDerivAt_const r ((ℓ : ℝ) * ((ℓ : ℝ) + 1))).div (hasDerivAt_pow 2 r) hr2
  have h2 : HasDerivAt (fun s : ℝ => 2 / s)
      (((0 : ℝ) * r - 2 * 1) / r ^ 2) r :=
    (hasDerivAt_const r (2 : ℝ)).div (hasDerivAt_id r) hrne
  have h3 : HasDerivAt (fun _ : ℝ => 2 * E) 0 r := hasDerivAt_const r _
  have hsum := (h1.sub h2).sub h3
  convert hsum using 1
  field_simp
  ring

/-- Threshold facts: for `r ≥ ℓ(ℓ+1)+1` (and `E ≥ 0`) the potential is negative with
`−W ≥ 1/r` and increasing (`W' ≥ 0`). -/
private lemma contW_thresh (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) {r : ℝ}
    (hr : (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 ≤ r) :
    0 < r ∧ 1 / r ≤ -contW ℓ E r ∧ contW ℓ E r < 0 ∧
      0 ≤ -2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 3 + 2 / r ^ 2 := by
  have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) := by positivity
  have hr0 : 0 < r := by nlinarith
  have hrge : (ℓ : ℝ) * ((ℓ : ℝ) + 1) < r := by nlinarith
  -- ℓ(ℓ+1)/r² ≤ 1/r  (since ℓ(ℓ+1) < r)
  have hkey : (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 ≤ 1 / r := by
    rw [← sub_nonneg, show (1 : ℝ) / r - (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2
      = (r - (ℓ : ℝ) * ((ℓ : ℝ) + 1)) / r ^ 2 from by field_simp]
    apply div_nonneg _ (by positivity)
    linarith [hrge]
  have hW : -contW ℓ E r = 2 / r + 2 * E - (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 := by
    simp only [contW]; ring
  have h2E : (0 : ℝ) ≤ 2 * E := by linarith
  have e1 : (2 : ℝ) / r = 2 * (1 / r) := by ring
  have h1r : (0 : ℝ) < 1 / r := by positivity
  refine ⟨hr0, ?_, ?_, ?_⟩
  · rw [hW]; linarith [hkey, h2E, e1, h1r]
  · rw [show contW ℓ E r = -(-contW ℓ E r) from by ring, hW]; linarith [hkey, h2E, e1, h1r]
  · -- W' = 2/r² − 2ℓ(ℓ+1)/r³ ≥ 0
    have h3 : (0 : ℝ) < r ^ 3 := by positivity
    rw [show -2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 3 + 2 / r ^ 2
        = (2 * (r - (ℓ : ℝ) * ((ℓ : ℝ) + 1))) / r ^ 3 from by field_simp; ring]
    apply div_nonneg _ (le_of_lt h3)
    nlinarith [hrge]

/-- **Energy differential inequality.** With `G = χ'² − Wχ²`, on `[r₀,∞)` (`r₀ ≥ ℓ(ℓ+1)+1`)
`G` is decreasing and `G/(−W)` is increasing (`G'(−W) + GW' = W'χ'² ≥ 0`), giving the
cross-multiplied lower bound `G(r₀)·(−W r) ≤ G(r)·(−W r₀)`. -/
private lemma energy_diff_ineq (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r)
    {r₀ : ℝ} (hr₀R : (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 ≤ r₀) :
    (∀ r, r₀ ≤ r → (deriv χ r) ^ 2 - contW ℓ E r * (χ r) ^ 2
        ≤ (deriv χ r₀) ^ 2 - contW ℓ E r₀ * (χ r₀) ^ 2)
    ∧ (∀ r, r₀ ≤ r →
        ((deriv χ r₀) ^ 2 - contW ℓ E r₀ * (χ r₀) ^ 2) * (-contW ℓ E r)
          ≤ ((deriv χ r) ^ 2 - contW ℓ E r * (χ r) ^ 2) * (-contW ℓ E r₀)) := by
  have hr₀pos : 0 < r₀ := (contW_thresh ℓ E hE hr₀R).1
  set G : ℝ → ℝ := fun r => (deriv χ r) ^ 2 - contW ℓ E r * (χ r) ^ 2 with hGdef
  set Wd : ℝ → ℝ := fun x => -2 * (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 3 + 2 / x ^ 2 with hWddef
  have hpos : ∀ x, r₀ ≤ x → 0 < x := fun x hx => lt_of_lt_of_le hr₀pos hx
  have hWdnn : ∀ x, r₀ ≤ x → 0 ≤ Wd x := fun x hx => (contW_thresh ℓ E hE (le_trans hr₀R hx)).2.2.2
  have hWneg : ∀ x, r₀ ≤ x → contW ℓ E x < 0 :=
    fun x hx => (contW_thresh ℓ E hE (le_trans hr₀R hx)).2.2.1
  have hGderiv : ∀ x, 0 < x → HasDerivAt G (-(Wd x) * (χ x) ^ 2) x := by
    intro x hx
    have h1 : HasDerivAt (fun s => deriv χ s ^ 2) (2 * deriv χ x * deriv^[2] χ x) x := by
      have h := (hχ2 x hx).mul (hχ2 x hx)
      rw [show (fun s => deriv χ s ^ 2) = (fun s => deriv χ s * deriv χ s) from by
        funext s; rw [pow_two]]
      convert h using 1; ring
    have hp : HasDerivAt (fun s => χ s ^ 2) (2 * χ x * deriv χ x) x := by
      have h := (hχ1 x hx).mul (hχ1 x hx)
      rw [show (fun s => χ s ^ 2) = (fun s => χ s * χ s) from by funext s; rw [pow_two]]
      convert h using 1; ring
    have h2 : HasDerivAt (fun s => contW ℓ E s * (χ s) ^ 2)
        (Wd x * (χ x) ^ 2 + contW ℓ E x * (2 * χ x * deriv χ x)) x :=
      (contW_hasDerivAt ℓ E hx).mul hp
    have hG := h1.sub h2
    convert hG using 1
    rw [hode x hx, show contW ℓ E x = (ℓ : ℝ) * ((ℓ : ℝ) + 1) / x ^ 2 - 2 / x - 2 * E from rfl]
    ring
  have hWc : ContinuousOn (contW ℓ E) (Set.Ici r₀) :=
    fun x hx => (contW_hasDerivAt ℓ E (hpos x hx)).continuousAt.continuousWithinAt
  have hχc : ContinuousOn χ (Set.Ici r₀) :=
    fun x hx => (hχ1 x (hpos x hx)).continuousAt.continuousWithinAt
  have hdχc : ContinuousOn (deriv χ) (Set.Ici r₀) :=
    fun x hx => (hχ2 x (hpos x hx)).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (Set.Ici r₀) := (hdχc.pow 2).sub (hWc.mul (hχc.pow 2))
  have hGdiff : DifferentiableOn ℝ G (interior (Set.Ici r₀)) := by
    rw [interior_Ici]
    exact fun x hx => (hGderiv x (lt_trans hr₀pos hx)).differentiableAt.differentiableWithinAt
  have hGdec : AntitoneOn G (Set.Ici r₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici r₀) hGc hGdiff
    intro x hx
    rw [interior_Ici] at hx
    rw [(hGderiv x (lt_trans hr₀pos hx)).deriv]
    nlinarith [sq_nonneg (χ x), hWdnn x (le_of_lt hx)]
  set H : ℝ → ℝ := fun s => G s / (-contW ℓ E s) with hHdef
  have hDne : ∀ x, r₀ ≤ x → -contW ℓ E x ≠ 0 := fun x hx => by have := hWneg x hx; linarith
  have hHc : ContinuousOn H (Set.Ici r₀) := hGc.div hWc.neg (fun x hx => hDne x hx)
  have hHderiv : ∀ x, r₀ ≤ x → HasDerivAt H
      ((-(Wd x) * (χ x) ^ 2 * (-contW ℓ E x) - G x * (-(Wd x))) / (-contW ℓ E x) ^ 2) x :=
    fun x hx => (hGderiv x (hpos x hx)).div ((contW_hasDerivAt ℓ E (hpos x hx)).neg) (hDne x hx)
  have hHdiff : DifferentiableOn ℝ H (interior (Set.Ici r₀)) := by
    rw [interior_Ici]
    exact fun x hx => (hHderiv x (le_of_lt hx)).differentiableAt.differentiableWithinAt
  have hHinc : MonotoneOn H (Set.Ici r₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici r₀) hHc hHdiff
    intro x hx
    rw [interior_Ici] at hx
    rw [(hHderiv x (le_of_lt hx)).deriv]
    apply div_nonneg _ (sq_nonneg _)
    rw [show -(Wd x) * (χ x) ^ 2 * (-contW ℓ E x) - G x * (-(Wd x)) = Wd x * (deriv χ x) ^ 2 from by
      rw [hGdef]; ring]
    exact mul_nonneg (hWdnn x (le_of_lt hx)) (sq_nonneg _)
  refine ⟨fun r hr => hGdec Set.self_mem_Ici (Set.mem_Ici.2 hr) hr, fun r hr => ?_⟩
  have hHle : H r₀ ≤ H r := hHinc Set.self_mem_Ici (Set.mem_Ici.2 hr) hr
  simp only [hHdef] at hHle
  have hD0 : 0 < -contW ℓ E r₀ := by have := hWneg r₀ (le_refl r₀); linarith
  have hDr : 0 < -contW ℓ E r := by have := hWneg r hr; linarith
  have hD0ne : (-contW ℓ E r₀) ≠ 0 := hD0.ne'
  have hDrne : (-contW ℓ E r) ≠ 0 := hDr.ne'
  have hmul := mul_le_mul_of_nonneg_right hHle (le_of_lt (mul_pos hD0 hDr))
  have key0 : G r₀ / (-contW ℓ E r₀) * (-contW ℓ E r₀ * -contW ℓ E r) = G r₀ * -contW ℓ E r := by
    rw [← mul_assoc, div_mul_cancel₀ _ hD0ne]
  have key1 : G r / (-contW ℓ E r) * (-contW ℓ E r₀ * -contW ℓ E r) = G r * -contW ℓ E r₀ := by
    rw [mul_comm (-contW ℓ E r₀) (-contW ℓ E r), ← mul_assoc, div_mul_cancel₀ _ hDrne]
  rw [key0, key1] at hmul
  exact hmul

/-- A function that is `L²` on `(a,∞)` and Lipschitz there tends to `0` at `+∞`.
Small-tail argument: if `|f r₀| ≥ ε` then `|f| ≥ ε/2` on `[r₀, r₀+δ]`, contributing
`(ε/2)²δ` to the integral — but the tail past a large `T₁` is smaller. -/
private lemma l2_tendsto_zero {f : ℝ → ℝ} {a B : ℝ} (hB : 0 ≤ B)
    (hlip : ∀ x y, a ≤ x → a ≤ y → |f x - f y| ≤ B * |x - y|)
    (hint : IntegrableOn (fun r => f r ^ 2) (Set.Ioi a)) :
    Filter.Tendsto f Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hBp : (0 : ℝ) < B + 1 := by linarith
  set δ := ε / (2 * (B + 1)) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδeq : ε = 2 * (B * δ) + 2 * δ := by rw [hδdef]; field_simp
  have htail : Filter.Tendsto (fun T => ∫ x in Set.Ioi T, f x ^ 2) Filter.atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero (f := fun r => f r ^ 2) (b := id) tendsto_id
  have hcpos : (0 : ℝ) < (ε / 2) ^ 2 * δ := by positivity
  obtain ⟨T₁, hT₁tail, hT₁a⟩ :=
    ((htail.eventually (gt_mem_nhds hcpos)).and (eventually_ge_atTop a)).exists
  refine ⟨T₁ + 1, fun r hr => ?_⟩
  rw [Real.dist_eq, sub_zero]
  by_contra hcon
  have hcon' : ε ≤ |f r| := not_lt.1 hcon
  have hrT₁ : T₁ < r := by linarith
  have hra : a ≤ r := le_trans hT₁a (by linarith)
  have hBδ : B * δ ≤ ε / 2 := by linarith [hδeq, hδpos]
  have hlb_pt : ∀ s ∈ Set.Ioc r (r + δ), (ε / 2) ^ 2 ≤ f s ^ 2 := by
    intro s hs
    have hsa : a ≤ s := le_trans hra (le_of_lt hs.1)
    have hsr : |r - s| ≤ δ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]; linarith [hs.2]
    have h2 : |f r - f s| ≤ B * δ :=
      le_trans (hlip r s hra hsa) (le_trans (mul_le_mul_of_nonneg_left hsr hB) (le_refl _))
    have h1 : |f r| - |f s| ≤ |f r - f s| := abs_sub_abs_le_abs_sub (f r) (f s)
    have hfs : ε / 2 ≤ |f s| := by linarith [h1, h2, hBδ, hcon']
    have : (ε / 2) ^ 2 ≤ |f s| ^ 2 := pow_le_pow_left₀ (by positivity) hfs 2
    rwa [sq_abs] at this
  have hintIoc : IntegrableOn (fun r => f r ^ 2) (Set.Ioc r (r + δ)) :=
    hint.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hra))
  have hlb : (ε / 2) ^ 2 * δ ≤ ∫ x in Set.Ioc r (r + δ), f x ^ 2 := by
    have hconst : ∫ _x in Set.Ioc r (r + δ), ((ε / 2) ^ 2 : ℝ) = (ε / 2) ^ 2 * δ := by
      rw [setIntegral_const, volume_real_Ioc_of_le (by linarith : r ≤ r + δ), smul_eq_mul]; ring
    have hci : IntegrableOn (fun _x : ℝ => ((ε / 2) ^ 2 : ℝ)) (Set.Ioc r (r + δ)) :=
      integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    rw [← hconst]
    exact setIntegral_mono_on hci hintIoc measurableSet_Ioc hlb_pt
  have hintIoiT : IntegrableOn (fun r => f r ^ 2) (Set.Ioi T₁) :=
    hint.mono_set (Set.Ioi_subset_Ioi hT₁a)
  have hub : (∫ x in Set.Ioc r (r + δ), f x ^ 2) ≤ ∫ x in Set.Ioi T₁, f x ^ 2 := by
    apply setIntegral_mono_set hintIoiT (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    exact (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hrT₁.le)).eventuallyLE
  linarith [hlb, hub, hT₁tail]

/-- **Forward uniqueness** for `u'' = V u` with zero Cauchy data at the left endpoint:
Grönwall on the system `(u, u')`, needing only the norm bound `‖(u', Vu)‖ ≤ (M+1)‖(u,u')‖`. -/
private lemma forward_zero {u du V : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hu : ∀ x ∈ Set.Icc a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Set.Icc a b, HasDerivAt du (V x * u x) x)
    (hVc : ContinuousOn V (Set.Icc a b))
    (hu0 : u a = 0) (hdu0 : du a = 0) :
    ∀ x ∈ Set.Icc a b, u x = 0 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hVc
  set F : ℝ → ℝ × ℝ := fun t => (u t, du t) with hFdef
  have huc : ContinuousOn u (Set.Icc a b) :=
    fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hduc : ContinuousOn du (Set.Icc a b) :=
    fun x hx => (hdu x hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn F (Set.Icc a b) := huc.prodMk hduc
  have hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt F (du x, V x * u x) (Set.Ici x) x := by
    intro x hx
    have hxab : x ∈ Set.Icc a b := ⟨hx.1, le_of_lt hx.2⟩
    exact ((hu x hxab).prodMk (hdu x hxab)).hasDerivWithinAt
  have hinit : F a = 0 := by rw [hFdef]; simp only [Prod.mk_eq_zero]; exact ⟨hu0, hdu0⟩
  have hbound : ∀ x ∈ Set.Ico a b, ‖(du x, V x * u x)‖ ≤ (M + 1) * ‖F x‖ := by
    intro x hx
    have hxab : x ∈ Set.Icc a b := ⟨hx.1, le_of_lt hx.2⟩
    rw [Prod.norm_def, hFdef, Prod.norm_def]
    simp only [Real.norm_eq_abs]
    have hMx : |V x| ≤ M := by have := hM x hxab; rwa [Real.norm_eq_abs] at this
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) hMx
    have hmax_nn : 0 ≤ max |u x| |du x| := le_trans (abs_nonneg _) (le_max_left _ _)
    apply max_le
    · calc |du x| ≤ max |u x| |du x| := le_max_right _ _
        _ ≤ (M + 1) * max |u x| |du x| := by nlinarith [hmax_nn, hMnn]
    · rw [abs_mul]
      calc |V x| * |u x| ≤ M * |u x| := mul_le_mul_of_nonneg_right hMx (abs_nonneg _)
        _ ≤ M * max |u x| |du x| := mul_le_mul_of_nonneg_left (le_max_left _ _) hMnn
        _ ≤ (M + 1) * max |u x| |du x| := by nlinarith [hmax_nn]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hcont hderiv hinit hbound
  intro x hx
  have h1 := congrArg Prod.fst (hzero x hx)
  simpa [hFdef] using h1

/-- Two-sided uniqueness: a `C²` solution of the reduced equation with zero Cauchy data at
`r₁ > 0` vanishes on all of `(0,∞)` (forward via `forward_zero`, backward via reflection). -/
private lemma cont_cauchy_zero (ℓ : ℕ) (E : ℝ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r)
    {r₁ : ℝ} (hr₁ : 0 < r₁) (h0 : χ r₁ = 0) (h0' : deriv χ r₁ = 0) :
    ∀ r, 0 < r → χ r = 0 := by
  have hodeW : ∀ x, 0 < x → contW ℓ E x * χ x = deriv^[2] χ x := fun x hx => by
    rw [hode x hx]; simp only [contW]
  have hlin : ∀ x : ℝ, HasDerivAt (fun t => 2 * r₁ - t) (-1 : ℝ) x :=
    fun x => (hasDerivAt_id x).const_sub (2 * r₁)
  have hfwd : ∀ r, r₁ ≤ r → χ r = 0 := by
    intro r hrr
    have hVc : ContinuousOn (contW ℓ E) (Set.Icc r₁ r) :=
      fun x hx => (contW_hasDerivAt ℓ E (lt_of_lt_of_le hr₁ hx.1)).continuousAt.continuousWithinAt
    refine forward_zero hrr (fun x hx => hχ1 x (lt_of_lt_of_le hr₁ hx.1)) ?_ hVc h0 h0' r
      (Set.right_mem_Icc.2 hrr)
    intro x hx
    rw [hodeW x (lt_of_lt_of_le hr₁ hx.1)]
    exact hχ2 x (lt_of_lt_of_le hr₁ hx.1)
  have hbwd : ∀ r, 0 < r → r ≤ r₁ → χ r = 0 := by
    intro r hrpos hrr₁
    rcases eq_or_lt_of_le hrr₁ with heq | hlt
    · rw [heq]; exact h0
    set b := 2 * r₁ - r with hbdef
    have hr₁b : r₁ ≤ b := by rw [hbdef]; linarith
    have hpos2 : ∀ x ∈ Set.Icc r₁ b, 0 < 2 * r₁ - x := by
      intro x hx; have hxb := hx.2; rw [hbdef] at hxb; linarith
    have hu : ∀ x ∈ Set.Icc r₁ b, HasDerivAt (fun t => χ (2 * r₁ - t)) (-deriv χ (2 * r₁ - x)) x := by
      intro x hx
      have h := (hχ1 (2 * r₁ - x) (hpos2 x hx)).comp x (hlin x)
      convert h using 1; ring
    have hdu : ∀ x ∈ Set.Icc r₁ b, HasDerivAt (fun t => -deriv χ (2 * r₁ - t))
        (contW ℓ E (2 * r₁ - x) * χ (2 * r₁ - x)) x := by
      intro x hx
      rw [hodeW (2 * r₁ - x) (hpos2 x hx)]
      have h := ((hχ2 (2 * r₁ - x) (hpos2 x hx)).comp x (hlin x)).neg
      convert h using 1; ring
    have hVc : ContinuousOn (fun t => contW ℓ E (2 * r₁ - t)) (Set.Icc r₁ b) :=
      fun x hx => (contW_hasDerivAt ℓ E (hpos2 x hx)).continuousAt.comp_continuousWithinAt
        ((continuous_const.sub continuous_id).continuousWithinAt)
    have hu0 : (fun t => χ (2 * r₁ - t)) r₁ = 0 := by
      show χ (2 * r₁ - r₁) = 0; rw [show 2 * r₁ - r₁ = r₁ from by ring]; exact h0
    have hdu0 : (fun t => -deriv χ (2 * r₁ - t)) r₁ = 0 := by
      show -deriv χ (2 * r₁ - r₁) = 0; rw [show 2 * r₁ - r₁ = r₁ from by ring, h0']; ring
    have hfz := forward_zero hr₁b hu hdu hVc hu0 hdu0 b (Set.right_mem_Icc.2 hr₁b)
    have hfz' : χ (2 * r₁ - b) = 0 := hfz
    rwa [show 2 * r₁ - b = r from by rw [hbdef]; ring] at hfz'
  intro r hr
  rcases le_total r r₁ with h | h
  · exact hbwd r hr h
  · exact hfwd r h

/-- **For `E ≥ 0`, every `C²` square-integrable solution of the reduced radial equation
    vanishes** (the continuous spectrum carries no bound states).

    Any `χ` solving `χ''(r) = (ℓ(ℓ+1)/r² − 2/r − 2E)·χ(r)` on `(0,∞)` and square-integrable
    there is identically `0`.

    **Proof.** For `r ≥ ℓ(ℓ+1)+1` the potential `W = ℓ(ℓ+1)/r² − 2/r − 2E` is negative,
    increasing, with `−W ≥ 1/r`. The energy `G = χ'² − Wχ²` is decreasing (`G' = −W'χ²`) and
    `G/(−W)` is increasing (`(G/(−W))' = W'χ'²/W² ≥ 0`), so `G ≥ K·(−W)` with
    `K = G(r₀)/(−W(r₀)) > 0` whenever `χ(r₀) ≠ 0` (`energy_diff_ineq`). Then `χ'` is bounded,
    so the `L²` function `χ` is Lipschitz and tends to `0` (`l2_tendsto_zero`); hence
    `(χχ')' = χ'² − (−W)χ² ≥ (K/2)·(−W) ≥ (K/2)/r` eventually, forcing `χχ' → +∞` by
    log-divergence — contradicting `χχ' → 0` (`χ → 0`, `χ'` bounded). So `χ ≡ 0` on
    `[ℓ(ℓ+1)+1, ∞)`, and Cauchy-data uniqueness (`cont_cauchy_zero`, Grönwall forward +
    reflection backward) extends this to all of `(0,∞)`. -/
theorem reduced_radial_continuum (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r)
    (hL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0)) :
    ∀ r, 0 < r → χ r = 0 := by
  have hodeW : ∀ x, 0 < x → contW ℓ E x * χ x = deriv^[2] χ x := fun x hx => by
    rw [hode x hx]; simp only [contW]
  have hRpos : (0 : ℝ) < (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 := by positivity
  -- Step 1: χ ≡ 0 on [R, ∞)
  have hRzero : ∀ r, (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 ≤ r → χ r = 0 := by
    by_contra hcon
    rw [not_forall] at hcon
    obtain ⟨r₀, hr₀⟩ := hcon
    rw [Classical.not_imp] at hr₀
    obtain ⟨hr₀R, hr₀ne⟩ := hr₀
    have hr₀pos : 0 < r₀ := lt_of_lt_of_le hRpos hr₀R
    obtain ⟨hGdec, hGratio⟩ := energy_diff_ineq ℓ E hE χ hχ1 hχ2 hode hr₀R
    set G0 := (deriv χ r₀) ^ 2 - contW ℓ E r₀ * (χ r₀) ^ 2 with hG0def
    have hWr₀neg : contW ℓ E r₀ < 0 := (contW_thresh ℓ E hE hr₀R).2.2.1
    have hD0pos : 0 < -contW ℓ E r₀ := by linarith
    have hχ₀sq : 0 < (χ r₀) ^ 2 := by positivity
    have hG0pos : 0 < G0 := by
      rw [hG0def]; nlinarith [sq_nonneg (deriv χ r₀), mul_pos hD0pos hχ₀sq]
    set K := G0 / (-contW ℓ E r₀) with hKdef
    have hKpos : 0 < K := div_pos hG0pos hD0pos
    -- threshold facts at any r ≥ r₀
    have hWfacts : ∀ r, r₀ ≤ r → contW ℓ E r < 0 ∧ 1 / r ≤ -contW ℓ E r := fun r hr =>
      ⟨(contW_thresh ℓ E hE (le_trans hr₀R hr)).2.2.1, (contW_thresh ℓ E hE (le_trans hr₀R hr)).2.1⟩
    -- G(r) ≥ K·(−W r)
    have hGlb : ∀ r, r₀ ≤ r →
        K * (-contW ℓ E r) ≤ (deriv χ r) ^ 2 - contW ℓ E r * (χ r) ^ 2 := by
      intro r hr
      have hg := hGratio r hr
      rw [hKdef, div_mul_eq_mul_div, div_le_iff₀ hD0pos]
      exact hg
    -- χ' is bounded by √G0
    have hBnd : ∀ r, r₀ ≤ r → |deriv χ r| ≤ Real.sqrt G0 := by
      intro r hr
      have hDr : 0 ≤ -contW ℓ E r := le_of_lt (by linarith [(hWfacts r hr).1])
      have h1 : (deriv χ r) ^ 2 ≤ G0 := by
        have := hGdec r hr; nlinarith [mul_nonneg hDr (sq_nonneg (χ r)), this]
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h1
    -- χ is Lipschitz on [r₀, ∞)
    have hlip : ∀ x y, r₀ ≤ x → r₀ ≤ y → |χ x - χ y| ≤ Real.sqrt G0 * |x - y| := by
      intro x y hx hy
      have hbd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := χ) (f' := deriv χ) (s := Set.Ici r₀) (C := Real.sqrt G0)
        (fun z hz => (hχ1 z (lt_of_lt_of_le hr₀pos hz)).hasDerivWithinAt)
        (fun z hz => by rw [Real.norm_eq_abs]; exact hBnd z hz) (convex_Ici r₀)
        (Set.mem_Ici.2 hy) (Set.mem_Ici.2 hx)
      simp only [Real.norm_eq_abs] at hbd
      exact hbd
    -- χ → 0
    have hχ0 : Filter.Tendsto χ Filter.atTop (𝓝 0) :=
      l2_tendsto_zero (Real.sqrt_nonneg G0) hlip (hL2.mono_set (Set.Ioi_subset_Ioi (le_of_lt hr₀pos)))
    -- χ² → 0
    have hχ0sq : Filter.Tendsto (fun r => (χ r) ^ 2) Filter.atTop (𝓝 0) := by
      have h := hχ0.mul hχ0
      simpa [← pow_two] using h
    -- pick r₂ ≥ r₀ with χ² < K/4 beyond it
    obtain ⟨r₂, hr₂⟩ := Filter.eventually_atTop.1
      ((hχ0sq.eventually (eventually_lt_nhds (show (0 : ℝ) < K / 4 by positivity))).and
        (eventually_ge_atTop r₀))
    have hr₂r₀ : r₀ ≤ r₂ := (hr₂ r₂ le_rfl).2
    have hr₂pos : 0 < r₂ := lt_of_lt_of_le hr₀pos hr₂r₀
    -- derivative of χ·χ'
    have hχχ'd : ∀ s, 0 < s →
        HasDerivAt (fun t => χ t * deriv χ t) ((deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2) s := by
      intro s hs
      convert (hχ1 s hs).mul (hχ2 s hs) using 1
      rw [← hodeW s hs]; ring
    -- pointwise lower bound (K/2)/s ≤ (χχ')'
    have hptw : ∀ s, r₂ ≤ s → (K / 2) * (1 / s) ≤ (deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2 := by
      intro s hs
      have hsr₀ : r₀ ≤ s := le_trans hr₂r₀ hs
      have hgl := hGlb s hsr₀
      have hsmall : (χ s) ^ 2 < K / 4 := (hr₂ s hs).1
      have hWs := hWfacts s hsr₀
      have hDs : 0 < -contW ℓ E s := by linarith [hWs.1]
      have heq : (deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2
          = ((deriv χ s) ^ 2 - contW ℓ E s * (χ s) ^ 2) - 2 * ((-contW ℓ E s) * (χ s) ^ 2) := by
        ring
      rw [heq]
      have hp1 : (-contW ℓ E s) * (K / 2) ≤ (-contW ℓ E s) * (K - 2 * (χ s) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hDs)
      have hp2 : (1 / s) * (K / 2) ≤ (-contW ℓ E s) * (K / 2) :=
        mul_le_mul_of_nonneg_right hWs.2 (by linarith)
      nlinarith [hgl, hp1, hp2]
    -- χ·χ' → +∞
    have hχχ'top : Filter.Tendsto (fun T => χ T * deriv χ T) Filter.atTop Filter.atTop := by
      have hlow : ∀ T, r₂ ≤ T →
          χ r₂ * deriv χ r₂ + (K / 2) * Real.log (T / r₂) ≤ χ T * deriv χ T := by
        intro T hT
        have hsub : Set.uIcc r₂ T ⊆ Set.Ioi 0 := by
          rw [Set.uIcc_of_le hT]; exact fun z hz => lt_of_lt_of_le hr₂pos hz.1
        have hd : ContinuousOn (deriv χ) (Set.uIcc r₂ T) :=
          fun z hz => (hχ2 z (hsub hz)).continuousAt.continuousWithinAt
        have hc : ContinuousOn χ (Set.uIcc r₂ T) :=
          fun z hz => (hχ1 z (hsub hz)).continuousAt.continuousWithinAt
        have hw : ContinuousOn (contW ℓ E) (Set.uIcc r₂ T) :=
          fun z hz => (contW_hasDerivAt ℓ E (hsub hz)).continuousAt.continuousWithinAt
        have hcont : ContinuousOn (fun s => (deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2)
            (Set.uIcc r₂ T) := (hd.pow 2).add (hw.mul (hc.pow 2))
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s hs => hχχ'd s (hsub hs)) hcont.intervalIntegrable
        have hmono : (K / 2) * Real.log (T / r₂)
            ≤ ∫ s in r₂..T, ((deriv χ s) ^ 2 + contW ℓ E s * (χ s) ^ 2) := by
          have h0notin : (0 : ℝ) ∉ Set.uIcc r₂ T := fun h => by
            have := hsub h; rw [Set.mem_Ioi] at this; exact lt_irrefl 0 this
          have hone : ∫ s in r₂..T, (K / 2) * (1 / s) = (K / 2) * Real.log (T / r₂) := by
            rw [intervalIntegral.integral_const_mul, integral_one_div h0notin]
          have hci : IntervalIntegrable (fun s => (K / 2) * (1 / s)) volume r₂ T :=
            (continuousOn_const.mul (continuousOn_const.div continuousOn_id
              (fun z hz => ne_of_gt (hsub hz)))).intervalIntegrable
          rw [← hone]
          refine intervalIntegral.integral_mono_on hT hci hcont.intervalIntegrable (fun s hs => ?_)
          exact hptw s hs.1
        linarith [hftc, hmono]
      have htendlog : Filter.Tendsto (fun T => χ r₂ * deriv χ r₂ + (K / 2) * Real.log (T / r₂))
          Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_add_const_left
        apply Filter.Tendsto.const_mul_atTop (by positivity)
        exact Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const hr₂pos)
      exact Filter.tendsto_atTop_mono' _ (Filter.eventually_atTop.2 ⟨r₂, hlow⟩) htendlog
    -- χ·χ' → 0
    have hχχ'zero : Filter.Tendsto (fun T => χ T * deriv χ T) Filter.atTop (𝓝 0) := by
      have hb : ∀ᶠ T in Filter.atTop, ‖χ T * deriv χ T‖ ≤ Real.sqrt G0 * |χ T| := by
        filter_upwards [eventually_ge_atTop r₀] with T hT
        rw [Real.norm_eq_abs, abs_mul]
        calc |χ T| * |deriv χ T| ≤ |χ T| * Real.sqrt G0 :=
              mul_le_mul_of_nonneg_left (hBnd T hT) (abs_nonneg _)
          _ = Real.sqrt G0 * |χ T| := mul_comm _ _
      have hg : Filter.Tendsto (fun T => Real.sqrt G0 * |χ T|) Filter.atTop (𝓝 0) := by
        have hax : Filter.Tendsto (fun T => |χ T|) Filter.atTop (𝓝 0) := by
          simpa using hχ0.abs
        simpa using hax.const_mul (Real.sqrt G0)
      exact squeeze_zero_norm' hb hg
    exact (not_tendsto_atTop_of_tendsto_nhds hχχ'zero) hχχ'top
  -- Step 2: extend to (0, ∞) via Cauchy-data uniqueness at R+1
  set r₁ := (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 2 with hr₁def
  have hr₁pos : 0 < r₁ := by rw [hr₁def]; positivity
  have hr₁ev : χ =ᶠ[𝓝 r₁] 0 := by
    filter_upwards [Ioi_mem_nhds (show (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 < r₁ by rw [hr₁def]; linarith)]
      with x hx
    exact hRzero x (le_of_lt hx)
  have h0 : χ r₁ = 0 := hr₁ev.eq_of_nhds
  have h0' : deriv χ r₁ = 0 := by
    rw [hr₁ev.deriv_eq]; simp
  exact cont_cauchy_zero ℓ E χ hχ1 hχ2 hode hr₁pos h0 h0'

/-! ## Quantization -/

/-- **The quantization theorem.**

    A *classical* (`C²` on `(0,∞)`) square-integrable solution of the radial
    equation `H_ℓ ψ = E ψ` with `E < 0` that is nonzero somewhere on `(0,∞)` and
    regular at the origin (`r·ψ(r) → 0` as `r → 0⁺`) exists if and only if
    `E = −1/(2n²)` for some integer `n ≥ ℓ + 1`.

    **On the hypotheses.** The `C²` hypotheses (`HasDerivAt`), the nondegeneracy
    `∃ r₀ > 0, ψ r₀ ≠ 0`, and the regularity `r·ψ(r) → 0` at `0⁺` are all
    essential. `radialHamiltonian` is built from Mathlib's junk-extended `deriv`,
    so *without* differentiability a `ψ` supported on a single point (or supported
    off `(0,∞)`) satisfies the equation vacuously for an arbitrary `E < 0`. And
    *without* the regularity condition the statement is false for `ℓ = 0`: the
    irregular Coulomb solution `ψ = W_{1/κ,1/2}(2κr)/r` is `C²` on `(0,∞)`,
    `L²(r²dr)`, nonzero, and solves the equation for *every* `E < 0` (limit-circle
    case at `0`; see `reduced_radial_L2_quantized`). The
    `C²`/nondegeneracy/regularity form here is the genuine classical-solution
    theorem, and matches the hypotheses of `radial_eigenfunction_unique`.

    **`←` (E = Eₙ ⟹ a solution exists): proved.** Take `ψ = R_{nℓ}`; it is `C²`
    (`differentiable_hydrogenRadial`), L² (`radial_wavefunction_L2`), nonzero
    (from `radial_wavefunction_norm`), solves the equation (`radial_eigenvalue_eq`),
    and is regular at `0` — `r·R_{nℓ}(r)` is continuous with value `0` at `r = 0`.

    **`→` (a solution exists ⟹ E = Eₙ): proved.**
    Set `κ = √(−2E) > 0` and pass to the reduced wavefunction `χ = r·ψ`, which by
    `reduced_ode` solves `χ'' = (ℓ(ℓ+1)/r² − 2/r + κ²)χ`. That an L² such `χ` forces
    `κ = 1/m` with `m ∈ ℕ`, `m ≥ ℓ+1` is `reduced_radial_L2_quantized` (proved via the
    confluent-hypergeometric machinery of `Spectra.Kummer`; see its docstring). Then
    `E = Eₘ` by `energy_eq_of_kappa`. -/
theorem radial_quantization (ℓ : ℕ) (E : ℝ) (hE : E < 0) :
    (∃ (ψ : ℝ → ℝ),
        (∃ r₀, 0 < r₀ ∧ ψ r₀ ≠ 0) ∧ RadialL2 ψ ∧
        (∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) ∧
        (∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r) ∧
        (∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r) ∧
        Filter.Tendsto (fun r => r * ψ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ↔
    ∃ (n : ℕ) (hn : ℓ + 1 ≤ n), E = hydrogenEigenvalue n (by omega) := by
  constructor
  · -- (→) a classical L² bound state forces quantization (via the reduced equation).
    rintro ⟨ψ, hnz, hL2, hψ1, hψ2, heq, hψ0⟩
    obtain ⟨hκpos, hκ2⟩ := kappa_pos_sq E hE
    set κ := Real.sqrt (-2 * E) with hκdef
    set χ : ℝ → ℝ := fun s => s * ψ s with hχdef
    have hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r := by
      intro r hr
      rw [hχdef, deriv_reducedMul ψ (hψ1 r hr)]
      exact hasDerivAt_reducedMul ψ (hψ1 r hr)
    have hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r := by
      intro r hr
      rw [hχdef, deriv2_reducedMul ψ hψ1 hψ2 hr]
      exact hasDerivAt_deriv_reducedMul ψ hψ1 hψ2 hr
    have hode : ∀ r, 0 < r → deriv^[2] χ r
        = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r := by
      intro r hr
      have hχr : χ r = r * ψ r := rfl
      rw [show deriv^[2] χ r = deriv^[2] (fun s => s * ψ s) r from rfl,
        reduced_ode ℓ E ψ hψ1 hψ2 heq hr, hχr, hκ2]
      ring
    have hχL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0) := reduced_integrableOn_sq ψ hL2
    have hχnz : ∃ r, 0 < r ∧ χ r ≠ 0 := reduced_nonzero ψ hnz
    have hχ0 : Filter.Tendsto χ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hψ0
    obtain ⟨m, hm_le, hκm⟩ :=
      reduced_radial_L2_quantized ℓ κ hκpos χ hχ1 hχ2 hode hχ0 hχL2 hχnz
    exact ⟨m, hm_le, energy_eq_of_kappa E κ m (by omega) hκ2 hκm⟩
  · -- (←) construct the eigenfunction R_{nℓ}.
    rintro ⟨n, hn, rfl⟩
    refine ⟨hydrogenRadialWavefunction n ℓ hn, ?_, radial_wavefunction_L2 n ℓ hn,
      fun r _ => (differentiable_hydrogenRadial n ℓ hn r).hasDerivAt,
      fun r _ => (differentiable_deriv_hydrogenRadial n ℓ hn r).hasDerivAt,
      fun r hr => radial_eigenvalue_eq n ℓ hn r hr,
      ((continuous_id'.mul (continuous_hydrogenRadialWavefunction n ℓ hn)).tendsto'
        0 0 (by simp)).mono_left nhdsWithin_le_nhds⟩
    -- nondegeneracy: if R_{nℓ} vanished on all of (0,∞) its unit norm would be 0.
    by_contra hcon
    have hz : ∀ r, 0 < r → hydrogenRadialWavefunction n ℓ hn r = 0 :=
      fun r hr => not_not.1 (fun h => hcon ⟨r, hr, h⟩)
    have hnorm := radial_wavefunction_norm n ℓ hn
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun _ => (0 : ℝ)) (fun r hr => by rw [hz r hr]; ring)] at hnorm
    simp at hnorm

/-! ## Continuous spectrum -/

/-- **For E ≥ 0, every classical L² solution vanishes (continuous spectrum).**

    This gives the continuous spectrum [0, ∞) of H_ℓ: at energy `E ≥ 0` there are
    no `L²` bound states, so any `C²` square-integrable solution is identically
    `0` on `(0,∞)`. (As in `radial_quantization`, the `C²` hypotheses are needed
    for the `deriv`-based `radialHamiltonian` to express a genuine classical ODE.)

    **Reduction (proved).** Passing to `χ = r·ψ` via `reduced_ode`, the claim is
    `reduced_radial_continuum`: with `W = ℓ(ℓ+1)/r² − 2/r − 2E → −2E ≤ 0`, the energy
    `χ'² − Wχ²` controls the solution and an elementary Grönwall/monotonicity argument
    forces any `L²` solution to vanish (no decaying solution exists in the oscillatory
    regime) — see `reduced_radial_continuum`. -/
theorem radial_continuum (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) :
    ∀ ψ : ℝ → ℝ,
      (∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) →
      (∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r) →
      (∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r) → RadialL2 ψ →
      ∀ r, 0 < r → ψ r = 0 := by
  intro ψ hψ1 hψ2 heq hL2
  set χ : ℝ → ℝ := fun s => s * ψ s with hχdef
  have hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r := by
    intro r hr
    rw [hχdef, deriv_reducedMul ψ (hψ1 r hr)]
    exact hasDerivAt_reducedMul ψ (hψ1 r hr)
  have hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r := by
    intro r hr
    rw [hχdef, deriv2_reducedMul ψ hψ1 hψ2 hr]
    exact hasDerivAt_deriv_reducedMul ψ hψ1 hψ2 hr
  have hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r := by
    intro r hr
    have hχr : χ r = r * ψ r := rfl
    rw [show deriv^[2] χ r = deriv^[2] (fun s => s * ψ s) r from rfl,
      reduced_ode ℓ E ψ hψ1 hψ2 heq hr, hχr]
  have hχL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0) := reduced_integrableOn_sq ψ hL2
  have h0 := reduced_radial_continuum ℓ E hE χ hχ1 hχ2 hode hχL2
  intro r hr
  have hrψ : r * ψ r = 0 := h0 r hr
  exact (mul_eq_zero.1 hrψ).resolve_left (ne_of_gt hr)

/-! ## One-dimensionality of the radial eigenspace (analytic core) -/

/-! ## Laguerre at-∞ two-sided asymptotic bound -/

/-- Coefficient of `x^k` in `laguerrePolynomial p α`. -/
private noncomputable def lagCoeff (p : ℕ) (α : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * realBinom (p + α) (p - k) / (k.factorial : ℝ)

private lemma laguerre_eq_sum_coeff (p : ℕ) (α : ℝ) (x : ℝ) :
    laguerrePolynomial p α x = ∑ k ∈ Finset.range (p + 1), lagCoeff p α k * x ^ k := by
  rw [laguerrePolynomial]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [lagCoeff]; ring

private lemma lagCoeff_leading (p : ℕ) (α : ℝ) :
    lagCoeff p α p = (-1 : ℝ) ^ p / (p.factorial : ℝ) := by
  rw [lagCoeff, Nat.sub_self, realBinom_zero, mul_one]

/-- Two-sided asymptotic: `(|cL|/2)·x^p ≤ |L_p^α(x)| ≤ (|cL|+M)·x^p` for `x` large,
where `cL = (-1)^p/p!` is the leading coefficient. -/
private lemma laguerre_asymptotic (p : ℕ) (α : ℝ) :
    ∃ x₀ c C : ℝ, 1 ≤ x₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ x, x₀ ≤ x → c * x ^ p ≤ |laguerrePolynomial p α x| ∧ |laguerrePolynomial p α x| ≤ C * x ^ p := by
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

private lemma chiR_tail_bounds (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ∃ r₂ c C : ℝ, 0 < r₂ ∧ 0 < c ∧ 0 < C ∧ ∀ r, r₂ ≤ r →
      c * (r ^ n * Real.exp (-r / n)) ≤ |r * hydrogenRadialWavefunction n ℓ hn r| ∧
      |r * hydrogenRadialWavefunction n ℓ hn r| ≤ C * (r ^ n * Real.exp (-r / n)) ∧
      r * hydrogenRadialWavefunction n ℓ hn r ≠ 0 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hf1 : (0:ℝ) < ((n - ℓ - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf2 : (0:ℝ) < ((n + ℓ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hNpos : 0 < radialNormalization n ℓ hn := by
    rw [radialNormalization, Real.sqrt_pos]; positivity
  obtain ⟨x₀, cl, Cl, hx₀1, hclpos, hClpos, hbnd⟩ :=
    laguerre_asymptotic (n - ℓ - 1) (2 * (ℓ:ℝ) + 1)
  set N := radialNormalization n ℓ hn with hNdef
  set c : ℝ := N * cl * (2 / (n:ℝ)) ^ (n - 1) with hcdef
  set C : ℝ := N * Cl * (2 / (n:ℝ)) ^ (n - 1) with hCdef
  refine ⟨max 1 (n * x₀ / 2), c, C, lt_of_lt_of_le one_pos (le_max_left _ _),
    by positivity, by positivity, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
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

private lemma chiR_differentiable (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Differentiable ℝ (chiR n ℓ hn) := by
  unfold chiR
  exact differentiable_id.mul (differentiable_hydrogenRadial n ℓ hn)

private lemma chiR_continuous (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : Continuous (chiR n ℓ hn) :=
  (chiR_differentiable n ℓ hn).continuous

private lemma chiR_deriv_eq (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (chiR n ℓ hn) = fun s =>
      hydrogenRadialWavefunction n ℓ hn s + s * deriv (hydrogenRadialWavefunction n ℓ hn) s := by
  funext s
  show deriv (fun t => t * hydrogenRadialWavefunction n ℓ hn t) s = _
  exact deriv_reducedMul _ ((differentiable_hydrogenRadial n ℓ hn s).hasDerivAt)

private lemma chiR_deriv_differentiable (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    Differentiable ℝ (deriv (chiR n ℓ hn)) := by
  rw [chiR_deriv_eq]
  exact (differentiable_hydrogenRadial n ℓ hn).add
    (differentiable_id.mul (differentiable_deriv_hydrogenRadial n ℓ hn))

private lemma chiR_solves (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    deriv^[2] (chiR n ℓ hn) r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + (1 / (n : ℝ)) ^ 2) * chiR n ℓ hn r := by
  unfold chiR
  exact reduced_eigenfunction_solves n ℓ hn hr

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
  have hBpos : 0 < B := by rw [hBdef]; positivity
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
  set W₀ := χ r₂ * deriv (chiR n ℓ hn) r₂ - deriv χ r₂ * chiR n ℓ hn r₂ with hW₀def
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
      have h1 : (0:ℝ) < ((n - ℓ - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have h2 : (0:ℝ) < ((n + ℓ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
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
    show chiR n ℓ hn s ≠ 0
    rw [show chiR n ℓ hn s = hydrogenReducedWavefunction n ℓ hn s from rfl]
    exact ne_of_gt hval
  obtain ⟨δ, hδpos, hδne⟩ := hnear0
  set c₀ := ψ rs / hydrogenRadialWavefunction n ℓ hn rs with hc₀def
  have hchiRrs : chiR n ℓ hn rs ≠ 0 := by
    rw [show chiR n ℓ hn rs = rs * hydrogenRadialWavefunction n ℓ hn rs from rfl]
    exact mul_ne_zero (ne_of_gt hrspos) hRrs
  have hc₀eq : χ rs / chiR n ℓ hn rs = c₀ := by
    show (rs * ψ rs) / (rs * hydrogenRadialWavefunction n ℓ hn rs)
      = ψ rs / hydrogenRadialWavefunction n ℓ hn rs
    rw [mul_div_mul_left _ _ (ne_of_gt hrspos)]
  -- global identification χ = c₀·χ_R
  have hident : ∀ r, 0 < r → χ r = c₀ * chiR n ℓ hn r := by
    intro r hr
    set rmin := min (min r rs) (δ / 2) with hrmindef
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

/-- **Completeness of {R_{nℓ}}_{n ≥ ℓ+1} in the discrete subspace.**

    Every `C²` negative-energy bound state `ψ` (i.e. `ψ ∈ L²(ℝ⁺, r²dr)` with
    `H_ℓ ψ = E ψ` for some `E < 0`) that is regular at the origin (`r·ψ(r) → 0` as
    `r → 0⁺`) can be approximated arbitrarily well in the `L²(r²dr)` norm by finite
    linear combinations of the `R_{nℓ}` (indexed by `k ≥ 0` via `n = k + ℓ + 1`).
    The regularity hypothesis is inherited from `radial_quantization` (it is needed
    to exclude the irregular Coulomb solution at `ℓ = 0`).

    **Reduction (proved here).** This is *not* the full spectral theorem: with the
    bound-state hypothesis it collapses to one-dimensionality of the eigenspaces.
    Concretely, if `ψ ≡ 0` on `(0,∞)` the empty sum works; otherwise
    `radial_quantization` gives `E = Eₙ` for some `n ≥ ℓ+1`, and
    `bound_state_eq_smul_eigenfunction` gives `ψ = c·R_{nℓ}`, so a *single* term
    `c·R_{nℓ}` makes the error integral exactly `0`. The quantization input
    (`reduced_radial_L2_quantized`, via `radial_quantization`) is now proved; the proof
    is therefore complete modulo the single remaining gap it invokes,
    `bound_state_eq_smul_eigenfunction`. The unrestricted statement — approximating
    an *arbitrary* `L²` function, where the differing scales `e^{−r/n}` of the
    `R_{nℓ}` matter — would instead need the self-adjoint spectral decomposition. -/
theorem radial_completeness (ℓ : ℕ) :
    ∀ ψ : ℝ → ℝ, RadialL2 ψ →
      (∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) →
      (∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r) →
      Filter.Tendsto (fun r => r * ψ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      (∃ E : ℝ, E < 0 ∧ ∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r) →
      ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
        ∫ r in Set.Ioi 0,
          (ψ r - ∑ k ∈ Finset.range N,
            c k * hydrogenRadialWavefunction (k + ℓ + 1) ℓ (by omega) r) ^ 2 * r ^ 2 < ε := by
  intro ψ hL2 hψ1 hψ2 hψ0 hbound ε hε
  obtain ⟨E, hElt, heqE⟩ := hbound
  by_cases hnz : ∃ r₀, 0 < r₀ ∧ ψ r₀ ≠ 0
  · -- Nondegenerate bound state: quantize, then it is a scalar multiple of R_{nℓ}.
    obtain ⟨n, hn, hEeq⟩ := (radial_quantization ℓ E hElt).mp
      ⟨ψ, hnz, hL2, hψ1, hψ2, heqE, hψ0⟩
    have heqn : ∀ r, 0 < r → radialHamiltonian ℓ ψ r = hydrogenEigenvalue n (by omega) * ψ r := by
      intro r hr; rw [heqE r hr, hEeq]
    obtain ⟨c, hc⟩ := bound_state_eq_smul_eigenfunction n ℓ hn ψ hL2 hψ1 hψ2 heqn
    obtain ⟨k₀, rfl⟩ : ∃ k₀, n = k₀ + ℓ + 1 := ⟨n - ℓ - 1, by omega⟩
    refine ⟨k₀ + 1, fun k => if k = k₀ then c else 0, ?_⟩
    -- The finite sum collapses to the single term c·R_{nℓ}.
    have hsum : ∀ r, (∑ k ∈ Finset.range (k₀ + 1),
        (if k = k₀ then c else 0) * hydrogenRadialWavefunction (k + ℓ + 1) ℓ (by omega) r)
        = c * hydrogenRadialWavefunction (k₀ + ℓ + 1) ℓ hn r := by
      intro r
      rw [Finset.sum_eq_single k₀]
      · simp
      · intro b _ hb; rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k₀)) h
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun r hr => by rw [hsum r, hc r hr]; ring)]
    simpa using hε
  · -- ψ vanishes on (0,∞): the empty sum already gives error 0.
    have hzero : ∀ r, 0 < r → ψ r = 0 := fun r hr => not_not.1 (fun h => hnz ⟨r, hr, h⟩)
    refine ⟨0, fun _ => 0, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun r hr => by
        simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
        rw [hzero r hr]; ring)]
    simpa using hε

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


/-! ## Interface summary

### For `HydrogenSpectrum.lean`:
- `hydrogenEigenvalue` — E_n = −1/(2n²)
- `hydrogenRadialWavefunction` — R_{nℓ}
- `radial_eigenvalue_eq` — H_ℓ R_{nℓ} = E_n R_{nℓ}
- `radial_quantization` — L² ⟺ E = E_n, n ≥ ℓ+1
- `radial_wavefunction_orthonormal` — orthonormality
- `radial_completeness` — completeness
- `radial_continuum` — continuous spectrum [0, ∞)
- `hydrogenEigenvalue_tendsto` — E_n → 0

### For the Bohr formula:
- `hydrogenEigenvalue` directly gives spectral lines:
  ν_{n→m} = E_m − E_n = (1/2)(1/n² − 1/m²)
-/


end QuantumMechanics.Hydrogen.RadialEq

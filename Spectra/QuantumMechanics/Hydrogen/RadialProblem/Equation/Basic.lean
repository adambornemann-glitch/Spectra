/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Orthogonality
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.Complete
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Laguerre.GenFun
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
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
    that, together with the (still open) quantization `→` direction, would give that
    every negative-energy bound state is a scalar multiple of some `R_{nℓ}`. -/
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

/-- **[Analytic gap — confluent-hypergeometric asymptotics, not yet in Mathlib]**

    *Square-integrable bound states of the reduced radial operator are quantized.*
    If `χ` is a `C²` function on `(0,∞)`, square-integrable there, nonzero at some
    point, and solving the reduced radial equation
    `χ''(r) = (ℓ(ℓ+1)/r² − 2/r + κ²)·χ(r)` with decay rate `κ > 0`,
    then `1/κ` is an integer `m ≥ ℓ+1`, i.e. `κ = 1/m`.

    **Why this is the hard core.** Writing `χ = r^{ℓ+1} e^{−κr} w`, the factor `w`
    solves the confluent (Laguerre/Kummer) ODE — this substitution is *proved*, as
    `laguerre_ansatz_reduced_iff`. In the variable `ρ = 2κr` the regular-at-`0`
    solution `w` is `₁F₁(ℓ+1 − 1/κ; 2ℓ+2; ρ)`, whose coefficients obey
    `c_{k+1}/c_k = (k + ℓ + 1 − 1/κ)/((k+1)(k+2ℓ+2))`. Unless this terminates —
    i.e. `1/κ = ℓ+1+p` for some `p ∈ ℕ` — the ratio tends to `1/k`, so `w(ρ)`
    grows like `e^ρ` and `χ(r) ∼ r^{ℓ+1} e^{+κr}` fails to be square-integrable.
    Formalising this growth estimate needs asymptotics of power-series solutions of
    linear ODEs (a Levinson/Poincaré-type theorem) not yet available in Mathlib.

    Every *mechanical* reduction feeding this lemma is proved: the reduced equation
    (`reduced_ode`), the Kummer substitution (`laguerre_ansatz_reduced_iff`,
    `laguerre_ansatz_residual`), the L²/nondegeneracy transfer
    (`reduced_integrableOn_sq`, `reduced_nonzero`), and the `κ ↔ Eₙ` dictionary
    (`kappa_pos_sq`, `energy_eq_of_kappa`). -/
theorem reduced_radial_L2_quantized (ℓ : ℕ) (κ : ℝ) (hκ : 0 < κ) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r + κ ^ 2) * χ r)
    (hL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0))
    (hnz : ∃ r, 0 < r ∧ χ r ≠ 0) :
    ∃ m : ℕ, ℓ + 1 ≤ m ∧ κ = 1 / (m : ℝ) := by
  sorry

/-- **Consistency of the analytic core on the known eigenfunctions.**

    The reduced hydrogen eigenfunction `χ_{mℓ} = r·R_{mℓ}` (for `m ≥ ℓ+1`) solves
    the reduced radial equation `χ'' = (ℓ(ℓ+1)/r² − 2/r + κ²)·χ` with decay rate
    `κ = 1/m`. Combined with `radial_wavefunction_L2` (square-integrability) and
    `radial_wavefunction_norm` (nonvanishing), this exhibits `χ_{mℓ}` as a witness
    satisfying *every* hypothesis of `reduced_radial_L2_quantized`, with the
    expected conclusion `κ = 1/m`. It confirms that the reduced equation
    (`reduced_ode`) and the analytic gap lemma's hypotheses are correctly stated
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

/-- **[Analytic gap — Coulomb-wave asymptotics, not yet in Mathlib]**

    *No square-integrable solutions for `E ≥ 0`.* For `E ≥ 0`, any `C²`
    square-integrable solution of the reduced radial equation
    `χ''(r) = (ℓ(ℓ+1)/r² − 2/r − 2E)·χ(r)` vanishes identically on `(0,∞)`.

    With `k = √(2E)`, the solutions are the regular/irregular Coulomb wave
    functions, oscillating like `sin(kr − …)`, `cos(kr − …)` as `r → ∞`; both are
    bounded but not square-integrable, so the only L² solution is `0`. (For
    `E = 0` the solutions involve Bessel functions, again non-L².) The reduction
    `ψ ↦ χ = r·ψ` (`reduced_ode`) is proved; the non-existence of L² oscillatory
    solutions is the analytic gap. -/
theorem reduced_radial_continuum (ℓ : ℕ) (E : ℝ) (hE : 0 ≤ E) (χ : ℝ → ℝ)
    (hχ1 : ∀ r, 0 < r → HasDerivAt χ (deriv χ r) r)
    (hχ2 : ∀ r, 0 < r → HasDerivAt (deriv χ) (deriv^[2] χ r) r)
    (hode : ∀ r, 0 < r → deriv^[2] χ r
      = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / r ^ 2 - 2 / r - 2 * E) * χ r)
    (hL2 : IntegrableOn (fun r => χ r ^ 2) (Set.Ioi 0)) :
    ∀ r, 0 < r → χ r = 0 := by
  sorry

/-! ## Quantization -/

/-- **The quantization theorem.**

    A *classical* (`C²` on `(0,∞)`) square-integrable solution of the radial
    equation `H_ℓ ψ = E ψ` with `E < 0` that is nonzero somewhere on `(0,∞)`
    exists if and only if `E = −1/(2n²)` for some integer `n ≥ ℓ + 1`.

    **On the hypotheses.** Both the `C²` hypotheses (`HasDerivAt`) and the
    nondegeneracy `∃ r₀ > 0, ψ r₀ ≠ 0` are essential. `radialHamiltonian` is built
    from Mathlib's junk-extended `deriv`, so *without* differentiability a `ψ`
    supported on a single point (or supported off `(0,∞)`) satisfies the equation
    vacuously for an arbitrary `E < 0` — making the bare statement false. The
    `C²`/nondegeneracy form here is the genuine classical-solution theorem, and
    matches the hypotheses of `radial_eigenfunction_unique`.

    **`←` (E = Eₙ ⟹ a solution exists): proved.** Take `ψ = R_{nℓ}`; it is `C²`
    (`differentiable_hydrogenRadial`), L² (`radial_wavefunction_L2`), nonzero
    (from `radial_wavefunction_norm`), and solves the equation
    (`radial_eigenvalue_eq`).

    **`→` (a solution exists ⟹ E = Eₙ): reduced to a documented analytic gap.**
    Set `κ = √(−2E) > 0` and pass to the reduced wavefunction `χ = r·ψ`, which by
    `reduced_ode` solves `χ'' = (ℓ(ℓ+1)/r² − 2/r + κ²)χ`. The remaining content —
    that an L² such `χ` forces `κ = 1/m` with `m ∈ ℕ`, `m ≥ ℓ+1` — is
    `reduced_radial_L2_quantized`, whose proof needs confluent-hypergeometric
    asymptotics not yet in Mathlib (see its docstring). Then `E = Eₘ` by
    `energy_eq_of_kappa`. -/
theorem radial_quantization (ℓ : ℕ) (E : ℝ) (hE : E < 0) :
    (∃ (ψ : ℝ → ℝ),
        (∃ r₀, 0 < r₀ ∧ ψ r₀ ≠ 0) ∧ RadialL2 ψ ∧
        (∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) ∧
        (∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r) ∧
        (∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r)) ↔
    ∃ (n : ℕ) (hn : ℓ + 1 ≤ n), E = hydrogenEigenvalue n (by omega) := by
  constructor
  · -- (→) a classical L² bound state forces quantization (via the reduced equation).
    rintro ⟨ψ, hnz, hL2, hψ1, hψ2, heq⟩
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
    obtain ⟨m, hm_le, hκm⟩ := reduced_radial_L2_quantized ℓ κ hκpos χ hχ1 hχ2 hode hχL2 hχnz
    exact ⟨m, hm_le, energy_eq_of_kappa E κ m (by omega) hκ2 hκm⟩
  · -- (←) construct the eigenfunction R_{nℓ}.
    rintro ⟨n, hn, rfl⟩
    refine ⟨hydrogenRadialWavefunction n ℓ hn, ?_, radial_wavefunction_L2 n ℓ hn,
      fun r _ => (differentiable_hydrogenRadial n ℓ hn r).hasDerivAt,
      fun r _ => (differentiable_deriv_hydrogenRadial n ℓ hn r).hasDerivAt,
      fun r hr => radial_eigenvalue_eq n ℓ hn r hr⟩
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

    **Reduction.** Passing to `χ = r·ψ` via `reduced_ode`, the claim is
    `reduced_radial_continuum`: the solutions are oscillatory Coulomb waves
    (`E > 0`) or Bessel-type (`E = 0`), bounded but not `L²`. That non-existence
    of `L²` oscillatory solutions is the documented analytic gap. -/
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

/-! ## Completeness of discrete eigenfunctions -/

/-- **[Analytic gap — one-dimensionality of the radial eigenspace.]**

    Every `C²` square-integrable bound state at the eigenvalue `Eₙ` is a scalar
    multiple of `R_{nℓ}`. Equivalently, the eigenspace of `H_ℓ` at `Eₙ` is
    (at most) one-dimensional.

    **Intended proof (reusing what is already formalised).** The weighted
    Wronskian `W(r) = r²(ψ R' − ψ' R)` is constant on `(0,∞)` (Abel; this is the
    `hZderiv` computation inside `radial_eigenfunction_unique`). Square-integrability
    forces `W ≡ 0`: the second solution of the radial ODE at `Eₙ` is irregular at
    `0` (`∼ r^{−ℓ−1}`) and grows at `∞` (`∼ e^{+r/n}`), so a nonzero Wronskian would
    make `ψ` non-`L²`. With `W = 0` at one point, `radial_eigenfunction_unique`
    propagates `ψ R' = ψ' R` to all of `(0,∞)`, and dividing by `R²` (where `R ≠ 0`)
    gives `ψ = c·R`. The remaining analytic input — `W ≡ 0` from L², i.e. excluding
    the irregular/growing solution — is the same decay-selection asymptotics as
    `reduced_radial_L2_quantized` and is not yet available in Mathlib. -/
theorem bound_state_eq_smul_eigenfunction (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (ψ : ℝ → ℝ)
    (hL2 : RadialL2 ψ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (heq : ∀ r, 0 < r → radialHamiltonian ℓ ψ r = hydrogenEigenvalue n (by omega) * ψ r) :
    ∃ c : ℝ, ∀ r, 0 < r → ψ r = c * hydrogenRadialWavefunction n ℓ hn r := by
  sorry

/-- **Completeness of {R_{nℓ}}_{n ≥ ℓ+1} in the discrete subspace.**

    Every `C²` negative-energy bound state `ψ` (i.e. `ψ ∈ L²(ℝ⁺, r²dr)` with
    `H_ℓ ψ = E ψ` for some `E < 0`) can be approximated arbitrarily well in the
    `L²(r²dr)` norm by finite linear combinations of the `R_{nℓ}` (indexed by
    `k ≥ 0` via `n = k + ℓ + 1`).

    **Reduction (proved here).** This is *not* the full spectral theorem: with the
    bound-state hypothesis it collapses to one-dimensionality of the eigenspaces.
    Concretely, if `ψ ≡ 0` on `(0,∞)` the empty sum works; otherwise
    `radial_quantization` gives `E = Eₙ` for some `n ≥ ℓ+1`, and
    `bound_state_eq_smul_eigenfunction` gives `ψ = c·R_{nℓ}`, so a *single* term
    `c·R_{nℓ}` makes the error integral exactly `0`. The proof is therefore
    complete modulo the two documented analytic gaps it invokes
    (`reduced_radial_L2_quantized`, via `radial_quantization`, and
    `bound_state_eq_smul_eigenfunction`). The unrestricted statement — approximating
    an *arbitrary* `L²` function, where the differing scales `e^{−r/n}` of the
    `R_{nℓ}` matter — would instead need the self-adjoint spectral decomposition. -/
theorem radial_completeness (ℓ : ℕ) :
    ∀ ψ : ℝ → ℝ, RadialL2 ψ →
      (∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r) →
      (∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r) →
      (∃ E : ℝ, E < 0 ∧ ∀ r, 0 < r → radialHamiltonian ℓ ψ r = E * ψ r) →
      ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
        ∫ r in Set.Ioi 0,
          (ψ r - ∑ k ∈ Finset.range N,
            c k * hydrogenRadialWavefunction (k + ℓ + 1) ℓ (by omega) r) ^ 2 * r ^ 2 < ε := by
  intro ψ hL2 hψ1 hψ2 hbound ε hε
  obtain ⟨E, hElt, heqE⟩ := hbound
  by_cases hnz : ∃ r₀, 0 < r₀ ∧ ψ r₀ ≠ 0
  · -- Nondegenerate bound state: quantize, then it is a scalar multiple of R_{nℓ}.
    obtain ⟨n, hn, hEeq⟩ := (radial_quantization ℓ E hElt).mp
      ⟨ψ, hnz, hL2, hψ1, hψ2, heqE⟩
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

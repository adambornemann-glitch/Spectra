/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.RadialEigenfunction
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SectorReductionLocal
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SectorProjection
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Degeneracy
import Spectra.QuantumMechanics.Hydrogen.Laplacian.SolidHarmonic

/-!
# General-ℓ hydrogen bound states (operator level)

The reverse direction `E = Eₙ ⟹ eigenpair` of the hydrogen discrete spectrum, for **all**
angular momenta `ℓ < n` and magnetic numbers `|m| ≤ ℓ`, not just the `ℓ = 0` `s`-states
handled in `RadialEigenfunction.lean`.

The genuine eigenfunction is the *separated* product

  `Ψ_{nℓm}(x) = R_{nℓ}(‖x‖) · Y_ℓ^m(x/‖x‖) = S_{nℓ}(‖x‖) · solidHarmonicNat ℓ m x`,

where `S_{nℓ}(r) = R_{nℓ}(r) / r^ℓ` is the **reduced radial profile** (smooth, the `r^ℓ`
prefactor of `R_{nℓ}` divided out), and `solidHarmonicNat ℓ m` is the *solid harmonic*
(`= ‖x‖^ℓ · Y_ℓ^m`, harmonic and homogeneous of degree `ℓ`, smooth away from the origin).

Unlike the `ℓ = 0` case the witness is **not** radial, so the radial `H²`-membership stack
of `RadialEigenfunction.lean` does not apply directly; this file rebuilds it for the
separated product.

## This section: the reduced radial profile (`H1a`)

* `reducedRadialProfile` — `S_{nℓ}(r) = N_{nℓ}·(2/n)^ℓ·e^{−r/n}·L_{n−ℓ−1}^{2ℓ+1}(2r/n)`.
* `contDiff_reducedRadialProfile` — it is `C²` (in fact `C^∞`).
* `hydrogenRadial_eq_pow_mul_reduced` — `R_{nℓ}(r) = r^ℓ · S_{nℓ}(r)`.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory MeasureTheory.Measure Real Complex Filter InnerProductSpace
open QuantumMechanics.Hydrogen.RadialEq
open Spectra.QuantumMechanics.Hydrogen Spectra.SphericalHarmonics Spectra.Sobolev
open Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)
open scoped Topology ContDiff Laplacian

/-! ## H1a — the reduced radial profile `S_{nℓ} = R_{nℓ} / r^ℓ` -/

/-- The **reduced radial profile** `S_{nℓ}(r) = R_{nℓ}(r) / r^ℓ`: the hydrogen radial
wavefunction with its explicit `r^ℓ` prefactor divided out.  Smooth everywhere (the only
non-smooth factor of `R_{nℓ}`, namely `r^ℓ`, has been removed). -/
def reducedRadialProfile (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ℝ → ℝ :=
  fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * Real.exp (-r / n) *
    laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n)

/-- The reduced radial profile is `C^∞`: a product of the smooth exponential and the smooth
Laguerre polynomial composed with a linear map. -/
lemma contDiff_reducedRadialProfile (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ContDiff ℝ ∞ (reducedRadialProfile n ℓ hn) := by
  unfold reducedRadialProfile
  have hL : ContDiff ℝ ∞ (fun r : ℝ =>
      laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n)) :=
    ((laguerre_smooth _ _).of_le le_top).comp (by fun_prop)
  fun_prop

/-- **Factorisation** `R_{nℓ}(r) = r^ℓ · S_{nℓ}(r)`: the radial wavefunction is its `r^ℓ`
prefactor times the (smooth) reduced profile. -/
lemma hydrogenRadial_eq_pow_mul_reduced (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (r : ℝ) :
    hydrogenRadialWavefunction n ℓ hn r = r ^ ℓ * reducedRadialProfile n ℓ hn r := by
  unfold hydrogenRadialWavefunction reducedRadialProfile
  rw [show (2 * r / (n : ℝ)) ^ ℓ = (2 / (n : ℝ)) ^ ℓ * r ^ ℓ from by
    rw [show 2 * r / (n : ℝ) = (2 / (n : ℝ)) * r from by ring, mul_pow]]
  ring

/-! ### Exponentially-weighted decay of the reduced profile `S` and its derivatives

The `H²`-regularity of the *separated* eigenfunction `Ψ = S(‖·‖)·Q` needs the reduced profile
`S = R/r^ℓ` and its first two derivatives to decay exponentially (so that the `S`-radial part is
`L²`).  These mirror the `R_{nℓ}` decay lemmas (`tendsto_*_hydrogenRadial_mul_exp` and the
`exp_bound_of_tendsto` packaging in `RadialEigenfunction.lean`) with the `r^ℓ` prefactor pruned:
`S = A·e^{−r/n}·L(2r/n)` with `A = N_{nℓ}·(2/n)^ℓ` a constant, so the buffered Laguerre limits
(`tendsto_pow_exp_laguerre_buffer` etc., with power `a = 0`) close everything. -/

/-- First derivative of the reduced profile (closed form, valid everywhere). -/
private lemma deriv_reducedRadialProfile (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (reducedRadialProfile n ℓ hn) = fun x =>
      radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
        Real.exp (-x / n) * (-(1 / n)) *
          laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)
        + Real.exp (-x / n) *
          ((2 / n) * deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * x / n))) := by
  funext x
  unfold reducedRadialProfile
  set A := radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ with hA
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with hLdef
  have hLd : ∀ y, HasDerivAt L (deriv L y) y :=
    fun y => ((laguerre_smooth _ _).differentiable (by simp)).differentiableAt.hasDerivAt
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x / n)) (Real.exp (-x / n) * (-1 / n)) x := by
    have hin : HasDerivAt (fun x : ℝ => -x / n) (-1 / n) x := by
      simpa using (hasDerivAt_id x).neg.div_const (n : ℝ)
    simpa using hin.exp
  have hcomp : HasDerivAt (fun x : ℝ => L (2 * x / n)) (deriv L (2 * x / n) * (2 / n)) x := by
    have hin : HasDerivAt (fun x : ℝ => 2 * x / n) (2 / n) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).div_const (n : ℝ)
    exact (hLd (2 * x / n)).comp x hin
  have hF : HasDerivAt (fun x : ℝ => A * Real.exp (-x / n) * L (2 * x / n)) _ x :=
    (hexp.const_mul A).mul hcomp
  rw [hF.deriv]
  ring

/-- The derivative of an associated Laguerre polynomial is again differentiable
(local copy of `RadialEq.differentiable_deriv_laguerre`, which is `private`). -/
private lemma differentiable_deriv_laguerre' (p : ℕ) (α : ℝ) :
    Differentiable ℝ (deriv (laguerrePolynomial p α)) :=
  (((laguerre_smooth p α).of_le (m := 2) le_top).deriv' (n := 1)).differentiable (by simp)

/-- Second derivative of the reduced profile (closed form, valid everywhere). -/
private lemma deriv2_reducedRadialProfile (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (deriv (reducedRadialProfile n ℓ hn)) = fun x =>
      radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * Real.exp (-x / n) * (
        (4 / n ^ 2) * deriv^[2] (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * x / n)
        - (4 / n ^ 2) * deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * x / n)
        + (1 / n ^ 2) * laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * x / n)) := by
  funext x
  rw [deriv_reducedRadialProfile n ℓ hn]
  set A := radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ with hA
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with hLdef
  have hLd : ∀ y, HasDerivAt L (deriv L y) y :=
    fun y => ((laguerre_smooth _ _).differentiable (by simp)).differentiableAt.hasDerivAt
  have hLd2 : ∀ y, HasDerivAt (deriv L) (deriv^[2] L y) y :=
    fun y => (differentiable_deriv_laguerre' _ _ y).hasDerivAt
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
  have hD1 : HasDerivAt (fun x : ℝ => A * (
      Real.exp (-x / n) * (-(1 / n)) * L (2 * x / n)
      + Real.exp (-x / n) * ((2 / n) * deriv L (2 * x / n)))) _ x :=
    (((hexp.mul_const (-(1 / (n : ℝ)))).mul hcomp).add
      ((hexp.mul (hcomp'.const_mul (2 / (n : ℝ)))))) |>.const_mul A
  rw [hD1.deriv]
  ring

/-- **The reduced profile decays exponentially**: `S_{nℓ}(r) · e^{εr} → 0` for `ε < 1/n`. -/
theorem tendsto_reducedRadial_mul_exp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {ε : ℝ}
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto (fun r : ℝ => reducedRadialProfile n ℓ hn r * Real.exp (ε * r))
      Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : (fun r : ℝ => reducedRadialProfile n ℓ hn r * Real.exp (ε * r))
      = fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
          r ^ 0 * Real.exp (-r / n) *
            laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r)) := by
    funext r
    unfold reducedRadialProfile
    rw [pow_zero]; ring
  rw [heq]
  simpa using (tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) 0 (2 * ℓ + 1) hn' hε).const_mul
    (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ)

/-- **The reduced profile's first derivative decays exponentially**:
    `S_{nℓ}'(r) · e^{εr} → 0` for `ε < 1/n`. -/
theorem tendsto_deriv_reducedRadial_mul_exp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {ε : ℝ}
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto (fun r : ℝ => deriv (reducedRadialProfile n ℓ hn) r * Real.exp (ε * r))
      Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : (fun r : ℝ => deriv (reducedRadialProfile n ℓ hn) r * Real.exp (ε * r))
      = fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
          (-(1 / (n : ℝ))) * (r ^ 0 * Real.exp (-r / n) *
            laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r))
          + (2 / (n : ℝ)) * (r ^ 0 * Real.exp (-r / n) *
            deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n) * Real.exp (ε * r))) := by
    funext r
    rw [deriv_reducedRadialProfile n ℓ hn, pow_zero]
    ring
  rw [heq]
  have h1 := tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) 0 (2 * ℓ + 1) hn' hε
  have h2 := tendsto_pow_exp_deriv_laguerre_buffer n (n - ℓ - 1) 0 (2 * ℓ + 1) hn' hε
  have hsum := (h1.const_mul (-(1 / (n : ℝ)))).add (h2.const_mul (2 / (n : ℝ)))
  simpa using hsum.const_mul (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ)

/-- **The reduced profile's second derivative decays exponentially**:
    `S_{nℓ}''(r) · e^{εr} → 0` for `ε < 1/n`. -/
theorem tendsto_deriv2_reducedRadial_mul_exp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {ε : ℝ}
    (hε : ε < 1 / (n : ℝ)) :
    Filter.Tendsto
      (fun r : ℝ => deriv (deriv (reducedRadialProfile n ℓ hn)) r * Real.exp (ε * r))
      Filter.atTop (nhds 0) := by
  have hn' : 0 < n := by omega
  have heq : (fun r : ℝ =>
        deriv (deriv (reducedRadialProfile n ℓ hn)) r * Real.exp (ε * r))
      = fun r => radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ * (
          (4 / (n : ℝ) ^ 2) * (r ^ 0 * Real.exp (-r / n) *
            deriv^[2] (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n) * Real.exp (ε * r))
          + (-(4 / (n : ℝ) ^ 2)) * (r ^ 0 * Real.exp (-r / n) *
            deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n) * Real.exp (ε * r))
          + (1 / (n : ℝ) ^ 2) * (r ^ 0 * Real.exp (-r / n) *
            laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n) * Real.exp (ε * r))) := by
    funext r
    rw [deriv2_reducedRadialProfile n ℓ hn, pow_zero]
    ring
  rw [heq]
  have h1 := tendsto_pow_exp_deriv2_laguerre_buffer n (n - ℓ - 1) 0 (2 * ℓ + 1) hn' hε
  have h2 := tendsto_pow_exp_deriv_laguerre_buffer n (n - ℓ - 1) 0 (2 * ℓ + 1) hn' hε
  have h3 := tendsto_pow_exp_laguerre_buffer n (n - ℓ - 1) 0 (2 * ℓ + 1) hn' hε
  have hsum := ((h1.const_mul (4 / (n : ℝ) ^ 2)).add
    (h2.const_mul (-(4 / (n : ℝ) ^ 2)))).add
    (h3.const_mul (1 / (n : ℝ) ^ 2))
  simpa using hsum.const_mul (radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ)

/-- **The reduced profile decays like `e^{−r/(2n)}`**: `|S_{nℓ}(r)| ≤ C·e^{−r/(2n)}` on `[0,∞)`. -/
lemma reducedRadialProfile_decay (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      |reducedRadialProfile n ℓ hn r| ≤ C * Real.exp (-(1 / (2 * (n:ℝ))) * r) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hε : (1 / (2 * (n : ℝ))) < 1 / (n : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hnR]; nlinarith
  exact exp_bound_of_tendsto (contDiff_reducedRadialProfile n ℓ hn).continuous
    (tendsto_reducedRadial_mul_exp n ℓ hn hε)

/-- **The reduced profile's first derivative decays like `e^{−r/(2n)}`**. -/
lemma deriv_reducedRadialProfile_decay (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      |deriv (reducedRadialProfile n ℓ hn) r| ≤ C * Real.exp (-(1 / (2 * (n:ℝ))) * r) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hε : (1 / (2 * (n : ℝ))) < 1 / (n : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hnR]; nlinarith
  exact exp_bound_of_tendsto
    ((contDiff_reducedRadialProfile n ℓ hn).continuous_deriv (by norm_num))
    (tendsto_deriv_reducedRadial_mul_exp n ℓ hn hε)

/-- **The reduced profile's second derivative decays like `e^{−r/(2n)}`**. -/
lemma deriv2_reducedRadialProfile_decay (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      |deriv (deriv (reducedRadialProfile n ℓ hn)) r| ≤ C * Real.exp (-(1 / (2 * (n:ℝ))) * r) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hε : (1 / (2 * (n : ℝ))) < 1 / (n : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hnR]; nlinarith
  have h2le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  exact exp_bound_of_tendsto
    ((((contDiff_reducedRadialProfile n ℓ hn).of_le h2le).deriv'
      (n := 1)).continuous_deriv (by norm_num))
    (tendsto_deriv2_reducedRadial_mul_exp n ℓ hn hε)

/-- A smooth radial cutoff that equals the reduced profile `S` near a given radius `r > 0`
and vanishes near the origin.  This localizes the (origin-singular) separated eigenfunction to
a globally `C^∞` separated test function near any interior chart point, so the proven sector
reduction `solidTest_reduces_half` applies. -/
lemma exists_cutoff_reduced (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ᶠ s in 𝓝 (0 : ℝ), χ s = 0) ∧
      (∀ᶠ a in 𝓝 r, χ a = reducedRadialProfile n ℓ hn a) := by
  have hr4 : (0 : ℝ) < r / 4 := by positivity
  refine ⟨fun a => reducedRadialProfile n ℓ hn a *
      Real.smoothTransition ((a - r / 4) / (r / 4)), ?_, ?_, ?_⟩
  · exact (contDiff_reducedRadialProfile n ℓ hn).mul
      (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _))
  · filter_upwards [Iio_mem_nhds hr4] with s hs
    simp only [Set.mem_Iio] at hs
    rw [Real.smoothTransition.zero_of_nonpos
      (div_neg_of_neg_of_pos (by linarith) hr4).le, mul_zero]
  · filter_upwards [Ioi_mem_nhds (show r / 2 < r by linarith)] with a ha
    rw [Real.smoothTransition.one_of_one_le
      (by rw [le_div_iff₀ hr4]; simp only [Set.mem_Ioi] at ha; linarith), mul_one]

/-! ## The separated eigenfunction (Cartesian, `Z = 1`) -/

/-- The `ℂ`-valued reduced radial profile. -/
def reducedRadialProfileC (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ℝ → ℂ :=
  fun r => (reducedRadialProfile n ℓ hn r : ℂ)

/-- The **separated eigenfunction** `Ψ_{nℓm}(x) = S_{nℓ}(‖x‖)·solidHarmonicNat ℓ m x`
(`= R_{nℓ}(‖x‖)·Y_ℓ^m(x/‖x‖)`), in Cartesian coordinates at `Z = 1`. -/
def separatedEigenfunction (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) : Spectra.Sobolev.R3 → ℂ :=
  fun x => reducedRadialProfileC n ℓ hn ‖x‖ * solidHarmonicNat ℓ m x

/-! ## H1c — the separated classical eigen-equation off the origin -/

/-- **The separated eigenfunction solves the eigen-equation at every interior chart point**
(`Z = 1` form): for `x = sphereChart r θ φ` with `r > 0` and `θ ∈ (0, π)`,

  `Σⱼ ∂ⱼ² Ψ_{nℓm}(x) = −2·(Eₙ + 1/‖x‖)·Ψ_{nℓm}(x)`,  with `Eₙ = −1/(2n²)`.

This is the Cartesian sum-of-second-derivatives form of `−½ΔΨ − Ψ/r = Eₙ·Ψ`.  The (origin-
singular) `Ψ` is localized near `x` by a smooth cutoff `χ = S` near `r`, making
`χ(‖·‖)·solidHarmonicNat` globally `C²`; the proven sector reduction `solidTest_reduces_half`
plus the radial ODE `radial_eigenvalue_eq` then close it. -/
lemma separated_eigen_chart (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ)
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single j 1)) (sphereChart r θ φ) (EuclideanSpace.single j 1)
      = (-2 : ℂ) * ((hydrogenEigenvalue n (by omega) : ℂ)
          + (‖sphereChart r θ φ‖ : ℂ)⁻¹)
        * separatedEigenfunction n ℓ m hn (sphereChart r θ φ) := by
  classical
  set p : CoulombParams := ⟨1, one_pos⟩ with hp
  set pt := sphereChart r θ φ with hpt
  have hnorm : ‖pt‖ = r := by rw [hpt, norm_sphereChart, abs_of_pos hr]
  have hptne : pt ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact hr)
  have hrne : (r : ℝ) ≠ 0 := hr.ne'
  -- the localizing cutoff `χ = S` near `r`, `0` near `0`
  obtain ⟨χ, hχ, hχ0, hχr⟩ := exists_cutoff_reduced n ℓ hn hr
  set fχ : Spectra.Sobolev.R3 → ℂ :=
    fun x => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x with hfχ
  have hfχ_cd : ContDiff ℝ 2 fχ := solidTest_contDiff ℓ m χ hχ hχ0
  -- `Ψ =ᶠ fχ` near `pt` (where `‖·‖ ≈ r`, so `χ = S`)
  have hΨeq : separatedEigenfunction n ℓ m hn =ᶠ[𝓝 pt] fχ := by
    have htend : Filter.Tendsto (fun x : Spectra.Sobolev.R3 => ‖x‖) (𝓝 pt) (𝓝 r) := by
      rw [← hnorm]; exact continuous_norm.tendsto pt
    filter_upwards [htend.eventually hχr] with x hx
    simp only [separatedEigenfunction, reducedRadialProfileC, hfχ, hx]
  -- locality of `Δ` transfers the computation to the globally-`C²` `fχ`
  have hΔ : Δ (separatedEigenfunction n ℓ m hn) pt = Δ fχ pt :=
    (laplacian_congr_nhds hΨeq).eq_of_nhds
  have hΨcd : ContDiffAt ℝ 2 (separatedEigenfunction n ℓ m hn) pt :=
    (hfχ_cd.contDiffAt).congr_of_eventuallyEq hΨeq
  have hΨdiff : DifferentiableAt ℝ (fderiv ℝ (separatedEigenfunction n ℓ m hn)) pt :=
    (hΨcd.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [← laplacian_eq_sum_fderiv (separatedEigenfunction n ℓ m hn) hΨdiff, hΔ]
  -- the sector reduction for `fχ`, with radial profile `χ·a^ℓ`
  have hred := solidTest_reduces_half p ℓ m hm χ hχ hχ0 (r := r) (θ := θ) (φ := φ) hr hθ
  -- the bracket profile `χ·a^ℓ` agrees with `Rc = ↑R_{nℓ}` near `r`
  have he : (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) =ᶠ[𝓝 r] (Rc n ℓ hn) := by
    filter_upwards [hχr] with a ha
    rw [ha, Rc, hydrogenRadial_eq_pow_mul_reduced n ℓ hn]; push_cast; ring
  have hval : (χ r : ℂ) * (r : ℂ) ^ ℓ = Rc n ℓ hn r := he.eq_of_nhds
  have hd1 : deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r = deriv (Rc n ℓ hn) r := he.deriv_eq
  have hd2 : deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r = deriv (deriv (Rc n ℓ hn)) r :=
    he.deriv.deriv_eq
  -- evaluate the angular factor, the eigenfunction, and the radial bracket near `pt`
  have hm' : |(m : ℤ)| ≤ (ℓ : ℤ) := by simpa using hm
  have hYval : solidHarmonicNat ℓ m pt
      = (r : ℂ) ^ ℓ * SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) := by
    rw [hpt, solidHarmonicNat_sphereChart ℓ m hm hr hθ]
  have hRcr : Rc n ℓ hn r = (r : ℂ) ^ ℓ * (reducedRadialProfile n ℓ hn r : ℂ) := by
    rw [Rc, hydrogenRadial_eq_pow_mul_reduced n ℓ hn]; push_cast; ring
  have hχval : (χ r : ℂ) = (reducedRadialProfile n ℓ hn r : ℂ) := by rw [hχr.self_of_nhds]
  have hsepval : separatedEigenfunction n ℓ m hn pt
      = Rc n ℓ hn r * SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) := by
    rw [separatedEigenfunction, reducedRadialProfileC, hnorm, hYval, hRcr]; ring
  have hmid : (χ ‖pt‖ : ℂ) * solidHarmonicNat ℓ m pt
      = Rc n ℓ hn r * SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) := by
    rw [hnorm, hYval, hχval, hRcr]; ring
  have hZ1 : p.Z = 1 := rfl
  have hcoul : coulombMultiplier p pt = -1 / r := by
    rw [coulombMultiplier, if_neg (show ‖pt‖ ≠ 0 from by rw [hnorm]; exact hrne), hnorm, hZ1]
  -- the radial ODE: `−½R″ − R′/r + (ℓ(ℓ+1)/2r² − 1/r)R = Eₙ·R`
  have hode : (-(1 / 2 : ℂ)) * deriv (deriv (Rc n ℓ hn)) r - (1 / (r : ℂ)) * deriv (Rc n ℓ hn) r
      + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (1 : ℂ) / (r : ℂ)) * Rc n ℓ hn r
      = (hydrogenEigenvalue n (by omega) : ℂ) * Rc n ℓ hn r := by
    have heq := radial_eigenvalue_eq n ℓ hn r hr
    unfold RadialEq.radialHamiltonian at heq
    have h2 : deriv^[2] (hydrogenRadialWavefunction n ℓ hn) r
        = deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r := by simp [Function.iterate_succ]
    rw [h2] at heq
    have hC := congrArg (fun x : ℝ => (x : ℂ)) heq
    simp only [deriv2_Rc]; simp only [deriv_Rc]; simp only [Rc]
    push_cast at hC ⊢
    linear_combination hC
  -- fold `hred` into `pt`-coordinates, substitute the evaluated pieces, and close
  rw [← hpt, hmid, hcoul, hd2, hd1, hval, hZ1] at hred
  rw [hsepval, hnorm]
  push_cast at hode hred ⊢
  linear_combination (-2 : ℂ) * hred
    + (-2 : ℂ) * SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) * hode

/-! ## H1d-i — growth bounds for the solid harmonic (homogeneity of degree ℓ) -/

/-- **The solid harmonic is positively homogeneous of degree `ℓ`**: for `t > 0` and `x ≠ 0`,
`solidHarmonicNat ℓ m (t • x) = t^ℓ · solidHarmonicNat ℓ m x`.  (Needs `m ≤ ℓ` for the power
bookkeeping `t^m · t^{ℓ−m} = t^ℓ`.)  This is the source of the gradient/Hessian growth bounds
`‖∂^k Sℓᵐ(x)‖ ≤ C·‖x‖^{ℓ−k}` driving the `L²`-membership of the separated eigenfunction. -/
lemma solidHarmonicNat_smul (ℓ m : ℕ) (hm : m ≤ ℓ) {t : ℝ} (ht : 0 < t)
    (x : Spectra.Sobolev.R3) (hx : x ≠ 0) :
    solidHarmonicNat ℓ m (t • x) = (t : ℂ) ^ ℓ * solidHarmonicNat ℓ m x := by
  have hsmul : ∀ i : Fin 3, (t • x) i = t * x i := fun i => rfl
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have htn : (t : ℝ) ≠ 0 := ht.ne'
  have hnorm : ‖t • x‖ = t * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have htpow : (t : ℂ) ^ m * (t : ℂ) ^ (ℓ - m) = (t : ℂ) ^ ℓ := by
    rw [← pow_add, Nat.add_sub_cancel' hm]
  unfold solidHarmonicNat
  rw [hsmul 0, hsmul 1, hsmul 2, hnorm,
    show (t * x 2) / (t * ‖x‖) = x 2 / ‖x‖ from by rw [mul_div_mul_left _ _ htn]]
  rw [show ((↑(t * x 0) : ℂ) + I * ↑(t * x 1)) ^ m
        = (t : ℂ) ^ m * ((↑(x 0) : ℂ) + I * ↑(x 1)) ^ m from by
      rw [← mul_pow]; push_cast; ring,
    show ((↑(t * ‖x‖) : ℂ)) ^ (ℓ - m) = (t : ℂ) ^ (ℓ - m) * (↑‖x‖ : ℂ) ^ (ℓ - m) from by
      push_cast; ring]
  rw [← htpow]; ring

/-- **The solid harmonic grows like `‖x‖^ℓ`**: `‖Sℓᵐ(x)‖ ≤ C·‖x‖^ℓ` for `x ≠ 0`.  Direct from
the formula: `|x₀+ix₁| ≤ ‖x‖`, `|x₂/‖x‖| ≤ 1` (so the Rodrigues polynomial is bounded by its
sup on `[−1,1]`), and `‖x‖^m·‖x‖^{ℓ−m} = ‖x‖^ℓ`. -/
lemma solidHarmonicNat_norm_le (ℓ m : ℕ) (hm : m ≤ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 →
      ‖solidHarmonicNat ℓ m x‖ ≤ C * ‖x‖ ^ ℓ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun t : ℝ => (rodriguesDeriv ℓ (ℓ + m)).eval t) (Polynomial.continuous _).continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by norm_num))
  refine ⟨‖(sphericalNorm ℓ m : ℂ)‖ * ‖((-1 : ℂ) ^ m / (2 ^ ℓ * (ℓ.factorial : ℂ)))‖ * M,
    by positivity, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnsq : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  -- the angular factor and the Rodrigues argument are controlled by `‖x‖`
  have h01 : ‖(↑(x 0) : ℂ) + I * ↑(x 1)‖ ≤ ‖x‖ := by
    rw [mul_comm I (↑(x 1) : ℂ), Complex.norm_add_mul_I, ← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x 2), hnsq])
  have hx2 : |x 2| ≤ ‖x‖ := by
    have h1 : (x 2) ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hnsq]
    nlinarith [sq_abs (x 2), h1, norm_nonneg x, abs_nonneg (x 2), hxpos,
      sq_nonneg (‖x‖ - |x 2|)]
  have hquot : x 2 / ‖x‖ ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Icc, ← abs_le, abs_div, abs_of_pos hxpos]
    exact (div_le_one hxpos).mpr hx2
  -- assemble
  rw [solidHarmonicNat]
  simp only [norm_mul]
  have hD : ‖(↑‖x‖ : ℂ) ^ (ℓ - m)‖ = ‖x‖ ^ (ℓ - m) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg x)]
  have hC1 : ‖((↑(x 0) : ℂ) + I * ↑(x 1)) ^ m‖ ≤ ‖x‖ ^ m := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h01 m
  have hE : ‖(↑((rodriguesDeriv ℓ (ℓ + m)).eval (x 2 / ‖x‖)) : ℂ)‖ ≤ M := by
    rw [Complex.norm_real]; have := hM _ hquot; rwa [Real.norm_eq_abs] at this
  calc ‖(sphericalNorm ℓ m : ℂ)‖ * ‖((-1 : ℂ) ^ m / (2 ^ ℓ * (ℓ.factorial : ℂ)))‖
        * ‖((↑(x 0) : ℂ) + I * ↑(x 1)) ^ m‖ * ‖(↑‖x‖ : ℂ) ^ (ℓ - m)‖
        * ‖(↑((rodriguesDeriv ℓ (ℓ + m)).eval (x 2 / ‖x‖)) : ℂ)‖
      ≤ ‖(sphericalNorm ℓ m : ℂ)‖ * ‖((-1 : ℂ) ^ m / (2 ^ ℓ * (ℓ.factorial : ℂ)))‖
        * ‖x‖ ^ m * ‖x‖ ^ (ℓ - m) * M := by
        rw [hD]; gcongr
    _ = ‖(sphericalNorm ℓ m : ℂ)‖ * ‖((-1 : ℂ) ^ m / (2 ^ ℓ * (ℓ.factorial : ℂ)))‖ * M
        * ‖x‖ ^ ℓ := by
        have hp : ‖x‖ ^ m * ‖x‖ ^ (ℓ - m) = ‖x‖ ^ ℓ := by
          rw [← pow_add, Nat.add_sub_cancel' hm]
        rw [← hp]; ring

/-- `solidHarmonicNat ℓ m` is differentiable at every nonzero point. -/
lemma differentiableAt_solidHarmonicNat (ℓ m : ℕ) {x : Spectra.Sobolev.R3} (hx : x ≠ 0) :
    DifferentiableAt ℝ (solidHarmonicNat ℓ m) x :=
  (((solidHarmonicNat_contDiffOn ℓ m).contDiffAt
    (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp))

/-- **Derivative-homogeneity** (degree `ℓ−1`, undivided form): differentiating the homogeneity
identity `Q(t·x) = t^ℓ Q(x)` gives `t · D Q(t·x) = t^ℓ · D Q(x)` for `t > 0`, `x ≠ 0`. -/
lemma fderiv_solidHarmonicNat_smul (ℓ m : ℕ) (hm : m ≤ ℓ) {t : ℝ} (ht : 0 < t)
    {x : Spectra.Sobolev.R3} (hx : x ≠ 0) :
    (t : ℝ) • fderiv ℝ (solidHarmonicNat ℓ m) (t • x)
      = (t : ℝ) ^ ℓ • fderiv ℝ (solidHarmonicNat ℓ m) x := by
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  -- chain rule for `z ↦ Q (t • z)`
  have hscale : HasFDerivAt (fun z : Spectra.Sobolev.R3 => t • z)
      (t • ContinuousLinearMap.id ℝ Spectra.Sobolev.R3) x :=
    (t • ContinuousLinearMap.id ℝ Spectra.Sobolev.R3).hasFDerivAt
  have hLHS : HasFDerivAt (fun z => solidHarmonicNat ℓ m (t • z))
      ((fderiv ℝ (solidHarmonicNat ℓ m) (t • x)).comp
        (t • ContinuousLinearMap.id ℝ Spectra.Sobolev.R3)) x :=
    (differentiableAt_solidHarmonicNat ℓ m htx).hasFDerivAt.comp x hscale
  -- homogeneity near `x`, so `z ↦ Q(t•z)` agrees with `z ↦ t^ℓ • Q z`
  have heq : (fun z : Spectra.Sobolev.R3 => solidHarmonicNat ℓ m (t • z))
      =ᶠ[𝓝 x] (fun z => (t : ℝ) ^ ℓ • solidHarmonicNat ℓ m z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz
    rw [solidHarmonicNat_smul ℓ m hm ht z hz, Complex.real_smul]; push_cast; ring
  have hRHS : HasFDerivAt (fun z => (t : ℝ) ^ ℓ • solidHarmonicNat ℓ m z)
      ((t : ℝ) ^ ℓ • fderiv ℝ (solidHarmonicNat ℓ m) x) x :=
    (differentiableAt_solidHarmonicNat ℓ m hx).hasFDerivAt.const_smul ((t : ℝ) ^ ℓ)
  have hcomp : (fderiv ℝ (solidHarmonicNat ℓ m) (t • x)).comp
      (t • ContinuousLinearMap.id ℝ Spectra.Sobolev.R3)
      = (t : ℝ) • fderiv ℝ (solidHarmonicNat ℓ m) (t • x) := by
    ext h
    simp
  rw [← hcomp]
  exact hLHS.unique (hRHS.congr_of_eventuallyEq heq)

/-- **The solid harmonic's gradient grows like `‖x‖^{ℓ−1}`** (for `ℓ ≥ 1`):
`‖D Sℓᵐ(x)‖ ≤ C·‖x‖^{ℓ−1}`.  Via the sup of `‖D Q‖` over the compact unit sphere, scaled by
derivative-homogeneity `D Q(x) = ‖x‖^{ℓ−1}·D Q(x/‖x‖)`. -/
lemma fderiv_solidHarmonicNat_norm_le (ℓ m : ℕ) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 →
      ‖fderiv ℝ (solidHarmonicNat ℓ m) x‖ ≤ C * ‖x‖ ^ (ℓ - 1) := by
  have hcont : ContinuousOn (fderiv ℝ (solidHarmonicNat ℓ m))
      (Metric.sphere (0 : Spectra.Sobolev.R3) 1) := by
    refine ((solidHarmonicNat_contDiffOn ℓ m).continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton (by simp)).mono (fun u hu => ?_)
    simp only [Metric.mem_sphere, dist_zero_right] at hu
    exact fun (h : u = 0) => by rw [h, norm_zero] at hu; exact zero_ne_one hu
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Spectra.Sobolev.R3) 1).exists_bound_of_continuousOn hcont
  have hpt : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∈
      Metric.sphere (0 : Spectra.Sobolev.R3) 1 := by
    simp [PiLp.norm_single]
  refine ⟨M, le_trans (norm_nonneg _) (hM _ hpt), fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : Spectra.Sobolev.R3 := ‖x‖⁻¹ • x with hu_def
  have hu_mem : u ∈ Metric.sphere (0 : Spectra.Sobolev.R3) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, hu_def, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos hxpos]
    field_simp
  have hune : u ≠ 0 := by
    rw [← norm_ne_zero_iff]; simp only [Metric.mem_sphere, dist_zero_right] at hu_mem
    rw [hu_mem]; exact one_ne_zero
  have hxu : ‖x‖ • u = x := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  have hhom := fderiv_solidHarmonicNat_smul ℓ m hm hxpos hune
  rw [hxu] at hhom
  have hdiv : fderiv ℝ (solidHarmonicNat ℓ m) x
      = ‖x‖ ^ (ℓ - 1) • fderiv ℝ (solidHarmonicNat ℓ m) u := by
    have hpow : ‖x‖ ^ ℓ = ‖x‖ * ‖x‖ ^ (ℓ - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hℓ]
    rw [hpow, mul_smul] at hhom
    exact smul_right_injective _ hxpos.ne' hhom
  rw [hdiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM u hu_mem) (pow_nonneg (norm_nonneg x) _)

/-! ### General machine: derivative bounds from positive homogeneity -/

/-- **Derivative-homogeneity, general** (undivided): if `f` is differentiable off the origin and
positively homogeneous of degree `d` (`f(s·y) = s^d·f y`), then `t·D f(t·x) = t^d·D f(x)`. -/
lemma fderiv_smul_of_homogeneous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Spectra.Sobolev.R3 → F} {d : ℕ}
    (hdiff : ∀ y : Spectra.Sobolev.R3, y ≠ 0 → DifferentiableAt ℝ f y)
    (hhom : ∀ (s : ℝ), 0 < s → ∀ (y : Spectra.Sobolev.R3), y ≠ 0 → f (s • y) = (s ^ d : ℝ) • f y)
    {t : ℝ} (ht : 0 < t) {x : Spectra.Sobolev.R3} (hx : x ≠ 0) :
    (t : ℝ) • fderiv ℝ f (t • x) = (t : ℝ) ^ d • fderiv ℝ f x := by
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  have hscale : HasFDerivAt (fun z : Spectra.Sobolev.R3 => t • z)
      (t • ContinuousLinearMap.id ℝ Spectra.Sobolev.R3) x :=
    (t • ContinuousLinearMap.id ℝ Spectra.Sobolev.R3).hasFDerivAt
  have hLHS : HasFDerivAt (fun z => f (t • z))
      ((fderiv ℝ f (t • x)).comp (t • ContinuousLinearMap.id ℝ Spectra.Sobolev.R3)) x :=
    (hdiff (t • x) htx).hasFDerivAt.comp x hscale
  have heq : (fun z : Spectra.Sobolev.R3 => f (t • z)) =ᶠ[𝓝 x] (fun z => (t : ℝ) ^ d • f z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with z hz using hhom t ht z hz
  have hRHS : HasFDerivAt (fun z => (t : ℝ) ^ d • f z) ((t : ℝ) ^ d • fderiv ℝ f x) x :=
    (hdiff x hx).hasFDerivAt.const_smul ((t : ℝ) ^ d)
  have hcomp : (fderiv ℝ f (t • x)).comp (t • ContinuousLinearMap.id ℝ Spectra.Sobolev.R3)
      = (t : ℝ) • fderiv ℝ f (t • x) := by ext h; simp
  rw [← hcomp]
  exact hLHS.unique (hRHS.congr_of_eventuallyEq heq)

/-- **Growth of the derivative from homogeneity, general**: a degree-`d` (`d ≥ 1`) positively
homogeneous `f` that is differentiable off `0` with `D f` continuous on the unit sphere satisfies
`‖D f(x)‖ ≤ C·‖x‖^{d−1}`. -/
lemma fderiv_norm_le_of_homogeneous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Spectra.Sobolev.R3 → F} {d : ℕ} (hd : 1 ≤ d)
    (hdiff : ∀ y : Spectra.Sobolev.R3, y ≠ 0 → DifferentiableAt ℝ f y)
    (hcont : ContinuousOn (fderiv ℝ f) (Metric.sphere (0 : Spectra.Sobolev.R3) 1))
    (hhom : ∀ (s : ℝ), 0 < s → ∀ (y : Spectra.Sobolev.R3), y ≠ 0 → f (s • y) = (s ^ d : ℝ) • f y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 → ‖fderiv ℝ f x‖ ≤ C * ‖x‖ ^ (d - 1) := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Spectra.Sobolev.R3) 1).exists_bound_of_continuousOn hcont
  have hpt : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∈
      Metric.sphere (0 : Spectra.Sobolev.R3) 1 := by simp [PiLp.norm_single]
  refine ⟨M, le_trans (norm_nonneg _) (hM _ hpt), fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : Spectra.Sobolev.R3 := ‖x‖⁻¹ • x with hu_def
  have hu_mem : u ∈ Metric.sphere (0 : Spectra.Sobolev.R3) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, hu_def, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos hxpos]
    field_simp
  have hune : u ≠ 0 := by
    rw [← norm_ne_zero_iff]; simp only [Metric.mem_sphere, dist_zero_right] at hu_mem
    rw [hu_mem]; exact one_ne_zero
  have hxu : ‖x‖ • u = x := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  have hhom2 := fderiv_smul_of_homogeneous hdiff hhom hxpos hune
  rw [hxu] at hhom2
  have hdiv : fderiv ℝ f x = ‖x‖ ^ (d - 1) • fderiv ℝ f u := by
    have hpow : ‖x‖ ^ d = ‖x‖ * ‖x‖ ^ (d - 1) := by rw [← pow_succ', Nat.sub_add_cancel hd]
    rw [hpow, mul_smul] at hhom2
    exact smul_right_injective _ hxpos.ne' hhom2
  rw [hdiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hM u hu_mem) (pow_nonneg (norm_nonneg x) _)

/-- **Multiply-through derivative bound from homogeneity** (no `d ≥ 1` needed): a degree-`d`
positively homogeneous `f` satisfies `‖x‖·‖D f(x)‖ ≤ C·‖x‖^d`.  This avoids the `ℕ`-truncation
issue of `‖x‖^{d−1}` at `d = 0`, so it applies to `∂Q` even at `ℓ = 1`. -/
lemma fderiv_norm_mul_le_of_homogeneous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Spectra.Sobolev.R3 → F} {d : ℕ}
    (hdiff : ∀ y : Spectra.Sobolev.R3, y ≠ 0 → DifferentiableAt ℝ f y)
    (hcont : ContinuousOn (fderiv ℝ f) (Metric.sphere (0 : Spectra.Sobolev.R3) 1))
    (hhom : ∀ (s : ℝ), 0 < s → ∀ (y : Spectra.Sobolev.R3), y ≠ 0 → f (s • y) = (s ^ d : ℝ) • f y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 →
      ‖x‖ * ‖fderiv ℝ f x‖ ≤ C * ‖x‖ ^ d := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Spectra.Sobolev.R3) 1).exists_bound_of_continuousOn hcont
  have hpt : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∈
      Metric.sphere (0 : Spectra.Sobolev.R3) 1 := by simp [PiLp.norm_single]
  refine ⟨M, le_trans (norm_nonneg _) (hM _ hpt), fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : Spectra.Sobolev.R3 := ‖x‖⁻¹ • x with hu_def
  have hu_mem : u ∈ Metric.sphere (0 : Spectra.Sobolev.R3) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, hu_def, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_pos hxpos]
    field_simp
  have hune : u ≠ 0 := by
    rw [← norm_ne_zero_iff]; simp only [Metric.mem_sphere, dist_zero_right] at hu_mem
    rw [hu_mem]; exact one_ne_zero
  have hxu : ‖x‖ • u = x := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  have hhom2 := fderiv_smul_of_homogeneous hdiff hhom hxpos hune
  rw [hxu] at hhom2
  have hnorm_eq : ‖x‖ * ‖fderiv ℝ f x‖ = ‖x‖ ^ d * ‖fderiv ℝ f u‖ := by
    have h := congrArg norm hhom2
    rwa [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) d)] at h
  rw [hnorm_eq, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM u hu_mem) (pow_nonneg (norm_nonneg x) d)

/-- The solid harmonic's gradient is positively homogeneous of degree `ℓ−1` (divided form). -/
lemma fderiv_solidHarmonicNat_smul' (ℓ m : ℕ) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ) {s : ℝ} (hs : 0 < s)
    {y : Spectra.Sobolev.R3} (hy : y ≠ 0) :
    fderiv ℝ (solidHarmonicNat ℓ m) (s • y)
      = (s ^ (ℓ - 1) : ℝ) • fderiv ℝ (solidHarmonicNat ℓ m) y := by
  have h := fderiv_solidHarmonicNat_smul ℓ m hm hs hy
  have hpow : (s : ℝ) ^ ℓ = s * s ^ (ℓ - 1) := by rw [← pow_succ', Nat.sub_add_cancel hℓ]
  rw [hpow, mul_smul] at h
  exact smul_right_injective _ hs.ne' h

/-- **Multiply-through Hessian bound** for the solid harmonic, valid for all `ℓ ≥ 1` (including
`ℓ = 1`, where `‖∂²Q‖ ~ 1/‖x‖`): `‖x‖·‖D² Sℓᵐ(x)‖ ≤ C·‖x‖^{ℓ−1}`. -/
lemma fderiv2_solidHarmonicNat_norm_mul_le (ℓ m : ℕ) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 →
      ‖x‖ * ‖fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x‖ ≤ C * ‖x‖ ^ (ℓ - 1) := by
  have h2le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hQ2 : ContDiffOn ℝ 2 (solidHarmonicNat ℓ m) {(0 : Spectra.Sobolev.R3)}ᶜ :=
    (solidHarmonicNat_contDiffOn ℓ m).of_le h2le
  have hgrad1 : ContDiffOn ℝ 1 (fderiv ℝ (solidHarmonicNat ℓ m)) {(0 : Spectra.Sobolev.R3)}ᶜ :=
    hQ2.fderiv_of_isOpen isOpen_compl_singleton (by norm_num)
  have hdiff : ∀ y : Spectra.Sobolev.R3, y ≠ 0 →
      DifferentiableAt ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) y :=
    fun y hy => (hgrad1.contDiffAt (isOpen_compl_singleton.mem_nhds hy)).differentiableAt (by simp)
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)))
      (Metric.sphere (0 : Spectra.Sobolev.R3) 1) := by
    refine (hgrad1.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl).mono (fun u hu => ?_)
    simp only [Metric.mem_sphere, dist_zero_right] at hu
    exact fun (h : u = 0) => by rw [h, norm_zero] at hu; exact zero_ne_one hu
  exact fderiv_norm_mul_le_of_homogeneous hdiff hcont
    (fun s hs y hy => fderiv_solidHarmonicNat_smul' ℓ m hm hℓ hs hy)

/-- **The solid harmonic's Hessian grows like `‖x‖^{ℓ−2}`** (for `ℓ ≥ 2`):
`‖D² Sℓᵐ(x)‖ ≤ C·‖x‖^{ℓ−2}`.  The general homogeneity machine applied to `D Q` (degree `ℓ−1`). -/
lemma fderiv2_solidHarmonicNat_norm_le (ℓ m : ℕ) (hm : m ≤ ℓ) (hℓ : 2 ≤ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 →
      ‖fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x‖ ≤ C * ‖x‖ ^ (ℓ - 2) := by
  have h2le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hQ2 : ContDiffOn ℝ 2 (solidHarmonicNat ℓ m) {(0 : Spectra.Sobolev.R3)}ᶜ :=
    (solidHarmonicNat_contDiffOn ℓ m).of_le h2le
  have hgrad1 : ContDiffOn ℝ 1 (fderiv ℝ (solidHarmonicNat ℓ m)) {(0 : Spectra.Sobolev.R3)}ᶜ :=
    hQ2.fderiv_of_isOpen isOpen_compl_singleton (by norm_num)
  have hdiff : ∀ y : Spectra.Sobolev.R3, y ≠ 0 →
      DifferentiableAt ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) y :=
    fun y hy => (hgrad1.contDiffAt (isOpen_compl_singleton.mem_nhds hy)).differentiableAt (by simp)
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)))
      (Metric.sphere (0 : Spectra.Sobolev.R3) 1) := by
    refine (hgrad1.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl).mono (fun u hu => ?_)
    simp only [Metric.mem_sphere, dist_zero_right] at hu
    exact fun (h : u = 0) => by rw [h, norm_zero] at hu; exact zero_ne_one hu
  have hres := fderiv_norm_le_of_homogeneous (d := ℓ - 1) (by omega) hdiff hcont
    (fun s hs y hy => fderiv_solidHarmonicNat_smul' ℓ m hm (by omega) hs hy)
  rwa [show ℓ - 1 - 1 = ℓ - 2 from by omega] at hres

/-! ## H²-Sobolev weak-derivative stack for the separated eigenfunction `Ψ = S(‖·‖)·Q`

Mirrors the radial stack of `RadialEigenfunction.lean` for the genuinely non-radial witness
`Ψ_{nℓm} = reducedRadialProfileC n ℓ hn (‖·‖) · solidHarmonicNat ℓ m`.  We assume `ℓ ≥ 1`
throughout (the `ℓ = 0` case is radial and is handled by `bound_state_of_radial_profile`). -/

/-! ### Polynomial × exponential absorption -/

/-- **Polynomial × exponential absorption.**  For `0 < a' < a` and any `k`, the function
`r ↦ r^k·e^{−a r}` is dominated by `C·e^{−a' r}` on `[0, ∞)`: the extra `r^k` is absorbed into
the gap `a − a' > 0`.  This converts the `poly × exp` pointwise bounds on `∂Ψ`, `∂²Ψ` into the
pure-exponential form consumed by `memLp_two_of_le_exp`. -/
lemma pow_mul_exp_le_exp (k : ℕ) {a a' : ℝ} (_ha' : 0 < a') (haa : a' < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      r ^ k * Real.exp (-a * r) ≤ C * Real.exp (-a' * r) := by
  have hb : (0 : ℝ) < a - a' := by linarith
  -- `g r = r^k·e^{−(a−a') r} → 0` at `+∞`, hence is bounded on `[0,∞)`
  have htend : Filter.Tendsto (fun r : ℝ => r ^ (k : ℝ) * Real.exp (-(a - a') * r))
      Filter.atTop (nhds 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (a - a') hb
  -- pick `R` past which the function is `≤ 1`
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (htend.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num)))
  -- bound the *bracket* `r^k e^{-(a-a') r}` on the compact `[0, max R 0]`
  set R₀ : ℝ := max R 0 with hR₀
  have hR₀0 : 0 ≤ R₀ := le_max_right _ _
  obtain ⟨b, -, hbmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R₀)).exists_isMaxOn
    (Set.nonempty_Icc.mpr hR₀0)
    (Continuous.continuousOn
      (by fun_prop : Continuous fun r : ℝ => r ^ k * Real.exp (-(a - a') * r)))
  set M : ℝ := b ^ k * Real.exp (-(a - a') * b) with hM
  refine ⟨max M 1, le_trans zero_le_one (le_max_right _ _), fun r hr => ?_⟩
  -- split off the `e^{-a' r}` factor: `r^k e^{-a r} = (r^k e^{-(a-a') r}) · e^{-a' r}`
  have hsplit : r ^ k * Real.exp (-a * r)
      = (r ^ k * Real.exp (-(a - a') * r)) * Real.exp (-a' * r) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  -- the bracket `r^k e^{-(a-a') r} ≤ max M 1`
  have hbracket : r ^ k * Real.exp (-(a - a') * r) ≤ max M 1 := by
    rcases le_total r R₀ with hrR | hrR
    · -- compact region: bracket ≤ M ≤ max M 1
      exact le_trans (isMaxOn_iff.mp hbmax r ⟨hr, hrR⟩) (le_max_left _ _)
    · -- tail region: bracket ≤ 1 ≤ max M 1
      have hxR : R ≤ r := le_trans (le_max_left _ _) hrR
      have h1 : r ^ (k : ℝ) * Real.exp (-(a - a') * r) ≤ 1 := le_of_lt (hR r hxR)
      rw [← Real.rpow_natCast r k]
      exact le_trans h1 (le_max_right _ _)
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hbracket (Real.exp_pos _).le

/-! ### The `ℂ`-lift `Sc = reducedRadialProfileC` and its derivatives -/

/-- `reducedRadialProfileC` is `C²` (in fact `C^∞`): the `ℂ`-lift of the smooth real profile. -/
lemma contDiff_reducedRadialProfileC (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ContDiff ℝ 2 (reducedRadialProfileC n ℓ hn) :=
  Complex.ofRealCLM.contDiff.of_le le_top
    |>.comp ((contDiff_reducedRadialProfile n ℓ hn).of_le (WithTop.coe_le_coe.mpr le_top))

/-- The derivative of the `ℂ`-lift is the `ℂ`-lift of the real derivative (mirrors `deriv_Rc`). -/
lemma deriv_reducedRadialProfileC (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (reducedRadialProfileC n ℓ hn)
      = fun r => ((deriv (reducedRadialProfile n ℓ hn) r : ℝ) : ℂ) := by
  funext r
  exact (((((contDiff_reducedRadialProfile n ℓ hn).differentiable
    (by norm_num)).differentiableAt).hasDerivAt).ofReal_comp).deriv

/-- The second derivative of the `ℂ`-lift is the `ℂ`-lift of the real second derivative. -/
lemma deriv2_reducedRadialProfileC (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (deriv (reducedRadialProfileC n ℓ hn))
      = fun r => ((deriv (deriv (reducedRadialProfile n ℓ hn)) r : ℝ) : ℂ) := by
  rw [deriv_reducedRadialProfileC n ℓ hn]
  funext r
  have hS2 : ContDiff ℝ 2 (reducedRadialProfile n ℓ hn) :=
    (contDiff_reducedRadialProfile n ℓ hn).of_le (WithTop.coe_le_coe.mpr le_top)
  exact (((hS2.differentiable_deriv_two).differentiableAt).hasDerivAt.ofReal_comp).deriv

/-- `‖Sc(r)‖ = |S(r)|`. -/
lemma norm_reducedRadialProfileC (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) (r : ℝ) :
    ‖reducedRadialProfileC n ℓ hn r‖ = |reducedRadialProfile n ℓ hn r| := by
  rw [reducedRadialProfileC, Complex.norm_real, Real.norm_eq_abs]

/-! ### Smoothness and the classical first partial of `Ψ`

`Ψ = (Sc∘‖·‖) · Q` is `C²` off the origin (product of the radial `C²` part `Sc∘‖·‖`
and the smooth solid harmonic `Q`). The classical first partial is given by the product rule. -/

/-- `Ψ = (Sc∘‖·‖) · Q` as a pointwise product of functions (for `fderiv` product-rule). -/
lemma separatedEigenfunction_eq_mul (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) :
    separatedEigenfunction n ℓ m hn
      = (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖)
        * solidHarmonicNat ℓ m := rfl

/-- `Ψ` is `C²` away from the origin. -/
lemma separated_contDiffOn (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) :
    ContDiffOn ℝ 2 (separatedEigenfunction n ℓ m hn) {(0 : Spectra.Sobolev.R3)}ᶜ := by
  rw [separatedEigenfunction_eq_mul]
  refine ContDiffOn.mul (fun x hx => ?_)
    ((solidHarmonicNat_contDiffOn ℓ m).of_le (WithTop.coe_le_coe.mpr le_top))
  exact (contDiffAt_radial (reducedRadialProfileC n ℓ hn)
    (contDiff_reducedRadialProfileC n ℓ hn) hx).contDiffWithinAt

/-- `Ψ` is continuous away from the origin. -/
lemma separated_continuousOn (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) :
    ContinuousOn (separatedEigenfunction n ℓ m hn) {(0 : Spectra.Sobolev.R3)}ᶜ :=
  (separated_contDiffOn n ℓ m hn).continuousOn

/-- `Ψ` is differentiable away from the origin. -/
lemma differentiableAt_separated (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n)
    {x : Spectra.Sobolev.R3} (hx : x ≠ 0) :
    DifferentiableAt ℝ (separatedEigenfunction n ℓ m hn) x :=
  ((separated_contDiffOn n ℓ m hn).contDiffAt
    (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by norm_num)

/-- **Product rule for the first partial of `Ψ`** at `x ≠ 0`:
`∂ᵢΨ(x) = Sc(‖x‖)·∂ᵢQ(x) + Q(x)·∂ᵢ(Sc∘‖·‖)(x)`. -/
lemma fderiv_separated_apply (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n)
    {x : Spectra.Sobolev.R3} (hx : x ≠ 0) (i : Fin 3) :
    fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1)
      = reducedRadialProfileC n ℓ hn ‖x‖
          * fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)
        + solidHarmonicNat ℓ m x
          * fderiv ℝ (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖) x
              (EuclideanSpace.single i 1) := by
  have hSc : HasDerivAt (reducedRadialProfileC n ℓ hn)
      (deriv (reducedRadialProfileC n ℓ hn) ‖x‖) ‖x‖ :=
    ((contDiff_reducedRadialProfileC n ℓ hn).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hcd : HasFDerivAt (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖)
      (fderiv ℝ (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖) x) x :=
    (hasFDerivAt_radial (reducedRadialProfileC n ℓ hn) hx hSc).differentiableAt.hasFDerivAt
  have hQ : HasFDerivAt (solidHarmonicNat ℓ m)
      (fderiv ℝ (solidHarmonicNat ℓ m) x) x :=
    (differentiableAt_solidHarmonicNat ℓ m hx).hasFDerivAt
  have hmul := hcd.mul hQ
  rw [separatedEigenfunction_eq_mul, hmul.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### Pointwise exponential-decay bounds (for `ℓ ≥ 1`)

`‖Ψ‖`, `‖∂ᵢΨ‖` decay like `e^{−a‖x‖}`; `‖∂ⱼ∂ᵢΨ‖` decays like `e^{−a‖x‖} + e^{−a‖x‖}/‖x‖`.
The radial part contributes exponential decay (`reducedRadialProfile_decay` etc.), the solid
harmonic the polynomial growth `‖x‖^{ℓ−k}` (absorbed by `pow_mul_exp_le_exp`).  We fix the decay
rate `a = 1/(2n)` (from `S`-decay) and absorb the polynomials into `a' = 1/(4n)`. -/

/-- **`‖Ψ x‖ ≤ C·e^{−‖x‖/(4n)}`** for `x ≠ 0` (`ℓ ≥ 1`). -/
lemma norm_separated_le_exp (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 →
      ‖separatedEigenfunction n ℓ m hn x‖
        ≤ C * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha' : (0:ℝ) < 1 / (4 * (n:ℝ)) := by positivity
  have haa : (1 / (4 * (n:ℝ))) < 1 / (2 * (n:ℝ)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨CS, hCS0, hCS⟩ := reducedRadialProfile_decay n ℓ hn
  obtain ⟨CQ, hCQ0, hCQ⟩ := solidHarmonicNat_norm_le ℓ m hm
  obtain ⟨Cabs, hCabs0, hCabs⟩ := pow_mul_exp_le_exp ℓ ha' haa
  refine ⟨CS * CQ * Cabs, by positivity, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  -- ‖Ψ x‖ = |S(‖x‖)| · ‖Q x‖
  have hΨ : ‖separatedEigenfunction n ℓ m hn x‖
      = |reducedRadialProfile n ℓ hn ‖x‖| * ‖solidHarmonicNat ℓ m x‖ := by
    rw [separatedEigenfunction, norm_mul, norm_reducedRadialProfileC]
  rw [hΨ]
  calc |reducedRadialProfile n ℓ hn ‖x‖| * ‖solidHarmonicNat ℓ m x‖
      ≤ (CS * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) * (CQ * ‖x‖ ^ ℓ) :=
        mul_le_mul (hCS ‖x‖ (norm_nonneg x)) (hCQ x hx) (norm_nonneg _)
          (by positivity)
    _ = CS * CQ * (‖x‖ ^ ℓ * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) := by ring
    _ ≤ CS * CQ * (Cabs * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖)) :=
        mul_le_mul_of_nonneg_left (hCabs ‖x‖ (norm_nonneg x)) (by positivity)
    _ = CS * CQ * Cabs * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) := by ring

/-- The radial-part partial is bounded by the real radial derivative:
`‖∂ᵢ(Sc∘‖·‖)(x)‖ ≤ |S'(‖x‖)|` for `x ≠ 0`. -/
lemma norm_fderiv_radial_reduced_le (n ℓ : ℕ) (hn : ℓ + 1 ≤ n)
    {x : Spectra.Sobolev.R3} (hx : x ≠ 0) (i : Fin 3) :
    ‖fderiv ℝ (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖) x
        (EuclideanSpace.single i 1)‖
      ≤ |deriv (reducedRadialProfile n ℓ hn) ‖x‖| := by
  have hSc : HasDerivAt (reducedRadialProfileC n ℓ hn)
      (deriv (reducedRadialProfileC n ℓ hn) ‖x‖) ‖x‖ :=
    ((contDiff_reducedRadialProfileC n ℓ hn).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have h := norm_fderiv_radial_le (reducedRadialProfileC n ℓ hn) hx hSc i
  rwa [deriv_reducedRadialProfileC, Complex.norm_real, Real.norm_eq_abs] at h

/-- **`‖∂ᵢΨ x (single i 1)‖ ≤ C·e^{−‖x‖/(4n)}`** for `x ≠ 0` (`ℓ ≥ 1`). -/
lemma norm_fderiv_separated_le_exp (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 →
      ‖fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1)‖
        ≤ C * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha' : (0:ℝ) < 1 / (4 * (n:ℝ)) := by positivity
  have haa : (1 / (4 * (n:ℝ))) < 1 / (2 * (n:ℝ)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨CS, hCS0, hCS⟩ := reducedRadialProfile_decay n ℓ hn
  obtain ⟨CS', hCS'0, hCS'⟩ := deriv_reducedRadialProfile_decay n ℓ hn
  obtain ⟨CQ, hCQ0, hCQ⟩ := solidHarmonicNat_norm_le ℓ m hm
  obtain ⟨CdQ, hCdQ0, hCdQ⟩ := fderiv_solidHarmonicNat_norm_le ℓ m hm hℓ
  obtain ⟨Cabs1, hCabs10, hCabs1⟩ := pow_mul_exp_le_exp (ℓ - 1) ha' haa
  obtain ⟨Cabs2, hCabs20, hCabs2⟩ := pow_mul_exp_le_exp ℓ ha' haa
  refine ⟨CS * CdQ * Cabs1 + CQ * CS' * Cabs2, by positivity, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  -- product rule + triangle inequality
  rw [fderiv_separated_apply n ℓ m hn hx i]
  -- first term: ‖Sc(‖x‖)·∂ᵢQ(x)‖ ≤ (CS e) · (CdQ ‖x‖^{ℓ-1})
  have hT1 : ‖reducedRadialProfileC n ℓ hn ‖x‖
      * fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)‖
      ≤ CS * CdQ * (‖x‖ ^ (ℓ - 1) * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) := by
    rw [norm_mul, norm_reducedRadialProfileC]
    have hdQ : ‖fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)‖
        ≤ CdQ * ‖x‖ ^ (ℓ - 1) := by
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      rw [PiLp.norm_single, norm_one, mul_one]
      exact hCdQ x hx
    calc |reducedRadialProfile n ℓ hn ‖x‖|
          * ‖fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)‖
        ≤ (CS * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) * (CdQ * ‖x‖ ^ (ℓ - 1)) :=
          mul_le_mul (hCS ‖x‖ (norm_nonneg x)) hdQ (norm_nonneg _) (by positivity)
      _ = CS * CdQ * (‖x‖ ^ (ℓ - 1) * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) := by ring
  -- second term: ‖Q(x)·∂ᵢ(Sc∘‖·‖)(x)‖ ≤ (CQ ‖x‖^ℓ) · (CS' e)
  have hT2 : ‖solidHarmonicNat ℓ m x
      * fderiv ℝ (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖) x
          (EuclideanSpace.single i 1)‖
      ≤ CQ * CS' * (‖x‖ ^ ℓ * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) := by
    rw [norm_mul]
    have hdr : ‖fderiv ℝ (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖) x
        (EuclideanSpace.single i 1)‖
        ≤ CS' * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖) :=
      le_trans (norm_fderiv_radial_reduced_le n ℓ hn hx i) (hCS' ‖x‖ (norm_nonneg x))
    calc ‖solidHarmonicNat ℓ m x‖
          * ‖fderiv ℝ (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖) x
              (EuclideanSpace.single i 1)‖
        ≤ (CQ * ‖x‖ ^ ℓ) * (CS' * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) :=
          mul_le_mul (hCQ x hx) hdr (norm_nonneg _) (by positivity)
      _ = CQ * CS' * (‖x‖ ^ ℓ * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) := by ring
  calc ‖reducedRadialProfileC n ℓ hn ‖x‖
        * fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)
      + solidHarmonicNat ℓ m x
        * fderiv ℝ (fun y : Spectra.Sobolev.R3 => reducedRadialProfileC n ℓ hn ‖y‖) x
            (EuclideanSpace.single i 1)‖
      ≤ CS * CdQ * (‖x‖ ^ (ℓ - 1) * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖))
        + CQ * CS' * (‖x‖ ^ ℓ * Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖)) :=
        le_trans (norm_add_le _ _) (add_le_add hT1 hT2)
    _ ≤ CS * CdQ * (Cabs1 * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖))
        + CQ * CS' * (Cabs2 * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hCabs1 ‖x‖ (norm_nonneg x)) (by positivity))
          (mul_le_mul_of_nonneg_left (hCabs2 ‖x‖ (norm_nonneg x)) (by positivity))
    _ = (CS * CdQ * Cabs1 + CQ * CS' * Cabs2) * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) := by ring

/-! ### Second-derivative bound for `Ψ`

The classical second partial `∂ⱼ∂ᵢΨ` is bounded by `C·e^{−a‖x‖} + C'·e^{−a‖x‖}/‖x‖`: the worst
singularity is exactly `1/‖x‖` (for all `ℓ ≥ 1`), coming from the radial Hessian and from the
gradient of `∂ᵢQ`.  We differentiate the product expression for `∂ᵢΨ` (valid `=ᶠ` near `x`). -/

/-- The op-norm of the gradient of `∂ᵢQ = fderiv Q · (single i 1)` is bounded by the Hessian
op-norm of `Q`: `‖D(∂ᵢQ)(x)‖ ≤ ‖D²Q(x)‖`. -/
lemma norm_fderiv_solidHarmonic_partial_le (ℓ m : ℕ)
    {x : Spectra.Sobolev.R3} (hx : x ≠ 0) (i : Fin 3) :
    ‖fderiv ℝ (fun y => fderiv ℝ (solidHarmonicNat ℓ m) y (EuclideanSpace.single i 1)) x‖
      ≤ ‖fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x‖ := by
  have h2le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hQ2 : ContDiffOn ℝ 2 (solidHarmonicNat ℓ m) {(0 : Spectra.Sobolev.R3)}ᶜ :=
    (solidHarmonicNat_contDiffOn ℓ m).of_le h2le
  have hgrad1 : ContDiffOn ℝ 1 (fderiv ℝ (solidHarmonicNat ℓ m))
      {(0 : Spectra.Sobolev.R3)}ᶜ :=
    hQ2.fderiv_of_isOpen isOpen_compl_singleton (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x :=
    (hgrad1.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  -- `(fun y => fderiv Q y v) = (apply v) ∘ (fderiv Q)`, so its fderiv is `(apply v).comp (D²Q)`
  have hfd : HasFDerivAt (fun y => fderiv ℝ (solidHarmonicNat ℓ m) y (EuclideanSpace.single i 1))
      ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).comp
        (fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x)) x := by
    have h0 := (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt.comp x
      hdiff.hasFDerivAt
    simpa [ContinuousLinearMap.apply_apply, Function.comp_def] using h0
  rw [hfd.fderiv]
  calc ‖(ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).comp
          (fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x)‖
      ≤ ‖ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))‖
          * ‖fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x‖ := by
        gcongr
        refine le_trans (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => ?_)) le_rfl
        rw [ContinuousLinearMap.apply_apply, one_mul]
        exact le_trans (ContinuousLinearMap.le_opNorm _ _)
          (by rw [PiLp.norm_single, norm_one, mul_one])
    _ = ‖fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x‖ := one_mul _

/-- The radial-part Hessian bound: `‖D(∂ᵢ(Sc∘‖·‖))(x)‖ ≤ |S''(‖x‖)| + 2|S'(‖x‖)|/‖x‖`. -/
lemma norm_fderiv_fderiv_radial_reduced_le (n ℓ : ℕ) (hn : ℓ + 1 ≤ n)
    {x : Spectra.Sobolev.R3} (hx : x ≠ 0) (i : Fin 3) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => reducedRadialProfileC n ℓ hn ‖z‖) y
        (EuclideanSpace.single i 1)) x‖
      ≤ |deriv (deriv (reducedRadialProfile n ℓ hn)) ‖x‖|
        + 2 * |deriv (reducedRadialProfile n ℓ hn) ‖x‖| / ‖x‖ := by
  have h := norm_fderiv_fderiv_radial_le (reducedRadialProfileC n ℓ hn)
    (contDiff_reducedRadialProfileC n ℓ hn) hx i
  rw [deriv2_reducedRadialProfileC] at h
  rw [deriv_reducedRadialProfileC] at h
  rwa [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- **Hessian op-norm of `Ψ`** at `x ≠ 0`: differentiating the product expression for `∂ᵢΨ`
gives the four-term bound
`‖D(∂ᵢΨ)(x)‖ ≤ |S|·‖D(∂ᵢQ)‖ + ‖∂ᵢQ‖·|S'| + ‖Q‖·(|S''|+2|S'|/‖x‖) + |S'|·‖DQ‖`,
all evaluated at `x` (with `S`-derivatives at `‖x‖`).  The directional second partial
`∂ⱼ∂ᵢΨ = D(∂ᵢΨ)(x)(single j 1)` is bounded by this op-norm. -/
lemma norm_fderiv_fderiv_separated_le (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n)
    {x : Spectra.Sobolev.R3} (hx : x ≠ 0) (i : Fin 3) :
    ‖fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1)) x‖
      ≤ |reducedRadialProfile n ℓ hn ‖x‖|
          * ‖fderiv ℝ (fun y => fderiv ℝ (solidHarmonicNat ℓ m) y
              (EuclideanSpace.single i 1)) x‖
        + ‖fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)‖
          * |deriv (reducedRadialProfile n ℓ hn) ‖x‖|
        + ‖solidHarmonicNat ℓ m x‖
          * ‖fderiv ℝ (fun y => fderiv ℝ (fun z => reducedRadialProfileC n ℓ hn ‖z‖) y
              (EuclideanSpace.single i 1)) x‖
        + |deriv (reducedRadialProfile n ℓ hn) ‖x‖|
          * ‖fderiv ℝ (solidHarmonicNat ℓ m) x‖ := by
  classical
  set Acl : Spectra.Sobolev.R3 → ℂ := fun y => reducedRadialProfileC n ℓ hn ‖y‖ with hAcl
  set Q : Spectra.Sobolev.R3 → ℂ := solidHarmonicNat ℓ m with hQ
  set B : Spectra.Sobolev.R3 → ℂ := fun y => fderiv ℝ Q y (EuclideanSpace.single i 1) with hB
  set Dr : Spectra.Sobolev.R3 → ℂ :=
    fun y => fderiv ℝ Acl y (EuclideanSpace.single i 1) with hDr
  -- differentiability of the factors at `x`
  have hSc : HasDerivAt (reducedRadialProfileC n ℓ hn)
      (deriv (reducedRadialProfileC n ℓ hn) ‖x‖) ‖x‖ :=
    ((contDiff_reducedRadialProfileC n ℓ hn).differentiable
      (by norm_num)).differentiableAt.hasDerivAt
  have hAcl_diff : DifferentiableAt ℝ Acl x :=
    (hasFDerivAt_radial (reducedRadialProfileC n ℓ hn) hx hSc).differentiableAt
  have h2le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hQ2 : ContDiffOn ℝ 2 Q {(0 : Spectra.Sobolev.R3)}ᶜ :=
    (solidHarmonicNat_contDiffOn ℓ m).of_le h2le
  have hQ_diff : DifferentiableAt ℝ Q x := differentiableAt_solidHarmonicNat ℓ m hx
  have hAcl2 : ContDiffAt ℝ 2 Acl x :=
    contDiffAt_radial (reducedRadialProfileC n ℓ hn) (contDiff_reducedRadialProfileC n ℓ hn) hx
  have hB_diff : DifferentiableAt ℝ B x := by
    have hgrad1 : ContDiffOn ℝ 1 (fderiv ℝ Q) {(0 : Spectra.Sobolev.R3)}ᶜ :=
      hQ2.fderiv_of_isOpen isOpen_compl_singleton (by norm_num)
    have hdiff : DifferentiableAt ℝ (fderiv ℝ Q) x :=
      (hgrad1.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
    exact (hdiff.clm_apply (differentiableAt_const _))
  have hDr_diff : DifferentiableAt ℝ Dr x :=
    ((first_deriv_contDiffOn (reducedRadialProfileC n ℓ hn)
      (contDiff_reducedRadialProfileC n ℓ hn) i).contDiffAt
      (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by simp)
  -- `∂ᵢΨ =ᶠ Acl·B + Q·Dr` near `x`
  have hEq : (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y (EuclideanSpace.single i 1))
      =ᶠ[𝓝 x] (fun y => Acl y * B y + Q y * Dr y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact fderiv_separated_apply n ℓ m hn hy i
  -- transfer the fderiv and apply the product rule
  have hP1 : HasFDerivAt (fun y => Acl y * B y)
      (Acl x • fderiv ℝ B x + B x • fderiv ℝ Acl x) x :=
    hAcl_diff.hasFDerivAt.mul hB_diff.hasFDerivAt
  have hP2 : HasFDerivAt (fun y => Q y * Dr y)
      (Q x • fderiv ℝ Dr x + Dr x • fderiv ℝ Q x) x :=
    hQ_diff.hasFDerivAt.mul hDr_diff.hasFDerivAt
  have hSum : HasFDerivAt (fun y => Acl y * B y + Q y * Dr y)
      ((Acl x • fderiv ℝ B x + B x • fderiv ℝ Acl x)
        + (Q x • fderiv ℝ Dr x + Dr x • fderiv ℝ Q x)) x := hP1.add hP2
  have hfd : fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
      (EuclideanSpace.single i 1)) x
      = (Acl x • fderiv ℝ B x + B x • fderiv ℝ Acl x)
        + (Q x • fderiv ℝ Dr x + Dr x • fderiv ℝ Q x) :=
    (hEq.fderiv_eq).trans hSum.fderiv
  rw [hfd]
  -- triangle inequality + op-norm bounds
  calc ‖(Acl x • fderiv ℝ B x + B x • fderiv ℝ Acl x)
          + (Q x • fderiv ℝ Dr x + Dr x • fderiv ℝ Q x)‖
      ≤ (‖Acl x • fderiv ℝ B x‖ + ‖B x • fderiv ℝ Acl x‖)
        + (‖Q x • fderiv ℝ Dr x‖ + ‖Dr x • fderiv ℝ Q x‖) :=
        le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ = ‖Acl x‖ * ‖fderiv ℝ B x‖ + ‖B x‖ * ‖fderiv ℝ Acl x‖
        + (‖Q x‖ * ‖fderiv ℝ Dr x‖ + ‖Dr x‖ * ‖fderiv ℝ Q x‖) := by
        rw [norm_smul, norm_smul, norm_smul, norm_smul]
    _ ≤ |reducedRadialProfile n ℓ hn ‖x‖| * ‖fderiv ℝ B x‖
        + ‖fderiv ℝ Q x (EuclideanSpace.single i 1)‖
          * |deriv (reducedRadialProfile n ℓ hn) ‖x‖|
        + (‖Q x‖ * ‖fderiv ℝ Dr x‖
          + |deriv (reducedRadialProfile n ℓ hn) ‖x‖| * ‖fderiv ℝ Q x‖) := by
        have hAclx : ‖Acl x‖ = |reducedRadialProfile n ℓ hn ‖x‖| := by
          rw [hAcl, norm_reducedRadialProfileC]
        have hAclfd : ‖fderiv ℝ Acl x‖ ≤ |deriv (reducedRadialProfile n ℓ hn) ‖x‖| := by
          have h := norm_fderiv_radial_op_le (reducedRadialProfileC n ℓ hn) hx hSc
          rwa [deriv_reducedRadialProfileC, Complex.norm_real, Real.norm_eq_abs] at h
        have hDrx : ‖Dr x‖ ≤ |deriv (reducedRadialProfile n ℓ hn) ‖x‖| :=
          norm_fderiv_radial_reduced_le n ℓ hn hx i
        rw [hAclx, show B x = fderiv ℝ Q x (EuclideanSpace.single i 1) from rfl]
        gcongr
    _ = |reducedRadialProfile n ℓ hn ‖x‖| * ‖fderiv ℝ B x‖
        + ‖fderiv ℝ Q x (EuclideanSpace.single i 1)‖
          * |deriv (reducedRadialProfile n ℓ hn) ‖x‖|
        + ‖Q x‖ * ‖fderiv ℝ Dr x‖
        + |deriv (reducedRadialProfile n ℓ hn) ‖x‖| * ‖fderiv ℝ Q x‖ := by ring

/-- **`‖∂ⱼ∂ᵢΨ x (single j 1)‖ ≤ C·e^{−a‖x‖} + C'·(e^{−a‖x‖}/‖x‖)`** for `x ≠ 0` (`ℓ ≥ 1`), with
`a = 1/(4n)`.  The four terms of the Hessian bound give `poly × exp` (regular) and
`poly × exp/‖x‖` (the worst, `1/‖x‖`, singularity) contributions, each absorbed by
`pow_mul_exp_le_exp`. -/
lemma norm_fderiv2_separated_le_exp (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ)
    (i j : Fin 3) :
    ∃ C C' : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧ ∀ x : Spectra.Sobolev.R3, x ≠ 0 →
      ‖fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)‖
        ≤ C * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖)
          + C' * (Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) / ‖x‖) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha' : (0:ℝ) < 1 / (4 * (n:ℝ)) := by positivity
  have haa : (1 / (4 * (n:ℝ))) < 1 / (2 * (n:ℝ)) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨CS, hCS0, hCS⟩ := reducedRadialProfile_decay n ℓ hn
  obtain ⟨CS', hCS'0, hCS'⟩ := deriv_reducedRadialProfile_decay n ℓ hn
  obtain ⟨CS'', hCS''0, hCS''⟩ := deriv2_reducedRadialProfile_decay n ℓ hn
  obtain ⟨CQ, hCQ0, hCQ⟩ := solidHarmonicNat_norm_le ℓ m hm
  obtain ⟨CdQ, hCdQ0, hCdQ⟩ := fderiv_solidHarmonicNat_norm_le ℓ m hm hℓ
  obtain ⟨Cd2Q, hCd2Q0, hCd2Q⟩ := fderiv2_solidHarmonicNat_norm_mul_le ℓ m hm hℓ
  -- absorption constants
  obtain ⟨Aℓ1, hAℓ10, hAℓ1⟩ := pow_mul_exp_le_exp (ℓ - 1) ha' haa
  obtain ⟨Aℓ, hAℓ0, hAℓ⟩ := pow_mul_exp_le_exp ℓ ha' haa
  -- regular coefficient `C` and singular coefficient `C'`
  refine ⟨CS' * CdQ * Aℓ1 + CQ * CS'' * Aℓ + CS' * CdQ * Aℓ1,
    CS * Cd2Q * Aℓ1 + CQ * 2 * CS' * Aℓ, by positivity, by positivity, fun x hx => ?_⟩
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  -- directional ≤ op-norm of the Hessian
  have hdir : ‖fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)‖
      ≤ ‖fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
          (EuclideanSpace.single i 1)) x‖ := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    rw [PiLp.norm_single, norm_one, mul_one]
  refine le_trans hdir (le_trans (norm_fderiv_fderiv_separated_le n ℓ m hn hx i) ?_)
  -- abbreviations for the four term-bounds
  set eA : ℝ := Real.exp (-(1 / (2 * (n:ℝ))) * ‖x‖) with heA
  set eB : ℝ := Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) with heB
  have heA0 : 0 < eA := Real.exp_pos _
  have heB0 : 0 < eB := Real.exp_pos _
  -- term-1: `|S|·‖D(∂ᵢQ)‖ ≤ CS·eA · (Cd2Q ‖x‖^{ℓ-1}/‖x‖)`
  have hDB : ‖fderiv ℝ (fun y => fderiv ℝ (solidHarmonicNat ℓ m) y (EuclideanSpace.single i 1)) x‖
      ≤ Cd2Q * ‖x‖ ^ (ℓ - 1) / ‖x‖ := by
    have h1 := norm_fderiv_solidHarmonic_partial_le ℓ m hx i
    have h2 := hCd2Q x hx
    rw [le_div_iff₀ hxpos]
    calc ‖fderiv ℝ (fun y => fderiv ℝ (solidHarmonicNat ℓ m) y
            (EuclideanSpace.single i 1)) x‖ * ‖x‖
        ≤ ‖fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x‖ * ‖x‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖x‖ * ‖fderiv ℝ (fderiv ℝ (solidHarmonicNat ℓ m)) x‖ := by ring
      _ ≤ Cd2Q * ‖x‖ ^ (ℓ - 1) := h2
  -- the two absorption facts
  have habs1 : ‖x‖ ^ (ℓ - 1) * eA ≤ Aℓ1 * eB := hAℓ1 ‖x‖ (norm_nonneg x)
  have habsℓ : ‖x‖ ^ ℓ * eA ≤ Aℓ * eB := hAℓ ‖x‖ (norm_nonneg x)
  have hT1 : |reducedRadialProfile n ℓ hn ‖x‖|
        * ‖fderiv ℝ (fun y => fderiv ℝ (solidHarmonicNat ℓ m) y (EuclideanSpace.single i 1)) x‖
      ≤ CS * Cd2Q * Aℓ1 * (eB / ‖x‖) := by
    calc |reducedRadialProfile n ℓ hn ‖x‖|
          * ‖fderiv ℝ (fun y => fderiv ℝ (solidHarmonicNat ℓ m) y
              (EuclideanSpace.single i 1)) x‖
        ≤ (CS * eA) * (Cd2Q * ‖x‖ ^ (ℓ - 1) / ‖x‖) :=
          mul_le_mul (hCS ‖x‖ (norm_nonneg x)) hDB (norm_nonneg _) (by positivity)
      _ = CS * Cd2Q * (‖x‖ ^ (ℓ - 1) * eA) * (1 / ‖x‖) := by ring
      _ ≤ CS * Cd2Q * (Aℓ1 * eB) * (1 / ‖x‖) := by
          gcongr
      _ = CS * Cd2Q * Aℓ1 * (eB / ‖x‖) := by ring
  -- term-2: `‖∂ᵢQ‖·|S'| ≤ CdQ ‖x‖^{ℓ-1} · CS' eA ≤ CS'·CdQ·Aℓ1·eB`
  have hdQi : ‖fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)‖
      ≤ CdQ * ‖x‖ ^ (ℓ - 1) := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
    rw [PiLp.norm_single, norm_one, mul_one]
    exact hCdQ x hx
  have hT2 : ‖fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)‖
        * |deriv (reducedRadialProfile n ℓ hn) ‖x‖|
      ≤ CS' * CdQ * Aℓ1 * eB := by
    calc ‖fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)‖
          * |deriv (reducedRadialProfile n ℓ hn) ‖x‖|
        ≤ (CdQ * ‖x‖ ^ (ℓ - 1)) * (CS' * eA) :=
          mul_le_mul hdQi (hCS' ‖x‖ (norm_nonneg x)) (abs_nonneg _) (by positivity)
      _ = CS' * CdQ * (‖x‖ ^ (ℓ - 1) * eA) := by rw [heA]; ring
      _ ≤ CS' * CdQ * (Aℓ1 * eB) := by gcongr
      _ = CS' * CdQ * Aℓ1 * eB := by ring
  -- term-3: `‖Q‖·‖D(∂ᵢ radial)‖ ≤ CQ‖x‖^ℓ·(|S''|+2|S'|/‖x‖)` (regular + singular split)
  have hT3 : ‖solidHarmonicNat ℓ m x‖
        * ‖fderiv ℝ (fun y => fderiv ℝ (fun z => reducedRadialProfileC n ℓ hn ‖z‖) y
            (EuclideanSpace.single i 1)) x‖
      ≤ CQ * CS'' * Aℓ * eB + CQ * 2 * CS' * Aℓ * (eB / ‖x‖) := by
    have hHess := norm_fderiv_fderiv_radial_reduced_le n ℓ hn hx i
    have hsplit : ‖solidHarmonicNat ℓ m x‖
          * ‖fderiv ℝ (fun y => fderiv ℝ (fun z => reducedRadialProfileC n ℓ hn ‖z‖) y
              (EuclideanSpace.single i 1)) x‖
        ≤ (CQ * ‖x‖ ^ ℓ)
            * (|deriv (deriv (reducedRadialProfile n ℓ hn)) ‖x‖|
              + 2 * |deriv (reducedRadialProfile n ℓ hn) ‖x‖| / ‖x‖) :=
      mul_le_mul (hCQ x hx) hHess (norm_nonneg _) (by positivity)
    refine le_trans hsplit ?_
    -- distribute and bound each of the two summands
    rw [mul_add]
    apply add_le_add
    · -- regular: `CQ‖x‖^ℓ·|S''| ≤ CQ·CS''·Aℓ·eB`
      calc CQ * ‖x‖ ^ ℓ * |deriv (deriv (reducedRadialProfile n ℓ hn)) ‖x‖|
          ≤ CQ * ‖x‖ ^ ℓ * (CS'' * eA) := by
            gcongr; exact hCS'' ‖x‖ (norm_nonneg x)
        _ = CQ * CS'' * (‖x‖ ^ ℓ * eA) := by rw [heA]; ring
        _ ≤ CQ * CS'' * (Aℓ * eB) := by gcongr
        _ = CQ * CS'' * Aℓ * eB := by ring
    · -- singular: `CQ‖x‖^ℓ·2|S'|/‖x‖ ≤ CQ·2·CS'·Aℓ·(eB/‖x‖)`
      calc CQ * ‖x‖ ^ ℓ * (2 * |deriv (reducedRadialProfile n ℓ hn) ‖x‖| / ‖x‖)
          ≤ CQ * ‖x‖ ^ ℓ * (2 * (CS' * eA) / ‖x‖) := by
            gcongr
            exact hCS' ‖x‖ (norm_nonneg x)
        _ = CQ * 2 * CS' * (‖x‖ ^ ℓ * eA) * (1 / ‖x‖) := by rw [heA]; ring
        _ ≤ CQ * 2 * CS' * (Aℓ * eB) * (1 / ‖x‖) := by gcongr
        _ = CQ * 2 * CS' * Aℓ * (eB / ‖x‖) := by ring
  -- term-4: `|S'|·‖DQ‖ ≤ CS'eA · CdQ‖x‖^{ℓ-1} ≤ CS'·CdQ·Aℓ1·eB`
  have hT4 : |deriv (reducedRadialProfile n ℓ hn) ‖x‖| * ‖fderiv ℝ (solidHarmonicNat ℓ m) x‖
      ≤ CS' * CdQ * Aℓ1 * eB := by
    calc |deriv (reducedRadialProfile n ℓ hn) ‖x‖| * ‖fderiv ℝ (solidHarmonicNat ℓ m) x‖
        ≤ (CS' * eA) * (CdQ * ‖x‖ ^ (ℓ - 1)) :=
          mul_le_mul (hCS' ‖x‖ (norm_nonneg x)) (hCdQ x hx) (norm_nonneg _) (by positivity)
      _ = CS' * CdQ * (‖x‖ ^ (ℓ - 1) * eA) := by rw [heA]; ring
      _ ≤ CS' * CdQ * (Aℓ1 * eB) := by gcongr
      _ = CS' * CdQ * Aℓ1 * eB := by ring
  -- assemble
  calc |reducedRadialProfile n ℓ hn ‖x‖|
        * ‖fderiv ℝ (fun y => fderiv ℝ (solidHarmonicNat ℓ m) y (EuclideanSpace.single i 1)) x‖
      + ‖fderiv ℝ (solidHarmonicNat ℓ m) x (EuclideanSpace.single i 1)‖
        * |deriv (reducedRadialProfile n ℓ hn) ‖x‖|
      + ‖solidHarmonicNat ℓ m x‖
        * ‖fderiv ℝ (fun y => fderiv ℝ (fun z => reducedRadialProfileC n ℓ hn ‖z‖) y
            (EuclideanSpace.single i 1)) x‖
      + |deriv (reducedRadialProfile n ℓ hn) ‖x‖| * ‖fderiv ℝ (solidHarmonicNat ℓ m) x‖
      ≤ CS * Cd2Q * Aℓ1 * (eB / ‖x‖)
        + CS' * CdQ * Aℓ1 * eB
        + (CQ * CS'' * Aℓ * eB + CQ * 2 * CS' * Aℓ * (eB / ‖x‖))
        + CS' * CdQ * Aℓ1 * eB :=
        add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4
    _ = (CS' * CdQ * Aℓ1 + CQ * CS'' * Aℓ + CS' * CdQ * Aℓ1) * eB
        + (CS * Cd2Q * Aℓ1 + CQ * 2 * CS' * Aℓ) * (eB / ‖x‖) := by ring

/-! ### `L²`-membership of `Ψ`, `∂ᵢΨ`, `∂ⱼ∂ᵢΨ` -/

/-- `∂ᵢΨ` is `C¹` away from the origin. -/
lemma separated_first_deriv_contDiffOn (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (i : Fin 3) :
    ContDiffOn ℝ 1 (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1)) {(0 : Spectra.Sobolev.R3)}ᶜ := by
  intro x hx
  have hx' : x ≠ 0 := hx
  have hΨ2 : ContDiffAt ℝ 2 (separatedEigenfunction n ℓ m hn) x :=
    (separated_contDiffOn n ℓ m hn).contDiffAt (isOpen_compl_singleton.mem_nhds hx')
  exact (((hΨ2.fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := (EuclideanSpace.single i (1 : ℝ))))).contDiffWithinAt)

/-- `Ψ` is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_separated (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) :
    AEStronglyMeasurable (separatedEigenfunction n ℓ m hn) volume := by
  have hae : ∀ᵐ x : Spectra.Sobolev.R3, x ∈ ({(0 : Spectra.Sobolev.R3)}ᶜ : Set _) := by
    rw [ae_iff]; simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not,
      Set.setOf_eq_eq_singleton]
    exact measure_singleton 0
  have := (separated_continuousOn n ℓ m hn).aestronglyMeasurable (μ := volume)
    (measurableSet_singleton (0 : Spectra.Sobolev.R3)).compl
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

/-- `∂ᵢΨ` is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_separated_first (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (i : Fin 3) :
    AEStronglyMeasurable (fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x
        (EuclideanSpace.single i 1)) volume := by
  have hae : ∀ᵐ x : Spectra.Sobolev.R3, x ∈ ({(0 : Spectra.Sobolev.R3)}ᶜ : Set _) := by
    rw [ae_iff]; simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not,
      Set.setOf_eq_eq_singleton]
    exact measure_singleton 0
  have := (separated_first_deriv_contDiffOn n ℓ m hn i).continuousOn.aestronglyMeasurable
    (μ := volume) (measurableSet_singleton (0 : Spectra.Sobolev.R3)).compl
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

/-- `∂ⱼ∂ᵢΨ` is a.e.-strongly-measurable. -/
lemma aestronglyMeasurable_separated_second (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (i j : Fin 3) :
    AEStronglyMeasurable (fun x => fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)) volume := by
  have hae : ∀ᵐ x : Spectra.Sobolev.R3, x ∈ ({(0 : Spectra.Sobolev.R3)}ᶜ : Set _) := by
    rw [ae_iff]; simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not,
      Set.setOf_eq_eq_singleton]
    exact measure_singleton 0
  have hcont : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      {(0 : Spectra.Sobolev.R3)}ᶜ := by
    intro x hx
    have hx' : x ≠ 0 := hx
    have hdf1 : ContDiffAt ℝ 1 (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1)) x :=
      (separated_first_deriv_contDiffOn n ℓ m hn i).contDiffAt
        (isOpen_compl_singleton.mem_nhds hx')
    have hcaf : ContinuousAt (fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1))) x := hdf1.continuousAt_fderiv one_ne_zero
    exact (((ContinuousLinearMap.apply ℝ ℂ
      (EuclideanSpace.single j (1 : ℝ))).continuous.continuousAt).comp hcaf).continuousWithinAt
  have := hcont.aestronglyMeasurable (μ := volume)
    (measurableSet_singleton (0 : Spectra.Sobolev.R3)).compl
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at this

/-- **`Ψ ∈ L²`.** -/
lemma memLp_separated (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ) :
    MemLp (separatedEigenfunction n ℓ m hn) 2 volume := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨C, hC0, hC⟩ := norm_separated_le_exp n ℓ m hn hm
  refine memLp_two_of_le_exp (aestronglyMeasurable_separated n ℓ m hn)
    (C := max ‖separatedEigenfunction n ℓ m hn 0‖ C) (a := 1 / (4 * (n:ℝ)))
    (by positivity) (fun x => ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, mul_zero, Real.exp_zero, mul_one]; exact le_max_left _ _
  · exact le_trans (hC x hx) (by gcongr; exact le_max_right _ _)

/-- **`∂ᵢΨ ∈ L²`.** -/
lemma memLp_separated_first (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ) (i : Fin 3) :
    MemLp (fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1))
      2 volume := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨C, hC0, hC⟩ := norm_fderiv_separated_le_exp n ℓ m hn hm hℓ i
  set D : Spectra.Sobolev.R3 → ℂ :=
    fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1) with hD
  refine memLp_two_of_le_exp (aestronglyMeasurable_separated_first n ℓ m hn i)
    (C := max ‖D 0‖ C) (a := 1 / (4 * (n:ℝ))) (by positivity) (fun x => ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [hD, norm_zero, mul_zero, Real.exp_zero, mul_one]; exact le_max_left _ _
  · exact le_trans (hC x hx) (by gcongr; exact le_max_right _ _)

/-- **`∂ⱼ∂ᵢΨ ∈ L²`** (the `1/‖x‖` singularity at the origin is `L²` in `ℝ³`). -/
lemma memLp_separated_second (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ) (i j : Fin 3) :
    MemLp (fun x => fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)) 2 volume := by
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨C, C', hC0, hC'0, hC⟩ := norm_fderiv2_separated_le_exp n ℓ m hn hm hℓ i j
  set D : Spectra.Sobolev.R3 → ℂ :=
    fun x => fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) with hD
  refine memLp_two_of_le_exp_add_div (aestronglyMeasurable_separated_second n ℓ m hn i j)
    (C := max ‖D 0‖ C) (C' := C') (a := 1 / (4 * (n:ℝ))) (by positivity) (fun x => ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [hD, norm_zero, mul_zero, Real.exp_zero, mul_one, div_zero, add_zero]
    exact le_max_left _ _
  · refine le_trans (hC x hx) ?_
    gcongr
    exact le_max_right _ _

/-! ### Near-origin boundedness and integrability against test functions

The `master_ibp` integration by parts needs `v` (`= Ψ` resp. `∂ᵢΨ`) bounded near the origin and
the products `v·∂ⱼφ`, `w·φ` integrable.  Boundedness near `0` comes from the exponential bounds
(`≤ C` for `x ≠ 0`); integrability comes from Hölder (`L²·L²⊆L¹`), since all factors are `L²`. -/

/-- `Ψ` is bounded by `max ‖Ψ 0‖ C` on `{‖x‖ ≤ 1}` (`ℓ ≥ 1`). -/
lemma separated_bounded_near_zero (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) :
    ∃ Mv : ℝ, 0 ≤ Mv ∧ ∀ x : Spectra.Sobolev.R3, ‖x‖ ≤ 1 →
      ‖separatedEigenfunction n ℓ m hn x‖ ≤ Mv := by
  obtain ⟨C, hC0, hC⟩ := norm_separated_le_exp n ℓ m hn hm
  refine ⟨max ‖separatedEigenfunction n ℓ m hn 0‖ C, le_trans (norm_nonneg _) (le_max_left _ _),
    fun x _ => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact le_max_left _ _
  · refine le_trans (hC x hx) ?_
    calc C * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) ≤ C * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by
            have : (0:ℝ) ≤ 1 / (4 * (n:ℝ)) * ‖x‖ := by positivity
            linarith)
      _ = C := mul_one C
      _ ≤ _ := le_max_right _ _

/-- `∂ᵢΨ` is bounded by `max ‖∂ᵢΨ 0‖ C` on `{‖x‖ ≤ 1}` (`ℓ ≥ 1`). -/
lemma separated_first_bounded_near_zero (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ)
    (i : Fin 3) :
    ∃ Mv : ℝ, 0 ≤ Mv ∧ ∀ x : Spectra.Sobolev.R3, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1)‖ ≤ Mv := by
  obtain ⟨C, hC0, hC⟩ := norm_fderiv_separated_le_exp n ℓ m hn hm hℓ i
  set D : Spectra.Sobolev.R3 → ℂ :=
    fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1) with hD
  refine ⟨max ‖D 0‖ C, le_trans (norm_nonneg _) (le_max_left _ _), fun x _ => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact le_max_left _ _
  · refine le_trans (hC x hx) ?_
    calc C * Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) ≤ C * 1 := by
          gcongr; exact Real.exp_le_one_iff.mpr (by
            have : (0:ℝ) ≤ 1 / (4 * (n:ℝ)) * ‖x‖ := by positivity
            linarith)
      _ = C := mul_one C
      _ ≤ _ := le_max_right _ _

/-- A smooth compactly supported function (and its `j`-partial) is `L²`. -/
lemma memLp_test_partial {φ : Spectra.Sobolev.R3 → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (j : Fin 3) :
    MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) 2 volume := by
  have hcont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (hφ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hcs : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  exact hcont.memLp_of_hasCompactSupport (μ := volume) hcs

/-! ### The separated weak derivatives -/

/-- **First weak derivative of the separated eigenfunction.**  For `Ψ` realized as the `L²`
element `(memLp_separated …).toLp`, the classical `i`-partial `∂ᵢΨ` (itself `L²`) is its weak
`i`-derivative. -/
lemma hasWeakDerivative_separated_first (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ)
    (i : Fin 3) :
    Spectra.Sobolev.HasWeakDerivative ((memLp_separated n ℓ m hn hm hℓ).toLp _) i
      ((memLp_separated_first n ℓ m hn hm hℓ i).toLp _) := by
  intro φ hφ hφc
  -- `L²` representatives
  have hΨ : ⇑((memLp_separated n ℓ m hn hm hℓ).toLp _) =ᵐ[volume]
      separatedEigenfunction n ℓ m hn := (memLp_separated n ℓ m hn hm hℓ).coeFn_toLp
  have hd1 : ⇑((memLp_separated_first n ℓ m hn hm hℓ i).toLp _) =ᵐ[volume]
      fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1) :=
    (memLp_separated_first n ℓ m hn hm hℓ i).coeFn_toLp
  -- near-origin bound and integrability data
  obtain ⟨Mv, hMv0, hMv⟩ := separated_bounded_near_zero n ℓ m hn hm
  have hvφ : Integrable (fun x => separatedEigenfunction n ℓ m hn x
      * fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (memLp_separated n ℓ m hn hm hℓ).integrable_mul (memLp_test_partial hφ hφc i)
  have hwφ : Integrable (fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x
      (EuclideanSpace.single i 1) * φ x) :=
    (memLp_separated_first n ℓ m hn hm hℓ i).integrable_mul
      (q := 2) (hφ.continuous.memLp_of_hasCompactSupport (μ := volume) hφc)
  have hIBP := master_ibp i (separated_continuousOn n ℓ m hn)
    ((separated_contDiffOn n ℓ m hn).of_le (by norm_num)) (fun x _ => rfl)
    one_pos hMv hMv0 hφ hφc hvφ hwφ
  calc ∫ x, ((memLp_separated n ℓ m hn hm hℓ).toLp _) x
        * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, separatedEigenfunction n ℓ m hn x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
        refine integral_congr_ae ?_; filter_upwards [hΨ] with x hx; rw [hx]
    _ = - ∫ x, fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1) * φ x :=
        hIBP
    _ = - ∫ x, ((memLp_separated_first n ℓ m hn hm hℓ i).toLp _) x * φ x := by
        congr 1; refine integral_congr_ae ?_; filter_upwards [hd1] with x hx; rw [hx]

/-- **Second weak derivative of the separated eigenfunction.**  The classical mixed second
partial `∂ⱼ∂ᵢΨ` (itself `L²`, the `1/‖x‖` singularity being `L²` in `ℝ³`) is the weak
`j`-derivative of the `L²` element representing `∂ᵢΨ`. -/
lemma hasWeakDerivative_separated_second (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ)
    (i j : Fin 3) :
    Spectra.Sobolev.HasWeakDerivative ((memLp_separated_first n ℓ m hn hm hℓ i).toLp _) j
      ((memLp_separated_second n ℓ m hn hm hℓ i j).toLp _) := by
  intro φ hφ hφc
  have hd1 : ⇑((memLp_separated_first n ℓ m hn hm hℓ i).toLp _) =ᵐ[volume]
      fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1) :=
    (memLp_separated_first n ℓ m hn hm hℓ i).coeFn_toLp
  have hd2 : ⇑((memLp_separated_second n ℓ m hn hm hℓ i j).toLp _) =ᵐ[volume]
      fun x => fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) :=
    (memLp_separated_second n ℓ m hn hm hℓ i j).coeFn_toLp
  obtain ⟨Mv, hMv0, hMv⟩ := separated_first_bounded_near_zero n ℓ m hn hm hℓ i
  have hvφ : Integrable (fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x
      (EuclideanSpace.single i 1) * fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (memLp_separated_first n ℓ m hn hm hℓ i).integrable_mul (memLp_test_partial hφ hφc j)
  have hwφ : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) * φ x) :=
    (memLp_separated_second n ℓ m hn hm hℓ i j).integrable_mul
      (q := 2) (hφ.continuous.memLp_of_hasCompactSupport (μ := volume) hφc)
  have hIBP := master_ibp j (separated_first_deriv_contDiffOn n ℓ m hn i).continuousOn
    (separated_first_deriv_contDiffOn n ℓ m hn i) (fun x _ => rfl)
    one_pos hMv hMv0 hφ hφc hvφ hwφ
  calc ∫ x, ((memLp_separated_first n ℓ m hn hm hℓ i).toLp _) x
        * fderiv ℝ φ x (EuclideanSpace.single j 1)
      = ∫ x, fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1)
          * fderiv ℝ φ x (EuclideanSpace.single j 1) := by
        refine integral_congr_ae ?_; filter_upwards [hd1] with x hx; rw [hx]
    _ = - ∫ x, fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) * φ x := hIBP
    _ = - ∫ x, ((memLp_separated_second n ℓ m hn hm hℓ i j).toLp _) x * φ x := by
        congr 1; refine integral_congr_ae ?_; filter_upwards [hd2] with x hx; rw [hx]

/-! ## H1e — the a.e. eigen-equation and the final assembly

The classical eigen-equation `separated_eigen_chart` holds only at interior chart points
`sphereChart r θ φ` (`r > 0`, `θ ∈ (0,π)`), i.e. off the null `x₁ = 0` hyperplane.  Because that
exceptional set is `volume`-null in `ℝ³`, the eigen-equation holds `volume`-a.e., which is all the
weak Laplacian needs. -/

/-- `WithLp.ofLp` (`= toLp.symm`) is `volume`-preserving from `R3` onto `Fin 3 → ℝ` (with the
repo's `borel R3` instances).  Mirror of `Decomposition.measurePreserving_toLp_R3`. -/
private lemma measurePreserving_ofLp_R3 :
    MeasurePreserving (WithLp.ofLp : Spectra.Sobolev.R3 → (Fin 3 → ℝ))
      (volume : Measure Spectra.Sobolev.R3) (volume : Measure (Fin 3 → ℝ)) := by
  have htoLp := Spectra.QuantumMechanics.Hydrogen.Decomposition.measurePreserving_toLp_R3
  have hmeas : Measurable (WithLp.ofLp : Spectra.Sobolev.R3 → (Fin 3 → ℝ)) :=
    (PiLp.continuous_ofLp 2 _).measurable
  refine ⟨hmeas, ?_⟩
  rw [← htoLp.map_eq, Measure.map_map hmeas
    (PiLp.continuous_toLp 2 _).measurable]
  simp [Function.comp_def]

/-- **A.e. chart coverage.**  For `volume`-a.e. `x : ℝ³` there exist spherical coordinates
`(r, θ, φ)` with `r > 0`, `θ ∈ (0, π)` and `x = sphereChart r θ φ`.  (The exceptional set is the
null `x₁ = 0` hyperplane.)  Pushed forward from `sphereCoordSymmF_image_ae_univ`. -/
lemma ae_exists_sphereChart :
    ∀ᵐ x : Spectra.Sobolev.R3,
      ∃ r θ φ : ℝ, 0 < r ∧ θ ∈ Set.Ioo 0 Real.pi ∧ x = sphereChart r θ φ := by
  have hnull : (volume : Measure (Fin 3 → ℝ))
      (Spectra.QuantumMechanics.Hydrogen.Decomposition.sphereCoordSymmF ''
        Spectra.QuantumMechanics.Hydrogen.Decomposition.chartBox)ᶜ = 0 :=
    (ae_eq_univ.mp Spectra.QuantumMechanics.Hydrogen.Decomposition.sphereCoordSymmF_image_ae_univ)
  have hmemb : ∀ᵐ y : (Fin 3 → ℝ), y ∈
      Spectra.QuantumMechanics.Hydrogen.Decomposition.sphereCoordSymmF ''
        Spectra.QuantumMechanics.Hydrogen.Decomposition.chartBox := by
    rw [ae_iff]
    refine measure_mono_null (fun a ha => ?_) hnull
    simpa [Set.mem_compl_iff] using ha
  -- the preimage under the measure-preserving `ofLp` is null in `R3`
  have hae : ∀ᵐ x : Spectra.Sobolev.R3, (WithLp.ofLp x : Fin 3 → ℝ) ∈
      Spectra.QuantumMechanics.Hydrogen.Decomposition.sphereCoordSymmF ''
        Spectra.QuantumMechanics.Hydrogen.Decomposition.chartBox :=
    measurePreserving_ofLp_R3.quasiMeasurePreserving.ae hmemb
  filter_upwards [hae] with x hx
  obtain ⟨c, hc, hcx⟩ := hx
  refine ⟨c 0, c 1, c 2, hc.1, hc.2.1, ?_⟩
  rw [← Spectra.QuantumMechanics.Hydrogen.Decomposition.toLp_sphereCoordSymmF, hcx,
    WithLp.toLp_ofLp]

/-- **The separated eigenfunction solves the eigen-equation `volume`-a.e.** (`Z = 1`):
`Σⱼ ∂ⱼ²Ψ_{nℓm}(x) = −2·(Eₙ + 1/‖x‖)·Ψ_{nℓm}(x)` for `volume`-a.e. `x`.  Built from the chart
identity `separated_eigen_chart` and the a.e. chart coverage `ae_exists_sphereChart`. -/
lemma separated_eigen_ae (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) :
    ∀ᵐ x : Spectra.Sobolev.R3,
      ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
          (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1)
        = (-2 : ℂ) * ((hydrogenEigenvalue n (by omega) : ℂ) + (‖x‖ : ℂ)⁻¹)
          * separatedEigenfunction n ℓ m hn x := by
  filter_upwards [ae_exists_sphereChart] with x hx
  obtain ⟨r, θ, φ, hr, hθ, rfl⟩ := hx
  exact separated_eigen_chart n ℓ m hn hm hr hθ

/-- **The spherical harmonic is invariant under the inverse chart round-trip.**  For
`r > 0` and `θ ∈ (0, π)` the angular coordinates `(sphereChartInv (sphereChart r θ φ)).2`
recover `θ` exactly in the polar slot and `φ` *modulo `2π`* in the azimuthal slot; since
`Y_ℓ^m ∝ e^{imφ}` is `2π`-periodic in `φ`, its value is unchanged. -/
lemma sphericalHarmonic_sphereChartInv_eq (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ (ℓ : ℤ))
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    SphericalHarmonic ℓ m hm (sphereChartInv (sphereChart r θ φ)).2
      = SphericalHarmonic ℓ m hm (θ, φ) := by
  -- the cartesian coordinates of the chart point
  have hofLp : (WithLp.ofLp (sphereChart r θ φ) : Fin 3 → ℝ)
      = sphereCoordSymmF ![r, θ, φ] := by
    rw [show sphereChart r θ φ = WithLp.toLp 2 (sphereCoordSymmF ![r, θ, φ])
      from (toLp_sphereCoordSymmF ![r, θ, φ]).symm, WithLp.ofLp_toLp]
  set y : Fin 3 → ℝ := sphereCoordSymmF ![r, θ, φ] with hy
  have hidx : (![r, θ, φ] : Fin 3 → ℝ) 0 = r ∧ (![r, θ, φ] : Fin 3 → ℝ) 1 = θ
      ∧ (![r, θ, φ] : Fin 3 → ℝ) 2 = φ := by
    refine ⟨rfl, rfl, ?_⟩
    show (![r, θ, φ] : Fin 3 → ℝ) 2 = φ
    rfl
  have hy0 : y 0 = r * Real.sin θ * Real.cos φ := by
    rw [hy, sphereCoordSymmF_zero, hidx.1, hidx.2.1, hidx.2.2]
  have hy1 : y 1 = r * Real.sin θ * Real.sin φ := by
    rw [hy, sphereCoordSymmF_one, hidx.1, hidx.2.1, hidx.2.2]
  have hy2 : y 2 = r * Real.cos θ := by
    rw [hy, sphereCoordSymmF_two, hidx.1, hidx.2.1]
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  -- radial coordinate of the inverse chart
  have hrad : Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2) = r := by
    rw [hy0, hy1, hy2]
    rw [show (r * Real.sin θ * Real.cos φ) ^ 2 + (r * Real.sin θ * Real.sin φ) ^ 2
        + (r * Real.cos θ) ^ 2 = r ^ 2 by
      have h1 := Real.sin_sq_add_cos_sq φ
      have h2 := Real.sin_sq_add_cos_sq θ
      linear_combination (r ^ 2 * Real.sin θ ^ 2) * h1 + r ^ 2 * h2]
    exact Real.sqrt_sq hr.le
  -- the inverse chart's angular coordinates
  have hchartInv : sphereChartInv (sphereChart r θ φ)
      = (r, Real.arccos (y 2 / r),
          if 0 < y 1 then Complex.arg ⟨y 0, y 1⟩
            else Complex.arg ⟨y 0, y 1⟩ + 2 * Real.pi) := by
    rw [sphereChartInv, hofLp, sphereCoordSymmInvF, reshuffle_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    rw [hrad]
  -- polar slot: `arccos(cos θ) = θ`
  have hpolar : (sphereChartInv (sphereChart r θ φ)).2.1 = θ := by
    rw [hchartInv]
    simp only
    rw [hy2, mul_div_cancel_left₀ _ hr.ne', Real.arccos_cos hθ.1.le hθ.2.le]
  -- the complex number `⟨y 0, y 1⟩ = (r·sin θ)·(cos φ + sin φ·I)`, a positive multiple of `e^{iφ}`
  have hz : (⟨y 0, y 1⟩ : ℂ)
      = ((r * Real.sin θ : ℝ) : ℂ) * (Complex.cos (φ : ℂ) + Complex.sin (φ : ℂ) * Complex.I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext <;>
      simp only [hy0, hy1, Complex.ofReal_mul, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  have hrs : 0 < r * Real.sin θ := mul_pos hr hsinθ
  -- the azimuthal slot differs from `φ` by an integer multiple of `2π`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (sphereChartInv (sphereChart r θ φ)).2.2 = φ + 2 * Real.pi * k := by
    rw [hchartInv]
    simp only
    have hsub := Complex.arg_mul_cos_add_sin_mul_I_sub hrs φ
    rw [← hz] at hsub
    have harg : Complex.arg ⟨y 0, y 1⟩ = φ + 2 * Real.pi * ⌊(Real.pi - φ) / (2 * Real.pi)⌋ := by
      linarith [hsub]
    by_cases hpos : 0 < y 1
    · rw [if_pos hpos]
      exact ⟨⌊(Real.pi - φ) / (2 * Real.pi)⌋, harg⟩
    · rw [if_neg hpos]
      refine ⟨⌊(Real.pi - φ) / (2 * Real.pi)⌋ + 1, ?_⟩
      rw [harg]; push_cast; ring
  -- assemble: `cos` of the polar slot is `cos θ`; `e^{im·azimuth} = e^{imφ}`
  set q : ℝ × ℝ := (sphereChartInv (sphereChart r θ φ)).2 with hq
  have hqeq : q = (q.1, q.2) := rfl
  rw [hqeq, hpolar, hk, sphericalHarmonic_eq, sphericalHarmonic_eq]
  congr 1
  rw [show I * (m : ℂ) * ((φ + 2 * Real.pi * k : ℝ) : ℂ)
      = I * (m : ℂ) * (φ : ℂ) + (m * k : ℤ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## Identifying the separated eigenfunction with the spherical eigenfunction

`hydrogenEigenfunction n ℓ ↑m hn hm'` lives on the *spherical* `L²` side
(`Decomposition.L2_R3`).  Transporting it back to Cartesian `L²(ℝ³)` through the chart
unitary `chartRealization.symm` produces exactly the separated product
`separatedEigenfunction n ℓ m hn`.  This is the bridge that turns the genuine eigenvector
`hydrogenEigenfunction` into the concrete Cartesian witness and conversely. -/

/-- **General-ℓ spherical coefficient of the eigenfunction.**  On the spherical side the
eigenfunction is a.e. the pure tensor `(r, ω) ↦ R_{nℓ}(r)·Y_ℓ^m(ω)`.  Mirror of the
`ℓ = 0` `eigenfunction_sph_coeFn`, for general `ℓ, m`. -/
lemma eigenfunction_sph_coeFn_gen (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm' : |(m : ℤ)| ≤ (ℓ : ℤ)) :
    ⇑(hydrogenEigenfunction n ℓ (m : ℤ) hn hm')
      =ᵐ[radialMeasure.prod sphereMeasure]
      tensorFun (Rc n ℓ hn) ⟨ℓ, ⟨(m : ℤ), hm'⟩⟩ := by
  have hsec := sectorEmbedding_coeFn ⟨ℓ, ⟨(m : ℤ), hm'⟩⟩ (radialLp n ℓ hn)
  have hrad := (Measure.quasiMeasurePreserving_fst (μ := radialMeasure)
    (ν := sphereMeasure)).ae_eq_comp (radialLp_coeFn n ℓ hn)
  filter_upwards [hsec, hrad] with p hp hr
  simp only [hydrogenEigenfunction]
  rw [hp]
  simp only [tensorFun]
  simp only [Function.comp_apply] at hr
  rw [hr]
  rfl

/-- **The separated eigenfunction, pulled back through the chart, is the same pure tensor.**
For a chart point `sphereChart r θ φ` (interior of the box) the Cartesian separated product
equals `R_{nℓ}(r)·Y_ℓ^m(θ,φ) = tensorFun (Rc n ℓ hn) ⟨ℓ,⟨m,hm'⟩⟩ (r,(θ,φ))`. -/
lemma separated_sphereChart_eq (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ)
    (hm' : |(m : ℤ)| ≤ (ℓ : ℤ)) {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    separatedEigenfunction n ℓ m hn (sphereChart r θ φ)
      = tensorFun (Rc n ℓ hn) ⟨ℓ, ⟨(m : ℤ), hm'⟩⟩ (r, (θ, φ)) := by
  have hnorm : ‖sphereChart r θ φ‖ = r := by rw [norm_sphereChart, abs_of_pos hr]
  have hharm : harmonic ⟨ℓ, ⟨(m : ℤ), hm'⟩⟩ = SphericalHarmonic ℓ (m : ℤ) hm' := rfl
  have hRpow : hydrogenRadialWavefunction n ℓ hn r = r ^ ℓ * reducedRadialProfile n ℓ hn r :=
    hydrogenRadial_eq_pow_mul_reduced n ℓ hn r
  simp only [tensorFun, hharm]
  rw [separatedEigenfunction, reducedRadialProfileC, hnorm,
    solidHarmonicNat_sphereChart ℓ m hm hr hθ]
  simp only [Rc, hRpow]
  push_cast; ring

/-- **The Cartesian transport of the spherical eigenfunction is the separated product.**
`chartRealization.symm (hydrogenEigenfunction n ℓ ↑m hn hm') =ᵐ[volume] separatedEigenfunction`.
This is the workhorse identifying the abstract spherical eigenvector with the concrete
Cartesian `H²` witness. -/
lemma chartRealization_symm_eigenfunction_eq_separated (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n)
    (hm : m ≤ ℓ) (hm' : |(m : ℤ)| ≤ (ℓ : ℤ)) :
    ⇑(chartRealization.symm (hydrogenEigenfunction n ℓ (m : ℤ) hn hm'))
      =ᵐ[volume] separatedEigenfunction n ℓ m hn := by
  -- the chart unitary's coeFn is the spherical eigenfunction precomposed with `sphereChartInv`
  have hsymm := chartRealization_symm_coeFn (hydrogenEigenfunction n ℓ (m : ℤ) hn hm')
  -- push the spherical-coeFn through `sphereChartInv` (volume-quasi-measure-preserving)
  have htrans := (measurePreserving_sphereChartInv.quasiMeasurePreserving).ae_eq_comp
    (eigenfunction_sph_coeFn_gen n ℓ m hn hm')
  -- a.e. every `x` is `sphereChart r θ φ` for interior `(r, θ)`
  filter_upwards [hsymm, htrans, ae_exists_sphereChart] with x hx ht hxchart
  rw [hx]
  simp only [Function.comp_apply] at ht
  rw [ht]
  obtain ⟨r, θ, φ, hr, hθ, rfl⟩ := hxchart
  -- on a chart point both sides equal `R_{nℓ}(r)·Y_ℓ^m(θ,φ)`
  rw [separated_sphereChart_eq n ℓ m hn hm hm' hr hθ]
  -- the inverse chart's radial coordinate is the norm `= r`; the angular part agrees mod 2π
  have hnorm : ‖sphereChart r θ φ‖ = r := by rw [norm_sphereChart, abs_of_pos hr]
  have hharm : harmonic ⟨ℓ, ⟨(m : ℤ), hm'⟩⟩ = SphericalHarmonic ℓ (m : ℤ) hm' := rfl
  simp only [tensorFun, hharm]
  rw [sphereChartInv_fst, hnorm]
  -- the angular coordinate of `sphereChartInv (sphereChart r θ φ)` differs from `(θ, φ)` only
  -- by an integer multiple of `2π` in `φ`, on which `Y_ℓ^m` (`∝ e^{imφ}`) is invariant
  congr 1
  exact sphericalHarmonic_sphereChartInv_eq ℓ (m : ℤ) hm' hr hθ

/-- **General-ℓ hydrogen bound state at `Z = 1`** (reverse direction of the discrete spectrum, all
`1 ≤ ℓ < n`, `|m| ≤ ℓ`).  The *separated* eigenfunction `Ψ_{nℓm} = S_{nℓ}(‖·‖)·solidHarmonicNat ℓ m`
is a genuine `H²` eigenvector of the Cartesian hydrogen Hamiltonian `H = −½Δ − 1/r` at eigenvalue
`Eₙ = −1/(2n²)`. -/
theorem hydrogen_bound_state_separated (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ) (hℓ : 1 ≤ ℓ) :
    ∃ ψ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain,
      (ψ : Spectra.Sobolev.L2_R3) ≠ 0 ∧
      (⇑(ψ : Spectra.Sobolev.L2_R3) =ᵐ[volume] separatedEigenfunction n ℓ m hn) ∧
      hydrogenHamiltonian ⟨1, one_pos⟩ ψ
        = ((hydrogenEigenvalue n (by omega) : ℝ) : ℂ) • (ψ : Spectra.Sobolev.L2_R3) := by
  classical
  set p : CoulombParams := ⟨1, one_pos⟩ with hp
  set E : ℝ := hydrogenEigenvalue n (by omega) with hE_def
  set Ψ : Spectra.Sobolev.L2_R3 := (memLp_separated n ℓ m hn hm hℓ).toLp _ with hΨ_def
  have hΨ : ⇑Ψ =ᵐ[volume] separatedEigenfunction n ℓ m hn :=
    (memLp_separated n ℓ m hn hm hℓ).coeFn_toLp
  -- abbreviations for the classical second partials (the L² witnesses)
  set d2 : Fin 3 → Fin 3 → Spectra.Sobolev.L2_R3 :=
    fun i j => (memLp_separated_second n ℓ m hn hm hℓ i j).toLp _ with hd2_def
  -- `Ψ ∈ H²` from the separated weak-derivative stack
  have hH2 : MemSobolevH2 Ψ := by
    refine ⟨fun i => ⟨(memLp_separated_first n ℓ m hn hm hℓ i).toLp _,
      hasWeakDerivative_separated_first n ℓ m hn hm hℓ i⟩, fun i j => ?_⟩
    exact ⟨d2 i j, (memLp_separated_first n ℓ m hn hm hℓ i).toLp _,
      hasWeakDerivative_separated_first n ℓ m hn hm hℓ i,
      hasWeakDerivative_separated_second n ℓ m hn hm hℓ i j⟩
  -- nonzero: if `Ψ = 0` then `Ψ` agrees a.e. (hence everywhere off `0`, by continuity) with `0`,
  -- so `R_{nℓ}(r)·Yℓᵐ(θ,φ) = 0` at every chart point; but `R` is nonzero somewhere (its
  -- `L²(r²dr)` norm is `1`), forcing `Y ≡ 0` on the box, contradicting `‖Y‖ = 1`.
  have hm' : |(m : ℤ)| ≤ (ℓ : ℤ) := by simpa using hm
  have hΨ0 : Ψ ≠ 0 := by
    intro h0
    have hae0 : separatedEigenfunction n ℓ m hn =ᵐ[volume] (0 : Spectra.Sobolev.R3 → ℂ) := by
      refine hΨ.symm.trans ?_; rw [h0]; exact Lp.coeFn_zero _ _ _
    -- agreement on the open set `{0}ᶜ` forces pointwise vanishing of the continuous `Ψ` there
    have heqOn : Set.EqOn (separatedEigenfunction n ℓ m hn) (0 : Spectra.Sobolev.R3 → ℂ)
        {(0 : Spectra.Sobolev.R3)}ᶜ :=
      eqOn_open_of_ae_eq (ae_restrict_of_ae hae0) isOpen_compl_singleton
        (separated_continuousOn n ℓ m hn) continuousOn_const
    -- the chart-point identity `Ψ(sphereChart r θ φ) = R_{nℓ}(r)·Yℓᵐ(θ,φ)`
    have hchart : ∀ r θ φ : ℝ, 0 < r → θ ∈ Set.Ioo 0 Real.pi →
        separatedEigenfunction n ℓ m hn (sphereChart r θ φ)
          = (hydrogenRadialWavefunction n ℓ hn r : ℂ) * SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) := by
      intro r θ φ hr hθ
      have hnorm : ‖sphereChart r θ φ‖ = r := by rw [norm_sphereChart, abs_of_pos hr]
      rw [separatedEigenfunction, reducedRadialProfileC, hnorm,
        solidHarmonicNat_sphereChart ℓ m hm hr hθ,
        hydrogenRadial_eq_pow_mul_reduced n ℓ hn]
      push_cast; ring
    -- every chart point is off the origin, so `R(r)·Y(θ,φ) = 0`
    have hRY : ∀ r θ φ : ℝ, 0 < r → θ ∈ Set.Ioo 0 Real.pi →
        (hydrogenRadialWavefunction n ℓ hn r : ℂ) * SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) = 0 := by
      intro r θ φ hr hθ
      have hne : sphereChart r θ φ ≠ 0 := by
        rw [← norm_ne_zero_iff, norm_sphereChart, abs_of_pos hr]; exact hr.ne'
      rw [← hchart r θ φ hr hθ]; exact heqOn hne
    -- `R` is nonzero somewhere: else its normalization integral would be `0 ≠ 1`
    obtain ⟨r₀, hr₀pos, hr₀ne⟩ : ∃ r > 0, hydrogenRadialWavefunction n ℓ hn r ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hz : ∫ r in Set.Ioi 0, hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2 = 0 := by
        rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
          (fun r hr => by rw [hcon r (Set.mem_Ioi.mp hr)]; ring)]
        simp
      rw [radial_wavefunction_norm] at hz; exact one_ne_zero hz
    -- hence `Y ≡ 0` on the open box `θ ∈ (0,π)`
    have hYzero : ∀ θ φ : ℝ, θ ∈ Set.Ioo 0 Real.pi → SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) = 0 := by
      intro θ φ hθ
      have := hRY r₀ θ φ hr₀pos hθ
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast h) hr₀ne
      · exact h
    -- contradiction with `∫∫ |Y|² sin θ = 1` (orthonormality)
    have horth := sphericalHarmonic_orthonormal ℓ ℓ (m : ℤ) (m : ℤ) hm' hm'
    simp only [and_self, if_true] at horth
    -- the inner `φ`-integral vanishes for every interior `θ`
    have hinner : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
        (∫ φ in (0:ℝ)..(2 * Real.pi),
          (starRingEnd ℂ) (SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ)) *
            SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) * (Real.sin θ : ℂ)) = 0 := by
      intro θ hθ
      rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
      rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
      · simp [← hθ0]
      rcases eq_or_lt_of_le hθ.2 with hθπ | hθπ
      · simp [hθπ]
      · have hfun : (fun φ => (starRingEnd ℂ) (SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ)) *
            SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) * (Real.sin θ : ℂ))
              = fun _ : ℝ => (0 : ℂ) := by
          funext φ; rw [hYzero θ φ ⟨hθ0, hθπ⟩]; ring
        rw [hfun, intervalIntegral.integral_zero]
    rw [intervalIntegral.integral_congr hinner] at horth
    simp at horth
  refine ⟨⟨Ψ, hH2⟩, hΨ0, hΨ, ?_⟩
  -- weak Laplacian collapses to `-∑ d2 i i`
  have hchoose : ∀ i : Fin 3, (hH2.2 i i).choose = d2 i i := by
    intro i
    exact hasWeakSecondDerivative_unique Ψ i i _ _ (hH2.2 i i).choose_spec
      ⟨(memLp_separated_first n ℓ m hn hm hℓ i).toLp _,
        hasWeakDerivative_separated_first n ℓ m hn hm hℓ i,
        hasWeakDerivative_separated_second n ℓ m hn hm hℓ i i⟩
  have hwL : weakLaplacian Ψ hH2 = -∑ i : Fin 3, d2 i i := by
    simp only [weakLaplacian]; rw [neg_inj]; exact Finset.sum_congr rfl (fun i _ => hchoose i)
  have hwL_coeFn : ⇑(weakLaplacian Ψ hH2) =ᵐ[volume]
      fun x => -∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
    have hc : ∀ i : Fin 3, ⇑(d2 i i) =ᵐ[volume]
        fun x => fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) :=
      fun i => (memLp_separated_second n ℓ m hn hm hℓ i i).coeFn_toLp
    rw [hwL, Fin.sum_univ_three]
    filter_upwards [Lp.coeFn_neg (d2 0 0 + d2 1 1 + d2 2 2),
      Lp.coeFn_add (d2 0 0 + d2 1 1) (d2 2 2), Lp.coeFn_add (d2 0 0) (d2 1 1),
      hc 0, hc 1, hc 2] with x hneg hadd2 hadd1 h0 h1 h2
    simp only [Fin.sum_univ_three, hneg, Pi.neg_apply, hadd2, hadd1, Pi.add_apply, h0, h1, h2]
  refine Lp.ext ?_
  have ehalf : ⇑(halfLaplacianPMap ⟨Ψ, hH2⟩) =ᵐ[volume]
      ((1 / 2 : ℝ) : ℂ) • ⇑(weakLaplacian Ψ hH2) := by
    rw [show halfLaplacianPMap ⟨Ψ, hH2⟩ = ((1 / 2 : ℝ) : ℂ) • weakLaplacian Ψ hH2 from by
      rw [halfLaplacianPMap_apply]; rfl]
    exact Lp.coeFn_smul _ _
  have ecoul : ⇑(coulombPotential p ⟨Ψ, hH2⟩) =ᵐ[volume]
      fun x => (coulombMultiplier p x : ℂ) * ⇑Ψ x :=
    (coulomb_mul_memLp_H2 p Ψ hH2).coeFn_toLp
  have eH : ⇑(hydrogenHamiltonian p ⟨Ψ, hH2⟩) =ᵐ[volume]
      fun x => ⇑(halfLaplacianPMap ⟨Ψ, hH2⟩) x + ⇑(coulombPotential p ⟨Ψ, hH2⟩) x := by
    rw [hydrogenHamiltonian_apply]; exact Lp.coeFn_add _ _
  have hae0 : ∀ᵐ x : Spectra.Sobolev.R3, x ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]; exact measure_singleton 0
  filter_upwards [eH, ehalf, ecoul, hwL_coeFn, Lp.coeFn_smul ((E : ℝ) : ℂ) Ψ, hΨ, hae0,
    separated_eigen_ae n ℓ m hn hm]
    with x heH hehalf hecoul hwLx hsmulE hΨfx hx0 heigx
  rw [heH, hehalf, hecoul, hsmulE, Pi.smul_apply, Pi.smul_apply, hwLx, hΨfx, smul_eq_mul,
    smul_eq_mul, heigx]
  have hcoulx : (coulombMultiplier p x : ℂ) = -(p.Z : ℂ) * (‖x‖ : ℂ)⁻¹ := by
    rw [coulombMultiplier, if_neg (by simpa using (norm_pos_iff.mpr hx0).ne')]
    push_cast; ring
  have hrne : (‖x‖ : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hx0)))
  have hZ1 : (p.Z : ℂ) = 1 := by rw [hp]; norm_num
  rw [hcoulx, hZ1]
  field_simp
  push_cast
  ring

/-! ## The degeneracy family transported to Cartesian `L²(ℝ³)` are genuine `H²` eigenvectors

We now assemble the reverse direction at the level of the *named* eigenfunctions
`hydrogenEigenfunction n ℓ m`: transported back to Cartesian `L²` via `chartRealization.symm`
each is a genuine `H²` eigenvector of the `Z = 1` hydrogen Hamiltonian at `Eₙ = −1/(2n²)`.
This holds for **every** `ℓ < n` and **every** `m ∈ {−ℓ,…,ℓ}` (including `m < 0`, handled by
the Condon–Shortley conjugation), and so for the whole `degenFamily n`. -/

/-- **Eigenpair transfer along an `L²` equality.**  If a domain element `ψ` is an eigenvector
at `E`, then any `L²` element equal to `↑ψ` is itself in the domain and an eigenvector at `E`. -/
lemma eigvec_transfer (p : CoulombParams) (E : ℝ) (w : Spectra.Sobolev.L2_R3)
    (ψ : (hydrogenHamiltonian p).domain) (hw : (ψ : Spectra.Sobolev.L2_R3) = w)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.L2_R3)) :
    ∃ hmem : w ∈ (hydrogenHamiltonian p).domain,
      hydrogenHamiltonian p ⟨w, hmem⟩ = (E : ℂ) • w := by
  refine ⟨hw ▸ ψ.2, ?_⟩
  have hψeq : (⟨w, hw ▸ ψ.2⟩ : (hydrogenHamiltonian p).domain) = ψ := Subtype.ext hw.symm
  rw [hψeq, heig, hw]

/-- **The `s`-state (`ℓ = 0`) transported eigenvector** at `Z = 1`.  `chartRealization.symm` of the
named `s`-state eigenfunction is a genuine `H²` eigenvector at `Eₙ`.  Built directly from the
abstract radial bound-state constructor `bound_state_of_radial_profile`. -/
lemma chartRealization_symm_sstate_eigenpair (n : ℕ) (hn : 1 ≤ n) (hm : |(0 : ℤ)| ≤ (0 : ℤ)) :
    ∃ hmem : chartRealization.symm (hydrogenEigenfunction n 0 0 (by omega) hm)
        ∈ (hydrogenHamiltonian ⟨1, one_pos⟩).domain,
      hydrogenHamiltonian ⟨1, one_pos⟩
          ⟨chartRealization.symm (hydrogenEigenfunction n 0 0 (by omega) hm), hmem⟩
        = ((hydrogenEigenvalue n hn : ℝ) : ℂ)
          • chartRealization.symm (hydrogenEigenfunction n 0 0 (by omega) hm) := by
  have hn0 : 0 + 1 ≤ n := by omega
  set c : ℂ := (sphericalNorm 0 0 : ℂ) with hc
  set g : ℝ → ℂ := fun r => c * Rc n 0 hn0 r with hg_def
  set a : ℝ := 1 / (2 * (n : ℝ)) with ha_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := by rw [ha_def]; positivity
  have hε : a < 1 / (n : ℝ) := by rw [ha_def, div_lt_div_iff₀ (by positivity) hnR]; nlinarith
  have hg : ContDiff ℝ 2 g := contDiff_const.mul (contDiff_Rc n 0 hn0)
  -- first-derivative decay bound
  obtain ⟨C₁, _, hC₁⟩ := exp_bound_of_tendsto
    ((contDiff_hydrogenRadial n 0 hn0).continuous_deriv (by norm_num))
    (tendsto_deriv_hydrogenRadial_mul_exp n 0 hn0 hε)
  -- `deriv g = c · deriv Rc`, `deriv (deriv g) = c · deriv (deriv Rc)`, both reduced to `R'`, `R''`.
  have hg_eq : g = fun s => c * Rc n 0 hn0 s := rfl
  have hderiv_g : deriv g = fun s => c * deriv (Rc n 0 hn0) s := by
    funext s
    rw [hg_eq, deriv_const_mul _ ((contDiff_Rc n 0 hn0).differentiable (by norm_num)).differentiableAt]
  have hderiv2_g : deriv (deriv g)
      = fun s => c * ((deriv (deriv (hydrogenRadialWavefunction n 0 hn0)) s : ℝ) : ℂ) := by
    funext s
    rw [hderiv_g,
      deriv_const_mul _ ((contDiff_Rc n 0 hn0).differentiable_deriv_two).differentiableAt,
      deriv2_Rc n 0 hn0]
  -- rewrite `deriv g` into the `ℝ→ℂ`-cast form (for the norm bound)
  have hderiv_g' : deriv g = fun s => c * ((deriv (hydrogenRadialWavefunction n 0 hn0) s : ℝ) : ℂ) := by
    rw [hderiv_g]; funext s; rw [deriv_Rc n 0 hn0]
  have hbd1 : ∀ r : ℝ, 0 ≤ r → ‖deriv g r‖ ≤ (|sphericalNorm 0 0| * C₁) * Real.exp (-a * r) := by
    intro r hr
    rw [hderiv_g']
    simp only [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |sphericalNorm 0 0| * |deriv (hydrogenRadialWavefunction n 0 hn0) r|
        ≤ |sphericalNorm 0 0| * (C₁ * Real.exp (-a * r)) := by gcongr; exact hC₁ r hr
      _ = |sphericalNorm 0 0| * C₁ * Real.exp (-a * r) := by ring
  -- second-derivative decay bound
  obtain ⟨C₂, _, hC₂⟩ := exp_bound_of_tendsto
    (((contDiff_hydrogenRadial n 0 hn0).deriv' (n := 1)).continuous_deriv (by norm_num))
    (tendsto_deriv2_hydrogenRadial_mul_exp n 0 hn0 hε)
  have hbd2 : ∀ r : ℝ, 0 ≤ r →
      ‖deriv (deriv g) r‖ ≤ (|sphericalNorm 0 0| * C₂) * Real.exp (-a * r) := by
    intro r hr
    rw [hderiv2_g]
    simp only [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |sphericalNorm 0 0| * |deriv (deriv (hydrogenRadialWavefunction n 0 hn0)) r|
        ≤ |sphericalNorm 0 0| * (C₂ * Real.exp (-a * r)) := by gcongr; exact hC₂ r hr
      _ = |sphericalNorm 0 0| * C₂ * Real.exp (-a * r) := by ring
  -- the transported s-state as the explicit `Ψ`
  set Ψ : Spectra.Sobolev.L2_R3 := chartRealization.symm (hydrogenEigenfunction n 0 0 hn0 hm)
    with hΨ_def
  have hΨ : ⇑Ψ =ᵐ[volume] fun x : R3 => g ‖x‖ :=
    chartRealization_symm_eigenfunction_coeFn n hn0 hm
  have hΨ0 : Ψ ≠ 0 := by
    intro h0
    have hae0 : (fun x : R3 => g ‖x‖) =ᵐ[volume] (0 : R3 → ℂ) := by
      refine hΨ.symm.trans ?_; rw [h0]; exact Lp.coeFn_zero _ _ _
    have heqOn : Set.EqOn (fun x : R3 => g ‖x‖) (0 : R3 → ℂ) {(0 : R3)}ᶜ :=
      eqOn_open_of_ae_eq (ae_restrict_of_ae hae0) isOpen_compl_singleton
        ((hg.continuous.comp continuous_norm).continuousOn) continuousOn_const
    -- `R_{n0}` nonzero somewhere ⟹ contradiction with `‖Ψ‖ = 1`
    obtain ⟨r₀, hr₀pos, hr₀ne⟩ : ∃ r > 0, hydrogenRadialWavefunction n 0 hn0 r ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hz : ∫ r in Set.Ioi 0, hydrogenRadialWavefunction n 0 hn0 r ^ 2 * r ^ 2 = 0 := by
        rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
          (fun r hr => by rw [hcon r (Set.mem_Ioi.mp hr)]; ring)]; simp
      rw [radial_wavefunction_norm] at hz; exact one_ne_zero hz
    have hx0 : (sphereChart r₀ (Real.pi / 2) 0) ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_sphereChart, abs_of_pos hr₀pos]; exact hr₀pos.ne'
    have hval := heqOn hx0
    simp only [Pi.zero_apply] at hval
    rw [hg_def, norm_sphereChart, abs_of_pos hr₀pos] at hval
    simp only [hc, Rc] at hval
    rcases mul_eq_zero.mp hval with h | h
    · exact (sphericalNorm_pos 0 0).ne' (by exact_mod_cast h)
    · exact hr₀ne (by exact_mod_cast h)
  -- the classical eigen-identity (`Z = 1`): `Σⱼ ∂ⱼ² g(‖x‖) = −2(Eₙ + 1/‖x‖) g(‖x‖)`
  have heigen : ∀ x : R3, x ≠ 0 →
      ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1)
        = (-2 : ℂ) * ((hydrogenEigenvalue n hn : ℂ) + (‖x‖ : ℂ)⁻¹) * g ‖x‖ := by
    intro x hx
    have h := sum_second_deriv_eigen n hn0 hx
    simp only [hg_def, hc]
    rw [h]
  -- assemble `Ψ ∈ H²` and the eigenpair *for the explicit `Ψ`* (mirrors `bound_state_of_radial_profile`)
  set p : CoulombParams := ⟨1, one_pos⟩ with hp
  set E : ℝ := hydrogenEigenvalue n hn with hE_def
  have heigen' : ∀ x : R3, x ≠ 0 →
      ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1)
        = (-2 : ℂ) * ((E : ℂ) + (p.Z : ℂ) * (‖x‖ : ℂ)⁻¹) * g ‖x‖ := by
    intro x hx
    have := heigen x hx
    simpa [hp, hE_def] using this
  set d2 : Fin 3 → Fin 3 → Spectra.Sobolev.L2_R3 :=
    fun i j => (memLp_second_deriv g hg ha hbd1 hbd2 i j).toLp _ with hd2_def
  have hH2 : MemSobolevH2 Ψ := by
    refine ⟨fun i => ⟨(memLp_first_deriv g hg ha hbd1 i).toLp _,
      hasWeakDerivative_radial_first g hg ha hbd1 Ψ hΨ i⟩, fun i j => ?_⟩
    exact ⟨d2 i j, (memLp_first_deriv g hg ha hbd1 i).toLp _,
      hasWeakDerivative_radial_first g hg ha hbd1 Ψ hΨ i,
      hasWeakDerivative_radial_second g hg ha hbd1 hbd2 i j⟩
  refine ⟨hH2, ?_⟩
  have hchoose : ∀ i : Fin 3, (hH2.2 i i).choose = d2 i i := fun i =>
    hasWeakSecondDerivative_unique Ψ i i _ _ (hH2.2 i i).choose_spec
      ⟨(memLp_first_deriv g hg ha hbd1 i).toLp _,
        hasWeakDerivative_radial_first g hg ha hbd1 Ψ hΨ i,
        hasWeakDerivative_radial_second g hg ha hbd1 hbd2 i i⟩
  have hwL : weakLaplacian Ψ hH2 = -∑ i : Fin 3, d2 i i := by
    simp only [weakLaplacian]; rw [neg_inj]; exact Finset.sum_congr rfl (fun i _ => hchoose i)
  have hwL_coeFn : ⇑(weakLaplacian Ψ hH2) =ᵐ[volume]
      fun x => -∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
    have hc' : ∀ i : Fin 3, ⇑(d2 i i) =ᵐ[volume]
        fun x => fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) :=
      fun i => (memLp_second_deriv g hg ha hbd1 hbd2 i i).coeFn_toLp
    rw [hwL, Fin.sum_univ_three]
    filter_upwards [Lp.coeFn_neg (d2 0 0 + d2 1 1 + d2 2 2),
      Lp.coeFn_add (d2 0 0 + d2 1 1) (d2 2 2), Lp.coeFn_add (d2 0 0) (d2 1 1),
      hc' 0, hc' 1, hc' 2] with x hneg hadd2 hadd1 h0 h1 h2
    simp only [Fin.sum_univ_three, hneg, Pi.neg_apply, hadd2, hadd1, Pi.add_apply, h0, h1, h2]
  show hydrogenHamiltonian p ⟨Ψ, hH2⟩ = ((E : ℝ) : ℂ) • Ψ
  refine Lp.ext ?_
  have hae0 : ∀ᵐ x : R3, x ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]; exact measure_singleton 0
  have ehalf : ⇑(halfLaplacianPMap ⟨Ψ, hH2⟩) =ᵐ[volume]
      ((1 / 2 : ℝ) : ℂ) • ⇑(weakLaplacian Ψ hH2) := by
    rw [show halfLaplacianPMap ⟨Ψ, hH2⟩ = ((1 / 2 : ℝ) : ℂ) • weakLaplacian Ψ hH2 from by
      rw [halfLaplacianPMap_apply]; rfl]
    exact Lp.coeFn_smul _ _
  have ecoul : ⇑(coulombPotential p ⟨Ψ, hH2⟩) =ᵐ[volume]
      fun x => (coulombMultiplier p x : ℂ) * ⇑Ψ x :=
    (coulomb_mul_memLp_H2 p Ψ hH2).coeFn_toLp
  have eH : ⇑(hydrogenHamiltonian p ⟨Ψ, hH2⟩) =ᵐ[volume]
      fun x => ⇑(halfLaplacianPMap ⟨Ψ, hH2⟩) x + ⇑(coulombPotential p ⟨Ψ, hH2⟩) x := by
    rw [hydrogenHamiltonian_apply]; exact Lp.coeFn_add _ _
  filter_upwards [eH, ehalf, ecoul, hwL_coeFn, Lp.coeFn_smul ((E : ℝ) : ℂ) Ψ, hΨ, hae0]
    with x heH hehalf hecoul hwLx hsmulE hΨfx hx0
  rw [heH, hehalf, hecoul, hsmulE, Pi.smul_apply, Pi.smul_apply, hwLx, hΨfx, smul_eq_mul,
    smul_eq_mul, heigen' x hx0]
  have hcoulx : (coulombMultiplier p x : ℂ) = -(p.Z : ℂ) * (‖x‖ : ℂ)⁻¹ := by
    rw [coulombMultiplier, if_neg (by simpa using (norm_pos_iff.mpr hx0).ne')]
    push_cast; ring
  have hrne : (‖x‖ : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hx0)))
  rw [hcoulx]
  field_simp
  push_cast
  ring

/-- **The transported named eigenfunction is a genuine eigenvector — non-negative `m`.**
For `0 ≤ m ≤ ℓ < n`, `chartRealization.symm (hydrogenEigenfunction n ℓ ↑m hn hm')` is an `H²`
eigenvector of the `Z = 1` hydrogen Hamiltonian at `Eₙ`.  Combines the `ℓ = 0` `s`-state branch
(`chartRealization_symm_sstate_eigenpair`) with the `ℓ ≥ 1` separated branch
(`hydrogen_bound_state_separated`), bridged by the connection lemma. -/
lemma chartRealization_symm_eigenfunction_eigenpair_nat (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (hm : m ≤ ℓ)
    (hn1 : 1 ≤ n) (hm' : |(m : ℤ)| ≤ (ℓ : ℤ)) :
    ∃ hmem : chartRealization.symm (hydrogenEigenfunction n ℓ (m : ℤ) hn hm')
        ∈ (hydrogenHamiltonian ⟨1, one_pos⟩).domain,
      hydrogenHamiltonian ⟨1, one_pos⟩
          ⟨chartRealization.symm (hydrogenEigenfunction n ℓ (m : ℤ) hn hm'), hmem⟩
        = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ)
          • chartRealization.symm (hydrogenEigenfunction n ℓ (m : ℤ) hn hm') := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓ1
  · -- `ℓ = 0` forces `m = 0`: the `s`-state branch
    subst hℓ0
    have hm0 : m = 0 := by omega
    subst hm0
    -- the eigenvalue proofs are definitionally irrelevant
    have := chartRealization_symm_sstate_eigenpair n hn1 hm'
    simpa using this
  · -- `ℓ ≥ 1`: the separated branch, transferred along the connection a.e. equality
    obtain ⟨ψ, _, hψae, hψeig⟩ := hydrogen_bound_state_separated n ℓ m hn hm hℓ1
    have heq : (ψ : Spectra.Sobolev.L2_R3)
        = chartRealization.symm (hydrogenEigenfunction n ℓ (m : ℤ) hn hm') := by
      refine Lp.ext (hψae.trans ?_)
      exact (chartRealization_symm_eigenfunction_eq_separated n ℓ m hn hm hm').symm
    exact eigvec_transfer ⟨1, one_pos⟩ (hydrogenEigenvalue n hn1)
      (chartRealization.symm (hydrogenEigenfunction n ℓ (m : ℤ) hn hm')) ψ heq (by
        rw [hψeig])

/-- **Conjugation flips the sign of `m` on the spherical eigenfunction (up to a nonzero real
constant).**  `star (hydrogenEigenfunction n ℓ ↑m) = κ • hydrogenEigenfunction n ℓ (−↑m)` with
`κ = sphericalNorm·reflectionFactor / (…) ≠ 0` (Condon–Shortley).  Here `star` is the `L²`
conjugation on the spherical decomposition space. -/
lemma star_hydrogenEigenfunction (n ℓ m : ℕ) (hn : ℓ + 1 ≤ n) (_hm : m ≤ ℓ)
    (hm' : |(m : ℤ)| ≤ (ℓ : ℤ)) (hmneg' : |(-(m : ℤ))| ≤ (ℓ : ℤ)) :
    star (hydrogenEigenfunction n ℓ (m : ℤ) hn hm')
      = ((sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)
            / (sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))) : ℝ) : ℂ)
          • hydrogenEigenfunction n ℓ (-(m : ℤ)) hn hmneg' := by
  refine Lp.ext ?_
  -- coeFn of `star`
  have hstar := Lp.coeFn_star (hydrogenEigenfunction n ℓ (m : ℤ) hn hm')
  -- coeFn of both eigenfunctions
  have hpos := eigenfunction_sph_coeFn_gen n ℓ m hn hm'
  have hneg :
      ⇑(hydrogenEigenfunction n ℓ (-(m : ℤ)) hn hmneg')
        =ᵐ[radialMeasure.prod sphereMeasure]
        tensorFun (Rc n ℓ hn) ⟨ℓ, ⟨-(m : ℤ), hmneg'⟩⟩ := by
    -- mirror of `eigenfunction_sph_coeFn_gen` for the index `−m`
    have hsec := sectorEmbedding_coeFn ⟨ℓ, ⟨-(m : ℤ), hmneg'⟩⟩ (radialLp n ℓ hn)
    have hrad := (Measure.quasiMeasurePreserving_fst (μ := radialMeasure)
      (ν := sphereMeasure)).ae_eq_comp (radialLp_coeFn n ℓ hn)
    filter_upwards [hsec, hrad] with p hp hr
    simp only [hydrogenEigenfunction]
    rw [hp]; simp only [tensorFun]; simp only [Function.comp_apply] at hr; rw [hr]; rfl
  -- coeFn of the smul
  have hsmul := Lp.coeFn_smul
    ((sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)
        / (sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))) : ℝ) : ℂ)
    (hydrogenEigenfunction n ℓ (-(m : ℤ)) hn hmneg')
  filter_upwards [hstar, hpos, hneg, hsmul] with p hsp hpp hnp hsmp
  rw [hsp, hsmp]
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpp, hnp]
  simp only [tensorFun, harmonic, ← starRingEnd_apply]
  -- `Rc` is real, so `conj (Rc r) = Rc r`; the harmonic conjugates by Condon–Shortley
  have hRcconj : starRingEnd ℂ (Rc n ℓ hn p.1) = Rc n ℓ hn p.1 := by
    simp only [Rc, Complex.conj_ofReal]
  rw [map_mul, hRcconj, sphericalHarmonic_conj ℓ (m : ℤ) hm' hmneg' p.2]
  ring

/-- **`chartRealization.symm` commutes with conjugation.**  Transporting the conjugate of a
spherical element back to Cartesian `L²` is the conjugate of its transport. -/
lemma chartRealization_symm_star (v : Decomposition.L2_R3) :
    chartRealization.symm (star v) = star (chartRealization.symm v) := by
  refine Lp.ext ?_
  -- LHS coeFn: `(star v) ∘ sphereChartInv`, a.e.
  have hL := chartRealization_symm_coeFn (star v)
  have hstarv := Lp.coeFn_star v
  have hstarv' := (measurePreserving_sphereChartInv.quasiMeasurePreserving).ae_eq_comp hstarv
  -- RHS coeFn: `star (⇑(chartRealization.symm v))`, and `⇑(chartRealization.symm v) = v ∘ sphereChartInv`
  have hR := Lp.coeFn_star (chartRealization.symm v)
  have hRv := chartRealization_symm_coeFn v
  filter_upwards [hL, hstarv', hR, hRv] with x hLx hsx hRx hRvx
  rw [hLx, hRx]
  simp only [Function.comp_apply] at hsx
  rw [hsx]
  simp only [Pi.star_apply, hRvx]

/-- **Eigenvectors are closed under the domain scalar action.**  If `χ` is an eigenvector at `E`,
so is `c • χ` for any complex `c` (and `↑(c • χ) = c • ↑χ`). -/
lemma eigvec_smul (p : CoulombParams) (E : ℝ) (c : ℂ) (χ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p χ = (E : ℂ) • (χ : Spectra.Sobolev.L2_R3)) :
    ∃ hmem : c • (χ : Spectra.Sobolev.L2_R3) ∈ (hydrogenHamiltonian p).domain,
      hydrogenHamiltonian p ⟨c • (χ : Spectra.Sobolev.L2_R3), hmem⟩
        = (E : ℂ) • (c • (χ : Spectra.Sobolev.L2_R3)) := by
  refine ⟨(c • χ).2, ?_⟩
  have hcoe : ((c • χ : (hydrogenHamiltonian p).domain) : Spectra.Sobolev.L2_R3)
      = c • (χ : Spectra.Sobolev.L2_R3) := rfl
  have hχeq : (⟨c • (χ : Spectra.Sobolev.L2_R3), (c • χ).2⟩ : (hydrogenHamiltonian p).domain)
      = c • χ := Subtype.ext hcoe.symm
  rw [hχeq, LinearPMap.map_smul, heig]
  exact smul_comm c ((E : ℝ) : ℂ) (χ : Spectra.Sobolev.L2_R3)

/-- **The transported named eigenfunction is a genuine eigenvector — general integer `m`.**
For `0 ≤ ℓ < n` and any `M ∈ {−ℓ,…,ℓ}`, `chartRealization.symm (hydrogenEigenfunction n ℓ M hn hM)`
is an `H²` eigenvector of the `Z = 1` hydrogen Hamiltonian at `Eₙ`.  Negative `M` is reduced to the
`M ≥ 0` case via conjugation (`star_hydrogenEigenfunction`, `chartRealization_symm_star`,
`hydrogenHamiltonian_star`). -/
lemma chartRealization_symm_eigenfunction_eigenpair (n ℓ : ℕ) (M : ℤ) (hn : ℓ + 1 ≤ n)
    (hn1 : 1 ≤ n) (hM : |M| ≤ (ℓ : ℤ)) :
    ∃ hmem : chartRealization.symm (hydrogenEigenfunction n ℓ M hn hM)
        ∈ (hydrogenHamiltonian ⟨1, one_pos⟩).domain,
      hydrogenHamiltonian ⟨1, one_pos⟩
          ⟨chartRealization.symm (hydrogenEigenfunction n ℓ M hn hM), hmem⟩
        = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ)
          • chartRealization.symm (hydrogenEigenfunction n ℓ M hn hM) := by
  rcases le_total 0 M with hM0 | hM0
  · -- `M ≥ 0`: lift to `ℕ` and apply the non-negative case
    lift M to ℕ using hM0 with m hm0
    have hmℓ : m ≤ ℓ := by have := hM; rw [abs_le] at this; omega
    exact chartRealization_symm_eigenfunction_eigenpair_nat n ℓ m hn hmℓ hn1 hM
  · -- `M ≤ 0`: write `M = −m` with `m = (-M).toNat`, and conjugate the `+m` eigenvector
    obtain ⟨m, hmM⟩ : ∃ m : ℕ, (m : ℤ) = -M :=
      ⟨(-M).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hMeq : M = -(m : ℤ) := by rw [hmM]; ring
    subst hMeq
    have hmℓ : m ≤ ℓ := by
      have hle : (m : ℤ) ≤ ℓ := by rw [abs_le] at hM; omega
      exact_mod_cast hle
    have hm' : |(m : ℤ)| ≤ (ℓ : ℤ) := by rw [← abs_neg]; exact hM
    -- the `+m` transported eigenfunction is a genuine eigenvector (non-negative case)
    obtain ⟨hmemPos, heigPos⟩ := chartRealization_symm_eigenfunction_eigenpair_nat n ℓ m hn hmℓ hn1 hm'
    set psiPos : (hydrogenHamiltonian ⟨1, one_pos⟩).domain :=
      ⟨chartRealization.symm (hydrogenEigenfunction n ℓ (m : ℤ) hn hm'), hmemPos⟩ with hpsiPos_def
    -- `star psiPos` is an eigenvector at the (real) eigenvalue `Eₙ`
    have hstar_eig := hydrogenHamiltonian_star ⟨1, one_pos⟩ (hydrogenEigenvalue n hn1) psiPos heigPos
    set χ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain :=
      ⟨star (psiPos : Spectra.Sobolev.L2_R3), memSobolevH2_star _ psiPos.2⟩ with hχ_def
    -- the Condon–Shortley constant `κ ≠ 0`
    set κ : ℝ := sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)
        / (sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))) with hκ_def
    have hκne : κ ≠ 0 := div_ne_zero
      (mul_ne_zero (sphericalNorm_pos ℓ (m : ℤ)).ne' (reflectionFactor_ne_zero ℓ (m : ℤ)))
      (mul_ne_zero (sphericalNorm_pos ℓ (-(m : ℤ))).ne'
        (reflectionFactor_ne_zero ℓ (-(m : ℤ))))
    -- `eigfn n ℓ M = κ⁻¹ • star (eigfn n ℓ m)`, so its chart-transport is `κ⁻¹ • star ↑psiPos`
    have hconj := star_hydrogenEigenfunction n ℓ m hn hmℓ hm' hM
    have hMtransport : chartRealization.symm (hydrogenEigenfunction n ℓ (-(m : ℤ)) hn hM)
        = (((κ⁻¹ : ℝ) : ℂ)) • (χ : Spectra.Sobolev.L2_R3) := by
      -- from `hconj : star (eigfn m) = κ • eigfn (−m)`: `eigfn (−m) = κ⁻¹ • star (eigfn m)`
      have hinv : hydrogenEigenfunction n ℓ (-(m : ℤ)) hn hM
          = ((κ⁻¹ : ℝ) : ℂ) • star (hydrogenEigenfunction n ℓ (m : ℤ) hn hm') := by
        rw [hconj, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hκne, Complex.ofReal_one,
          one_smul]
      rw [hinv, map_smul, chartRealization_symm_star]
    rw [hMtransport]
    exact eigvec_smul ⟨1, one_pos⟩ (hydrogenEigenvalue n hn1) ((κ⁻¹ : ℝ) : ℂ) χ hstar_eig

/-- **★ Main deliverable.**  Every member of the degeneracy family `degenFamily n`, transported to
Cartesian `L²(ℝ³)` via `chartRealization.symm`, is a genuine `H²` eigenvector of the `Z = 1`
hydrogen Hamiltonian at the eigenvalue `Eₙ = −1/(2n²)`.  This covers all `n²` states `ψ_{nℓm}`
(`0 ≤ ℓ < n`, `m ∈ {−ℓ,…,ℓ}`, including `m < 0`). -/
theorem degenFamily_mem_ker (n : ℕ) (hn : 1 ≤ n) (i : ↥(degenIndex n)) :
    ∃ hmem : chartRealization.symm (degenFamily n i) ∈ (hydrogenHamiltonian ⟨1, one_pos⟩).domain,
      hydrogenHamiltonian ⟨1, one_pos⟩ ⟨_, hmem⟩
        = ((hydrogenEigenvalue n hn : ℝ) : ℂ) • chartRealization.symm (degenFamily n i) := by
  obtain ⟨hℓn, hMℓ⟩ := degenIndex_bounds i
  exact chartRealization_symm_eigenfunction_eigenpair n i.1.1 ((i.1.2 : ℤ) - i.1.1) hℓn hn hMℓ

/-! ## H2 — every `Eₙ` eigenstate lies in the span of the `n²` degeneracy states

The reverse inclusion `ker(H − Eₙ) ⊆ span(degenFamily n)`.  The forward machinery
(`SectorProjection.lean`) gives, sector by sector, a *classical* `C²` radial solution of the
reduced radial eigen-equation at `Eₙ`; the quantization/uniqueness theorems
(`radial_quantization` + `bound_state_eq_smul_eigenfunction`) then force each sector coefficient
to be either zero (if `ℓ ≥ n`) or a scalar multiple of `R_{nℓ}` (if `ℓ < n`).  The Hilbert-sum
reassembly collapses the (finitely-supported) decomposition into a finite span combination, which
`chartRealization.symm` transports back to the Cartesian side. -/

/-- **Injectivity of the energy levels.** `Eₙ = Eₙ' ⟹ n = n'` for `n, n' ≥ 1`
(immediate from strict monotonicity). -/
lemma hydrogenEigenvalue_inj {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h : hydrogenEigenvalue n hn = hydrogenEigenvalue n' hn') : n = n' := by
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exact absurd h (hydrogenEigenvalue_strictMono hn hn' hlt).ne
  · exact heq
  · exact absurd h.symm (hydrogenEigenvalue_strictMono hn' hn hgt).ne

/-- **Log-coordinate a.e. transport.**  A volume-a.e. equality of `s ↦ f(eˢ)` with `h` transports
to a `radialMeasure`-a.e. equality of `f` with `r ↦ h(log r)`.  (Inverse of the measure-transport
in `exp_ae_ne_of_radial_ae_ne`: the bad set in `r` is the `exp`-image of the volume-null bad set in
`s`, and `radialMeasure ≪ volume`.) -/
lemma radial_ae_of_logCoord_ae {f h : ℝ → ℝ}
    (hae : (fun s => f (Real.exp s)) =ᵐ[volume] h) :
    f =ᵐ[radialMeasure] fun r => h (Real.log r) := by
  have hN : volume {s | ¬ f (Real.exp s) = h s} = 0 := by
    have := hae; rw [Filter.EventuallyEq, ae_iff] at this; simpa using this
  have himg : volume (Real.exp '' {s | ¬ f (Real.exp s) = h s}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume Real.differentiable_exp.differentiableOn hN
  have hac : radialMeasure ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.restrict_le_self).absolutelyContinuous
  have hIoic : radialMeasure (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    have h := ae_radial_mem_Ioi; rwa [ae_iff] at h
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null
    (show {r | ¬ f r = h (Real.log r)} ⊆
      Real.exp '' {s | ¬ f (Real.exp s) = h s} ∪ (Set.Ioi 0)ᶜ from ?_) ?_
  · intro r hr
    by_cases hr0 : 0 < r
    · exact Or.inl ⟨Real.log r, by simpa [Real.exp_log hr0] using hr, Real.exp_log hr0⟩
    · exact Or.inr (by simpa using hr0)
  · exact measure_union_null (hac himg) hIoic

/-- **Per-sector dichotomy at a *known* level `n`.** A classical `C²`, `L²`, origin-regular
solution `ψ` of the reduced radial eigen-equation `H_ℓ ψ = Eₙ ψ` (at the *given* `Eₙ`) is *either*
identically zero on `(0,∞)`, *or* `ℓ < n` and `ψ = c·R_{nℓ}` for some constant `c`.  Specialization
of the general `RadialEq.radial_bound_state_unique` (which quantizes the energy of a nonzero bound
state) to a known `n`, using injectivity of the energy levels (`hydrogenEigenvalue_inj`) to pin
`n' = n`. -/
lemma radial_bound_state_dichotomy_at (ℓ n : ℕ) (hn1 : 1 ≤ n) (ψ : ℝ → ℝ)
    (hL2 : RadialL2 ψ)
    (hψ1 : ∀ r, 0 < r → HasDerivAt ψ (deriv ψ r) r)
    (hψ2 : ∀ r, 0 < r → HasDerivAt (deriv ψ) (deriv^[2] ψ r) r)
    (hψ0 : Filter.Tendsto (fun r => r * ψ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (heq : ∀ r, 0 < r → RadialEq.radialHamiltonian ℓ ψ r = hydrogenEigenvalue n hn1 * ψ r) :
    (∀ r, 0 < r → ψ r = 0) ∨
      (∃ (hℓn : ℓ + 1 ≤ n) (c : ℝ), ∀ r, 0 < r → ψ r = c * hydrogenRadialWavefunction n ℓ hℓn r) := by
  rcases RadialEq.radial_bound_state_unique ℓ (hydrogenEigenvalue n hn1)
      (hydrogenEigenvalue_neg n hn1) ψ hL2 hψ1 hψ2 hψ0 heq with hzero | ⟨n', hn', c, hEeq, hc⟩
  · exact Or.inl hzero
  · -- injectivity forces `n' = n`, so `ℓ + 1 ≤ n`
    right
    have hnn' : n = n' := hydrogenEigenvalue_inj hn1 (by omega) hEeq
    subst hnn'
    exact ⟨hn', c, hc⟩

/-- **Step A — GAP-1 bridge.**  The `i`-th component of the spherical decomposition of `Φ` is the
radial `L²` element built from the angular coefficient `coeffFun i Φ`.  Proved by `ext_inner_left`:
pairing the `i`-component against an arbitrary `R` reduces, through the unitary
`sphericalDecomposition` (`lp.inner_single_left`, `inner_map_map`,
`sphericalDecomposition_symm_single`) and the Fubini identity
`inner_sectorEmbedding_eq_integral_coeffFun`, to the radial pairing of `R` against `coeffFun i Φ`. -/
lemma sphericalDecomposition_eq_toLp_coeffFun (Φ : Decomposition.L2_R3) (i : HarmonicIdx) :
    sphericalDecomposition Φ i = (memLp_coeffFun i Φ).toLp (coeffFun i Φ) := by
  refine ext_inner_left ℂ (fun R => ?_)
  -- LHS: ⟪R, w i⟫ = ⟪single i R, w⟫ = ⟪symm (single i R), Φ⟫ = ⟪sectorEmbedding i R, Φ⟫
  have h1 : inner ℂ R (sphericalDecomposition Φ i)
      = inner ℂ (lp.single 2 i R) (sphericalDecomposition Φ) :=
    (lp.inner_single_left i R (sphericalDecomposition Φ)).symm
  have h2 : inner ℂ (lp.single 2 i R) (sphericalDecomposition Φ)
      = inner ℂ (sphericalDecomposition.symm (lp.single 2 i R)) Φ := by
    have := sphericalDecomposition.symm.inner_map_map (lp.single 2 i R) (sphericalDecomposition Φ)
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    exact this.symm
  rw [h1, h2, sphericalDecomposition_symm_single,
    inner_sectorEmbedding_eq_integral_coeffFun]
  -- RHS: ⟪R, toLp (coeffFun i Φ)⟫ = ∫ conj(R r)·coeffFun i Φ r ∂radialMeasure
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_coeffFun i Φ).coeFn_toLp] with r hr
  rw [hr, RCLike.inner_apply']

/-- **Step B (real, single functional).**  For an `Eₙ`-eigenpair `ψ'`, a sector `⟨ℓ, -(m:ℤ)⟩`
(`m ≤ ℓ`), and a real-linear functional `L`, the radial profile `r ↦ L(coeffFun ⟨ℓ,-(m:ℤ)⟩ Φ' r)`
is `radialMeasure`-a.e. *either* zero *or* (when `ℓ < n`) a real scalar multiple of `R_{nℓ}`.  This
is `forward_eigenvalue`'s sector analysis run with the *given* eigenvalue and closed with the
`radial_bound_state_unique` dichotomy in place of `radial_quantization_Z`. -/
lemma sector_reIm_dichotomy (n : ℕ) (hn1 : 1 ≤ n)
    (ψ' : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig' : hydrogenHamiltonian ⟨1, one_pos⟩ ψ'
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψ' : Spectra.Sobolev.L2_R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ) (L : ℂ →L[ℝ] ℝ) :
    (∀ᵐ r ∂radialMeasure, L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ' : Spectra.Sobolev.L2_R3)) r) = 0) ∨
      (∃ (hℓn : ℓ + 1 ≤ n) (c : ℝ), ∀ᵐ r ∂radialMeasure,
        L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
          (chartRealization (ψ' : Spectra.Sobolev.L2_R3)) r)
          = c * hydrogenRadialWavefunction n ℓ hℓn r) := by
  classical
  set Φ' := chartRealization (ψ' : Spectra.Sobolev.L2_R3) with hΦ'
  set g : ℝ → ℂ := coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩ Φ' with hg
  set E := hydrogenEigenvalue n hn1 with hE
  -- raw classical `C²` solution of the log-coordinate ODE (mirrors `forward_eigenvalue`)
  obtain ⟨c₀, hae, hc1, hc2, hode⟩ :=
    Spectra.RadialRegularity.classical_of_weak_ode
      (locallyIntegrable_comp_exp g (memLp_coeffFun _ _) L)
      (b := fun s => (ℓ : ℝ) * ((ℓ : ℝ) + 1)
        - 2 * (⟨1, one_pos⟩ : CoulombParams).Z * Real.exp s - 2 * E * Real.exp (2 * s))
      (by fun_prop)
      (sector_sweak ⟨1, one_pos⟩ E ψ' heig' ℓ m hm L)
  obtain ⟨h1, h2, h3⟩ := radial_classical_of_logCoord ℓ (⟨1, one_pos⟩ : CoulombParams).Z E c₀
    hc1 hc2 hode
  set ψr : ℝ → ℝ := fun r => c₀ (Real.log r) with hψr
  have hZ1 : (⟨1, one_pos⟩ : CoulombParams).Z = 1 := rfl
  -- the radial Hamiltonian ODE `H_ℓ ψr = Eₙ ψr` (from `h3`, using `Z = 1`)
  have hHeq : ∀ r, 0 < r → RadialEq.radialHamiltonian ℓ ψr r = E * ψr r := by
    intro r hr
    have h3r := h3 r hr
    rw [hZ1] at h3r
    simp only [RadialEq.radialHamiltonian]
    linarith [h3r]
  -- `ψr ∈ RadialL2`, C¹/C², origin-regular
  have hL2 : RadialL2 ψr := sector_radialL2 g (memLp_coeffFun _ _) L c₀ hae
  have hint : Integrable (fun s => Real.exp s * c₀ s ^ 2) volume :=
    (sector_coulomb_L2 ⟨1, one_pos⟩ ψ' ℓ m hm L).congr
      (by filter_upwards [hae] with s hs; rw [hs])
  have hψ0 : Filter.Tendsto (fun r => r * ψr r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    radial_bc_of_logCoord ℓ (⟨1, one_pos⟩ : CoulombParams).Z E (by rw [hZ1]; norm_num)
      (hydrogenEigenvalue_neg n hn1) c₀ hc1 hc2 hode hint
  -- the a.e. link `L(g r) =ᵐ[radialMeasure] ψr r`
  have hlink : (fun r => L (g r)) =ᵐ[radialMeasure] ψr :=
    radial_ae_of_logCoord_ae (h := c₀) hae
  -- run the radial dichotomy
  rcases radial_bound_state_dichotomy_at ℓ n hn1 ψr hL2 h1 h2 hψ0 hHeq with hzero | ⟨hℓn, c, hc⟩
  · left
    filter_upwards [hlink, ae_radial_mem_Ioi] with r hrl hr0
    rw [hg] at hrl ⊢; rw [hrl, hψr]
    exact hzero r (Set.mem_Ioi.mp hr0)
  · right
    refine ⟨hℓn, c, ?_⟩
    filter_upwards [hlink, ae_radial_mem_Ioi] with r hrl hr0
    rw [hg] at hrl ⊢; rw [hrl, hψr]
    exact hc r (Set.mem_Ioi.mp hr0)

/-- **Step B (complex coefficient, non-positive index).**  Recombining the real and imaginary
dichotomies (`sector_reIm_dichotomy` at `reCLM`, `imCLM`): the `⟨ℓ,-(m:ℤ)⟩` angular coefficient of
an `Eₙ`-eigenpair is `radialMeasure`-a.e. *either* zero *or* (when `ℓ < n`) a complex scalar
multiple of `R_{nℓ}`. -/
lemma sector_complex_dichotomy (n : ℕ) (hn1 : 1 ≤ n)
    (ψ' : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig' : hydrogenHamiltonian ⟨1, one_pos⟩ ψ'
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψ' : Spectra.Sobolev.L2_R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ) :
    (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ' : Spectra.Sobolev.L2_R3)) =ᵐ[radialMeasure] 0) ∨
      (∃ (hℓn : ℓ + 1 ≤ n) (c : ℂ),
        coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
          (chartRealization (ψ' : Spectra.Sobolev.L2_R3))
          =ᵐ[radialMeasure] fun r => c * Rc n ℓ hℓn r) := by
  classical
  set g : ℝ → ℂ := coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
    (chartRealization (ψ' : Spectra.Sobolev.L2_R3)) with hg
  have hre := sector_reIm_dichotomy n hn1 ψ' heig' ℓ m hm Complex.reCLM
  have him := sector_reIm_dichotomy n hn1 ψ' heig' ℓ m hm Complex.imCLM
  rw [← hg] at hre him
  by_cases hz : g =ᵐ[radialMeasure] 0
  · exact Or.inl hz
  · right
    -- some part is nonzero, so its dichotomy is the nonzero branch, fixing `ℓ < n`
    obtain ⟨L, hLeq, hLne⟩ := exists_reIm_comp_ne_zero (μ := radialMeasure) g hz
    -- extract `ℓ < n` and real coefficients for both re and im
    have hgetℓ : ℓ + 1 ≤ n := by
      rcases hLeq with rfl | rfl
      · rcases hre with h | ⟨hℓn, _, _⟩
        · exact absurd h hLne
        · exact hℓn
      · rcases him with h | ⟨hℓn, _, _⟩
        · exact absurd h hLne
        · exact hℓn
    refine ⟨hgetℓ, ?_⟩
    -- real coefficients `cre`, `cim` (zero branch ↦ coefficient 0)
    obtain ⟨cre, hcre⟩ : ∃ cre : ℝ, ∀ᵐ r ∂radialMeasure,
        Complex.reCLM (g r) = cre * hydrogenRadialWavefunction n ℓ hgetℓ r := by
      rcases hre with h | ⟨hℓn', c, hc⟩
      · exact ⟨0, by filter_upwards [h] with r hr; rw [hr]; simp⟩
      · exact ⟨c, by simpa [Subsingleton.elim hℓn' hgetℓ] using hc⟩
    obtain ⟨cim, hcim⟩ : ∃ cim : ℝ, ∀ᵐ r ∂radialMeasure,
        Complex.imCLM (g r) = cim * hydrogenRadialWavefunction n ℓ hgetℓ r := by
      rcases him with h | ⟨hℓn', c, hc⟩
      · exact ⟨0, by filter_upwards [h] with r hr; rw [hr]; simp⟩
      · exact ⟨c, by simpa [Subsingleton.elim hℓn' hgetℓ] using hc⟩
    refine ⟨((cre : ℂ) + (cim : ℂ) * Complex.I), ?_⟩
    filter_upwards [hcre, hcim] with r hr hi
    have hrer : (g r).re = cre * hydrogenRadialWavefunction n ℓ hgetℓ r := by simpa using hr
    have himr : (g r).im = cim * hydrogenRadialWavefunction n ℓ hgetℓ r := by simpa using hi
    apply Complex.ext
    · simp only [Rc, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      rw [hrer]; ring
    · simp only [Rc, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.mul_im]
      rw [himr]; ring

/-- **Step B (general integer `M`).**  The full per-sector dichotomy for *any* magnetic index
`M ∈ {−ℓ,…,ℓ}` of the spherical decomposition of an `Eₙ`-eigenstate: the `⟨ℓ,M⟩` angular
coefficient of `Φ = chartRealization ψ` is `radialMeasure`-a.e. *either* zero *or* (when `ℓ < n`) a
complex scalar multiple of `R_{nℓ}`.  Non-negative `M` is reduced to the native non-positive index
of `sector_complex_dichotomy` via conjugation (`coeffFun_star`, `hydrogenHamiltonian_star`). -/
lemma coeffFun_dichotomy (n : ℕ) (hn1 : 1 ≤ n)
    (ψ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig : hydrogenHamiltonian ⟨1, one_pos⟩ ψ
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψ : Spectra.Sobolev.L2_R3))
    (ℓ : ℕ) (M : ℤ) (hM : |M| ≤ (ℓ : ℤ)) :
    (coeffFun ⟨ℓ, M, hM⟩ (chartRealization (ψ : Spectra.Sobolev.L2_R3)) =ᵐ[radialMeasure] 0) ∨
      (∃ (hℓn : ℓ + 1 ≤ n) (c : ℂ),
        coeffFun ⟨ℓ, M, hM⟩ (chartRealization (ψ : Spectra.Sobolev.L2_R3))
          =ᵐ[radialMeasure] fun r => c * Rc n ℓ hℓn r) := by
  classical
  rcases le_total M 0 with hMle | hMge
  · -- `M ≤ 0`: native non-positive index, `m = (-M).toNat`
    obtain ⟨m, hmM⟩ : ∃ m : ℕ, (m : ℤ) = -M := ⟨(-M).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hMeq : M = -(m : ℤ) := by omega
    have hm : m ≤ ℓ := by rw [abs_le] at hM; omega
    -- the index `⟨ℓ, M, hM⟩` *is* `⟨ℓ, -(m:ℤ), _⟩`
    have hidx : (⟨ℓ, M, hM⟩ : HarmonicIdx)
        = ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩ := by
      apply HarmonicIdx.ext <;> simp [hMeq]
    rw [hidx]
    rcases sector_complex_dichotomy n hn1 ψ heig ℓ m hm with h | ⟨hℓn, c, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨hℓn, c, hc⟩
  · -- `M ≥ 0`: conjugate trick via `star ψ`, `m = M.toNat`
    obtain ⟨m, hmM⟩ : ∃ m : ℕ, (m : ℤ) = M := ⟨M.toNat, Int.toNat_of_nonneg hMge⟩
    have hm : m ≤ ℓ := by rw [abs_le] at hM; omega
    have hmI : |(m : ℤ)| ≤ (ℓ : ℤ) := by rw [hmM]; exact hM
    -- the index `⟨ℓ, M, hM⟩` is `⟨ℓ, (m:ℤ), _⟩`
    have hidx : (⟨ℓ, M, hM⟩ : HarmonicIdx) = ⟨ℓ, (m : ℤ), hmI⟩ := by
      apply HarmonicIdx.ext <;> simp [hmM]
    rw [hidx]
    -- the Condon–Shortley constant
    set κ : ℝ := sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))
        / (sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)) with hκ
    have hκne : κ ≠ 0 := div_ne_zero
      (mul_ne_zero (sphericalNorm_pos _ _).ne' (reflectionFactor_ne_zero _ _))
      (mul_ne_zero (sphericalNorm_pos _ _).ne' (reflectionFactor_ne_zero _ _))
    -- `star ψ` is an eigenpair at `Eₙ`; run the dichotomy on its `-(m:ℤ)` coefficient
    set ψs : (hydrogenHamiltonian ⟨1, one_pos⟩).domain :=
      ⟨star (ψ : Spectra.Sobolev.L2_R3), memSobolevH2_star _ ψ.2⟩ with hψs
    have heigs : hydrogenHamiltonian ⟨1, one_pos⟩ ψs
        = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψs : Spectra.Sobolev.L2_R3) :=
      hydrogenHamiltonian_star ⟨1, one_pos⟩ (hydrogenEigenvalue n hn1) ψ heig
    -- `coeffFun_star`: the `-(m:ℤ)` coefficient of `star ψ` is `κ·conj` of the `m` coefficient of ψ
    have hcs := coeffFun_star ℓ m hm (ψ : Spectra.Sobolev.L2_R3)
    rcases sector_complex_dichotomy n hn1 ψs heigs ℓ m hm with h | ⟨hℓn, c, hc⟩
    · -- the `-(m:ℤ)` coefficient of `star ψ` is a.e. 0, hence so is the `m` coefficient of ψ
      left
      -- `hcs : coeffFun⟨ℓ,-(m)⟩(chartReal (star ψ)) =ᵐ κ·conj(coeffFun⟨ℓ,m⟩(chartReal ψ))`
      have hzero : (fun r => (κ : ℂ) *
          starRingEnd ℂ (coeffFun ⟨ℓ, (m : ℤ), hmI⟩
            (chartRealization (ψ : Spectra.Sobolev.L2_R3)) r)) =ᵐ[radialMeasure] 0 :=
        hcs.symm.trans h
      filter_upwards [hzero] with r hr
      simp only [Pi.zero_apply] at hr ⊢
      rcases mul_eq_zero.mp hr with hk | hc0
      · exact absurd (Complex.ofReal_eq_zero.mp hk) hκne
      · rw [starRingEnd_apply, star_eq_zero] at hc0; exact hc0
    · -- the `-(m:ℤ)` coefficient of `star ψ` is `c·Rc`; conjugate back
      right
      refine ⟨hℓn, (κ : ℂ)⁻¹ * starRingEnd ℂ c, ?_⟩
      -- from `hcs` and `hc`: `κ·conj(coeffFun⟨ℓ,m⟩ Φ) =ᵐ c·Rc`, so `coeffFun⟨ℓ,m⟩ Φ =ᵐ conj(κ⁻¹c)·Rc`
      have hcomb : (fun r => (κ : ℂ) *
          starRingEnd ℂ (coeffFun ⟨ℓ, (m : ℤ), hmI⟩
            (chartRealization (ψ : Spectra.Sobolev.L2_R3)) r))
          =ᵐ[radialMeasure] fun r => c * Rc n ℓ hℓn r := hcs.symm.trans hc
      filter_upwards [hcomb] with r hr
      have hκc : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκne
      -- solve for the `m` coefficient and conjugate (Rc is real)
      have hval : starRingEnd ℂ (coeffFun ⟨ℓ, (m : ℤ), hmI⟩
          (chartRealization (ψ : Spectra.Sobolev.L2_R3)) r) = (κ : ℂ)⁻¹ * (c * Rc n ℓ hℓn r) := by
        field_simp at hr ⊢
        linear_combination hr
      have hRcconj : starRingEnd ℂ (Rc n ℓ hℓn r) = Rc n ℓ hℓn r := by
        simp [Rc, Complex.conj_ofReal]
      have := congrArg (starRingEnd ℂ) hval
      rw [Complex.conj_conj] at this
      rw [this]
      simp only [map_mul, map_inv₀, hRcconj, Complex.conj_ofReal]
      ring

/-- **Index map into the degeneracy family.**  For `ℓ < n` and `|M| ≤ ℓ`, the named eigenfunction
`ψ_{nℓM}` is literally a member of `degenFamily n` (at the index `⟨⟨ℓ, (M+ℓ).toNat⟩, _⟩`), hence lies
in the span of its range. -/
lemma hydrogenEigenfunction_mem_span (n ℓ : ℕ) (M : ℤ) (hℓn : ℓ + 1 ≤ n) (hM : |M| ≤ (ℓ : ℤ)) :
    hydrogenEigenfunction n ℓ M hℓn hM ∈ Submodule.span ℂ (Set.range (degenFamily n)) := by
  -- the index `j = (M + ℓ).toNat ∈ {0,…,2ℓ}`
  set j : ℕ := (M + ℓ).toNat with hj
  have hjmem : ⟨ℓ, j⟩ ∈ degenIndex n := by
    simp only [degenIndex, Finset.mem_sigma, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have : |M| ≤ (ℓ : ℤ) := hM
    rw [abs_le] at this
    omega
  set idx : ↥(degenIndex n) := ⟨⟨ℓ, j⟩, hjmem⟩ with hidx
  -- `degenFamily n idx = hydrogenEigenfunction n ℓ ((j:ℤ)-ℓ) _ _`, and `(j:ℤ)-ℓ = M`
  have hjM : ((j : ℤ) - ℓ) = M := by
    have : |M| ≤ (ℓ : ℤ) := hM
    rw [abs_le] at this
    simp only [hj]
    omega
  have heq : degenFamily n idx = hydrogenEigenfunction n ℓ M hℓn hM := by
    simp only [degenFamily, hidx]
    -- the magnetic index agrees; the proof arguments are irrelevant
    have hidxeq : (⟨ℓ, (j : ℤ) - ℓ, (degenIndex_bounds idx).2⟩ : HarmonicIdx)
        = ⟨ℓ, M, hM⟩ := HarmonicIdx.ext rfl (by simpa using hjM)
    simp only [hydrogenEigenfunction]
    rw [hidxeq]
  rw [← heq]
  exact Submodule.subset_span ⟨idx, rfl⟩

/-- **Step C, per sector.**  Each reassembled summand `sectorEmbedding i (w i)` of an
`Eₙ`-eigenstate's spherical decomposition lies in the span of the degeneracy family, *and* it
vanishes whenever `i.1 ≥ n` (so the family `i ↦ sectorEmbedding i (w i)` is finitely supported).
Combining Step A (`w i = toLp (coeffFun i Φ)`), the general-`M` dichotomy (`coeffFun_dichotomy`),
and `radialLp_coeFn` (`⇑(radialLp) =ᵐ R_{nℓ}`): the `i`-component is `0` or `c • ψ_{nℓM}`. -/
lemma sectorEmbedding_w_mem_span (n : ℕ) (hn1 : 1 ≤ n)
    (ψ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig : hydrogenHamiltonian ⟨1, one_pos⟩ ψ
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) • (ψ : Spectra.Sobolev.L2_R3))
    (i : HarmonicIdx) :
    sectorEmbedding i (sphericalDecomposition
        (chartRealization (ψ : Spectra.Sobolev.L2_R3)) i)
      ∈ Submodule.span ℂ (Set.range (degenFamily n)) ∧
    (n ≤ i.1 → sphericalDecomposition (chartRealization (ψ : Spectra.Sobolev.L2_R3)) i = 0) := by
  classical
  obtain ⟨ℓ, M, hM⟩ := i
  set Φ := chartRealization (ψ : Spectra.Sobolev.L2_R3) with hΦ
  -- Step A: the component is the `toLp` of the angular coefficient
  have hA := sphericalDecomposition_eq_toLp_coeffFun Φ ⟨ℓ, M, hM⟩
  rcases coeffFun_dichotomy n hn1 ψ heig ℓ M hM with hzero | ⟨hℓn, c, hc⟩
  · -- zero component
    have hw0 : sphericalDecomposition Φ ⟨ℓ, M, hM⟩ = 0 := by
      rw [hA]
      refine Lp.ext ?_
      filter_upwards [(memLp_coeffFun ⟨ℓ, M, hM⟩ Φ).coeFn_toLp, hzero, Lp.coeFn_zero ℂ 2 radialMeasure]
        with r h1 h2 h3
      rw [h1, h2, h3]
    refine ⟨?_, fun _ => hw0⟩
    rw [hw0, map_zero]
    exact Submodule.zero_mem _
  · -- `c • radialLp` component, `ℓ < n`
    have hw : sphericalDecomposition Φ ⟨ℓ, M, hM⟩ = c • radialLp n ℓ hℓn := by
      rw [hA]
      refine Lp.ext ?_
      filter_upwards [(memLp_coeffFun ⟨ℓ, M, hM⟩ Φ).coeFn_toLp, hc,
        Lp.coeFn_smul c (radialLp n ℓ hℓn), radialLp_coeFn n ℓ hℓn] with r h1 h2 h3 h4
      rw [h1, h2, h3, Pi.smul_apply, h4, smul_eq_mul, Rc]
    refine ⟨?_, fun hle => absurd hℓn (by simp only at hle; omega)⟩
    rw [hw, map_smul]
    refine Submodule.smul_mem _ c ?_
    -- `sectorEmbedding ⟨ℓ,M⟩ (radialLp n ℓ hℓn) = hydrogenEigenfunction n ℓ M`
    have : sectorEmbedding ⟨ℓ, M, hM⟩ (radialLp n ℓ hℓn)
        = hydrogenEigenfunction n ℓ M hℓn hM := rfl
    rw [this]
    exact hydrogenEigenfunction_mem_span n ℓ M hℓn hM

/-- The set of harmonic indices with `ℓ < n` is finite (it injects into
`range n ×ˢ Icc (-n) n` via `i ↦ (i.1, i.2.1)`). -/
lemma finite_harmonicIdx_lt (n : ℕ) : {i : HarmonicIdx | (i.1 : ℕ) < n}.Finite := by
  classical
  apply Set.Finite.of_finite_image (f := fun i : HarmonicIdx => (i.1, i.2.1))
  · refine Set.Finite.subset
      ((Set.finite_Iio n).prod (Set.finite_Icc (-(n : ℤ)) n)) ?_
    rintro _ ⟨⟨ℓ, M, hM⟩, hmem, rfl⟩
    simp only [Set.mem_setOf_eq] at hmem
    refine Set.mem_prod.mpr ⟨hmem, ?_⟩
    rw [Set.mem_Icc, ← abs_le]
    exact le_trans hM (by exact_mod_cast hmem.le)
  · intro a _ b _ hab
    exact HarmonicIdx.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- **★ H2 deliverable.**  Every `Z = 1` hydrogen eigenstate `ψ` at the energy `Eₙ` lies in the
`ℂ`-span of the `n²` transported degeneracy states `chartRealization.symm (degenFamily n ·)`.

This is the reverse inclusion `ker(H − Eₙ) ⊆ span`, completing (with `degenFamily_mem_ker`, the
forward `⊇`) the identification of the `Eₙ`-eigenspace with the degeneracy span.  The proof: pass
to the spherical side `Φ = chartRealization ψ`, decompose `Φ = ∑' i, sectorEmbedding i (w i)` in the
Hilbert sum; each summand is either `0` (when `ℓ ≥ n`) or a multiple of a degeneracy state (when
`ℓ < n`), and the family is finitely supported, so the sum collapses to a finite span combination,
which `chartRealization.symm` transports back. -/
theorem eigenspace_subset_span (n : ℕ) (hn : 1 ≤ n)
    (ψ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain)
    (heig : hydrogenHamiltonian ⟨1, one_pos⟩ ψ
      = ((hydrogenEigenvalue n hn : ℝ) : ℂ) • (ψ : Spectra.Sobolev.L2_R3)) :
    (ψ : Spectra.Sobolev.L2_R3)
      ∈ Submodule.span ℂ (Set.range (fun i => chartRealization.symm (degenFamily n i))) := by
  classical
  set Φ := chartRealization (ψ : Spectra.Sobolev.L2_R3) with hΦ
  set w := sphericalDecomposition Φ with hw
  set f : HarmonicIdx → Decomposition.L2_R3 := fun i => sectorEmbedding i (w i) with hf
  -- the per-sector data: each summand lies in the span; support is within `{ℓ < n}`
  have hsector := fun i => sectorEmbedding_w_mem_span n hn ψ heig i
  -- Step C reassembly on the *spherical* side: `Φ = ∑' i, f i`
  have hsum : Φ = ∑' i, f i := by
    have h := sphericalDecomposition_symm_apply w
    rw [hw, LinearIsometryEquiv.symm_apply_apply] at h
    rw [hΦ] at h ⊢
    exact h
  -- finite support of `f`
  have hsupp : Function.support f ⊆ {i : HarmonicIdx | (i.1 : ℕ) < n} := by
    intro i hi
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_lt] at hlt
    exact hi (by simp only [hf]; rw [(hsector i).2 hlt, map_zero])
  obtain ⟨T, hT⟩ := (finite_harmonicIdx_lt n).subset hsupp |>.exists_finset_coe
  -- the tsum collapses to a finite sum over `T`
  have hΦsum : Φ = ∑ i ∈ T, f i := by
    rw [hsum, tsum_eq_sum (s := T) ?_]
    intro i hiT
    by_contra hne
    exact hiT (hT.ge (Function.mem_support.mpr hne))
  -- `Φ ∈ span (range degenFamily n)` (spherical side)
  have hΦmem : Φ ∈ Submodule.span ℂ (Set.range (degenFamily n)) := by
    rw [hΦsum]
    exact Submodule.sum_mem _ (fun i _ => (hsector i).1)
  -- transport along the linear isometry `chartRealization.symm`
  have htrans : chartRealization.symm Φ
      ∈ Submodule.span ℂ (chartRealization.symm '' Set.range (degenFamily n)) :=
    Submodule.apply_mem_span_image_of_mem_span
      (f := (chartRealization.symm : Decomposition.L2_R3 →ₗ[ℂ] Spectra.Sobolev.L2_R3)) hΦmem
  rw [← Set.range_comp] at htrans
  -- `chartRealization.symm Φ = ψ`
  have hψ : chartRealization.symm Φ = (ψ : Spectra.Sobolev.L2_R3) := by
    rw [hΦ, LinearIsometryEquiv.symm_apply_apply]
  rwa [hψ] at htrans

end QuantumMechanics.Hydrogen.Spectrum

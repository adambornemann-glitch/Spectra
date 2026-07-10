/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.SolidHarmonic
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Degeneracy
import Spectra.QuantumMechanics.Hydrogen.Spectrum.RadialEigenfunction.Basic
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SectorProjection
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SectorReductionLocal

/-!
# Separated hydrogen eigenfunctions: profile and Sobolev regularity

This file builds the non-radial (`ℓ ≥ 1`) separated eigenfunction
`Ψ_{nℓm} = S_{nℓ}(‖·‖)·solidHarmonicNat ℓ m` from its reduced radial profile
`S_{nℓ} = R_{nℓ}/r^ℓ`, establishes the classical eigen-equation it satisfies off the origin (via
a localizing smooth cutoff avoiding the origin singularity), and assembles the `H²`
weak-derivative stack placing `Ψ` in the domain of the hydrogen Hamiltonian.  The `ℓ = 0`
(spherically symmetric) case is radial and is handled by `bound_state_of_radial_profile` in
`RadialEigenfunction/Basic.lean`.

## Main statements

* `reducedRadialProfile`/`separatedEigenfunction` — the smooth reduced radial profile
  `S_{nℓ} = R_{nℓ}/r^ℓ` and the Cartesian separated eigenfunction
  `Ψ_{nℓm} = S_{nℓ}(‖·‖)·Y_ℓ^m`.
* `separated_eigen_chart` — `Ψ` solves the Cartesian sum-of-second-derivatives eigen-equation
  `Σⱼ ∂ⱼ² Ψ = −2·(Eₙ + 1/‖x‖)·Ψ` at every interior chart point (`r > 0`, `θ ∈ (0, π)`).
* `memLp_separated`/`memLp_separated_first`/`memLp_separated_second` — `Ψ`, its first partials
  `∂ᵢΨ`, and its mixed second partials `∂ⱼ∂ᵢΨ` are all `L²` (the `1/‖x‖` Hessian singularity is
  `L²` in `ℝ³`).
* `hasWeakDerivative_separated_first`/`_second` — the classical partials are the weak
  first/second derivatives of the `L²` element representing `Ψ`, via `master_ibp`.
* `fderiv_smul_of_homogeneous`/`fderiv_norm_le_of_homogeneous`/`fderiv_norm_mul_le_of_homogeneous`
  — the general positive-homogeneity machine yielding the solid-harmonic gradient/Hessian growth
  bounds `‖∂^k Sℓᵐ(x)‖ ≤ C·‖x‖^{ℓ−k}`.
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
`exp_bound_of_tendsto` packaging in `RadialEigenfunction/Basic.lean`) with the `r^ℓ` prefactor
pruned: `S = A·e^{−r/n}·L(2r/n)` with `A = N_{nℓ}·(2/n)^ℓ` a constant, so the buffered Laguerre
limits (`tendsto_pow_exp_laguerre_buffer` etc., with power `a = 0`) close everything. -/

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
  set A := radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ with _hA
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with _hLdef
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
  set A := radialNormalization n ℓ hn * (2 / (n : ℝ)) ^ ℓ with _hA
  set L := laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) with _hLdef
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
            deriv (laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1)) (2 * r / n) * Real.exp (ε * r)))
            := by
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
  set p : CoulombParams := ⟨1, one_pos⟩ with _hp
  set pt := sphereChart r θ φ with hpt
  have hnorm : ‖pt‖ = r := by rw [hpt, norm_sphereChart, abs_of_pos hr]
  have _hptne : pt ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; exact hr)
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
  have _hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
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
    refine (hgrad1.continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton le_rfl).mono (fun u hu => ?_)
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
    refine (hgrad1.continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton le_rfl).mono (fun u hu => ?_)
    simp only [Metric.mem_sphere, dist_zero_right] at hu
    exact fun (h : u = 0) => by rw [h, norm_zero] at hu; exact zero_ne_one hu
  have hres := fderiv_norm_le_of_homogeneous (d := ℓ - 1) (by omega) hdiff hcont
    (fun s hs y hy => fderiv_solidHarmonicNat_smul' ℓ m hm (by omega) hs hy)
  rwa [show ℓ - 1 - 1 = ℓ - 2 from by omega] at hres

/-! ## H²-Sobolev weak-derivative stack for the separated eigenfunction `Ψ = S(‖·‖)·Q`

Mirrors the radial stack of `RadialEigenfunction/` for the genuinely non-radial witness
`Ψ_{nℓm} = reducedRadialProfileC n ℓ hn (‖·‖) · solidHarmonicNat ℓ m`.  Throughout, `ℓ ≥ 1` is
assumed (the `ℓ = 0` case is radial and is handled by `bound_state_of_radial_profile`). -/

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
  set R₀ : ℝ := max R 0 with _hR₀
  have hR₀0 : 0 ≤ R₀ := le_max_right _ _
  obtain ⟨b, -, hbmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R₀)).exists_isMaxOn
    (Set.nonempty_Icc.mpr hR₀0)
    (Continuous.continuousOn
      (by fun_prop : Continuous fun r : ℝ => r ^ k * Real.exp (-(a - a') * r)))
  set M : ℝ := b ^ k * Real.exp (-(a - a') * b) with _hM
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
harmonic the polynomial growth `‖x‖^{ℓ−k}` (absorbed by `pow_mul_exp_le_exp`).  The decay rate
is fixed at `a = 1/(2n)` (from `S`-decay), with the polynomials absorbed into `a' = 1/(4n)`. -/

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
  have _hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
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
  have _hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
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
gradient of `∂ᵢQ`.  The bound comes from differentiating the product expression for `∂ᵢΨ`
(valid `=ᶠ` near `x`). -/

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
  set Q : Spectra.Sobolev.R3 → ℂ := solidHarmonicNat ℓ m with _hQ
  set B : Spectra.Sobolev.R3 → ℂ := fun y => fderiv ℝ Q y (EuclideanSpace.single i 1) with _hB
  set Dr : Spectra.Sobolev.R3 → ℂ :=
    fun y => fderiv ℝ Acl y (EuclideanSpace.single i 1) with _hDr
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
  have _hAcl2 : ContDiffAt ℝ 2 Acl x :=
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
  set eB : ℝ := Real.exp (-(1 / (4 * (n:ℝ))) * ‖x‖) with _heB
  have _heA0 : 0 < eA := Real.exp_pos _
  have _heB0 : 0 < eB := Real.exp_pos _
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
  have hcont : ContinuousOn
    (fun x => fderiv ℝ (fun y => fderiv ℝ (separatedEigenfunction n ℓ m hn) y
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
  obtain ⟨C, _hC0, hC⟩ := norm_separated_le_exp n ℓ m hn hm
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
  obtain ⟨C, _hC0, hC⟩ := norm_fderiv_separated_le_exp n ℓ m hn hm hℓ i
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
  obtain ⟨C, C', _hC0, _hC'0, hC⟩ := norm_fderiv2_separated_le_exp n ℓ m hn hm hℓ i j
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
    fun x => fderiv ℝ (separatedEigenfunction n ℓ m hn) x (EuclideanSpace.single i 1) with _hD
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

end QuantumMechanics.Hydrogen.Spectrum

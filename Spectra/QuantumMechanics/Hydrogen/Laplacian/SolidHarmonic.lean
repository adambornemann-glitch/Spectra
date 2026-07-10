/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Regular solid harmonics

The **regular solid harmonic** of degree `ℓ` and order `m ≥ 0` is the Cartesian function

`Sℓᵐ(x) = Nℓᵐ · (−1)^m/(2^ℓ ℓ!) · (x₀ + i x₁)^m · ‖x‖^{ℓ−m} · Q(x₂/‖x‖)`,

where `Q = d^{ℓ+m}/dt^{ℓ+m}(t² − 1)^ℓ` is the Rodrigues polynomial.  Unlike the surface
harmonic `Yℓᵐ` (which is singular on the `z`-axis as a function of the Cartesian point, through
the `e^{imφ}` factor), the solid harmonic is **smooth away from the origin**: the `(sin θ)^m`
factor inside `Yℓᵐ` combines with `e^{imφ}` into the polynomial `(x₀ + i x₁)^m`, and the
leftover radial powers are smooth on `ℝ³ ∖ {0}`.

This is the missing ingredient for the **forward direction** of the hydrogen discrete-spectrum
theorem: it supplies a *smooth, separated* test function `χ(‖x‖) · Sℓᵐ(x)` against which
the weak eigen-equation can be projected onto angular sector `(ℓ, m)` (the surface harmonic
`Yℓᵐ` itself is not smooth enough to serve as such a test function).

## Main statements

* `solidHarmonicNat` — the Cartesian definition (order `m : ℕ`).
* `solidHarmonicNat_sphereChart` — the chart identity
  `Sℓᵐ(sphereChart r θ φ) = r^ℓ Yℓᵐ(θ, φ)`.
* `solidHarmonicNat_contDiffOn` — smoothness on `ℝ³ ∖ {0}`.
-/

open Complex
open scoped ContDiff

namespace Spectra.SphericalHarmonics

open Spectra.QuantumMechanics.Hydrogen (sphereChart norm_sphereChart)

/-- **Regular solid harmonic** (Cartesian, non-negative order `m`):
`Sℓᵐ(x) = Nℓᵐ · (−1)^m/(2^ℓ ℓ!) · (x₀+i x₁)^m · ‖x‖^{ℓ−m} · Q(x₂/‖x‖)`, where
`Q = d^{ℓ+m}/dt^{ℓ+m}(t²−1)^ℓ`.  Equals `r^ℓ Yℓᵐ` on the chart and is smooth away
from the origin.

The exponent `ℓ − m` is truncated `ℕ` subtraction, so for the unphysical range `m > ℓ` it
clamps to `0` (the radial factor becomes `‖x‖^0 = 1`); on the physical range `m ≤ ℓ` nothing
is clamped. -/
noncomputable def solidHarmonicNat (ℓ m : ℕ) (x : Spectra.Sobolev.R3) : ℂ :=
  (sphericalNorm ℓ m : ℂ) * ((-1 : ℂ) ^ m / (2 ^ ℓ * ℓ.factorial : ℂ))
    * (↑(x 0) + I * ↑(x 1)) ^ m * (↑‖x‖ : ℂ) ^ (ℓ - m)
    * (((rodriguesDeriv ℓ (ℓ + m)).eval (x 2 / ‖x‖) : ℝ) : ℂ)

/-- **Chart identity.** On the spherical chart the solid harmonic reduces to `r^ℓ` times the
surface harmonic: `solidHarmonicNat ℓ m (sphereChart r θ φ) = r^ℓ · Yℓᵐ(θ,φ)`. -/
lemma solidHarmonicNat_sphereChart (ℓ m : ℕ) (hm : m ≤ ℓ) {r θ φ : ℝ}
    (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    solidHarmonicNat ℓ m (sphereChart r θ φ)
      = (r : ℂ) ^ ℓ * SphericalHarmonic ℓ (m : ℤ) (by simpa using hm) (θ, φ) := by
  have hsin : Real.sin θ ≥ 0 := Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, hθ.2.le⟩
  -- chart components
  have hx0 : (sphereChart r θ φ) 0 = r * Real.sin θ * Real.cos φ := by simp [sphereChart]
  have hx1 : (sphereChart r θ φ) 1 = r * Real.sin θ * Real.sin φ := by simp [sphereChart]
  have hx2 : (sphereChart r θ φ) 2 = r * Real.cos θ := by simp [sphereChart]
  have hnorm : ‖sphereChart r θ φ‖ = r := by rw [norm_sphereChart, abs_of_pos hr]
  -- `√(1 - cos²) = sin` on `(0, π)`
  have hsqrt : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [show (1 : ℝ) - Real.cos θ ^ 2 = Real.sin θ ^ 2 by
      linear_combination -Real.sin_sq_add_cos_sq θ, Real.sqrt_sq hsin]
  -- the `(x₀ + i x₁)^m = (r sin θ)^m e^{imφ}` factor
  have hexp : (↑(r * Real.sin θ * Real.cos φ) + I * ↑(r * Real.sin θ * Real.sin φ)) ^ m
      = (↑r * ↑(Real.sin θ)) ^ m * Complex.exp (I * (m : ℂ) * (φ : ℂ)) := by
    have he : (↑(Real.cos φ) : ℂ) + I * ↑(Real.sin φ) = Complex.exp (I * (φ : ℂ)) := by
      rw [mul_comm I (φ : ℂ), Complex.exp_mul_I]; push_cast; ring
    rw [show (↑(r * Real.sin θ * Real.cos φ) + I * ↑(r * Real.sin θ * Real.sin φ) : ℂ)
        = (↑r * ↑(Real.sin θ)) * (↑(Real.cos φ) + I * ↑(Real.sin φ)) by push_cast; ring,
      he, mul_pow, ← Complex.exp_nat_mul,
      show (↑m : ℂ) * (I * ↑φ) = I * ↑m * ↑φ from by ring]
  rw [solidHarmonicNat, hx0, hx1, hx2, hnorm, SphericalHarmonic, AssociatedLegendre,
    if_pos (Int.natCast_nonneg m), Int.toNat_natCast, assocLegendreNat, hexp]
  have hrc : (↑r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [show r * Real.cos θ / r = Real.cos θ by field_simp, hsqrt]
  have hrpow : (↑r : ℂ) ^ (ℓ - m) = (↑r : ℂ) ^ ℓ / (↑r : ℂ) ^ m := by
    rw [eq_div_iff (pow_ne_zero m hrc), ← pow_add, Nat.sub_add_cancel hm]
  push_cast
  rw [hrpow]
  field_simp
  ring

/-- **Smoothness.** The solid harmonic is `C^∞` away from the origin: it is a polynomial in
`(x₀, x₁)`, times a power of `‖x‖`, times a polynomial in `x₂/‖x‖`, each smooth on
`ℝ³ ∖ {0}`. -/
lemma solidHarmonicNat_contDiffOn (ℓ m : ℕ) :
    ContDiffOn ℝ ∞ (solidHarmonicNat ℓ m) {(0 : Spectra.Sobolev.R3)}ᶜ := by
  have hQ : ContDiff ℝ ∞ (fun t : ℝ => (rodriguesDeriv ℓ (ℓ + m)).eval t) := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      using Polynomial.contDiff_aeval (𝕜 := ℝ) (rodriguesDeriv ℓ (ℓ + m)) ∞
  intro x hx
  have hx0 : x ≠ 0 := hx
  have hcoord : ∀ i : Fin 3, ContDiffAt ℝ ∞ (fun y : Spectra.Sobolev.R3 => (y i : ℝ)) x :=
    fun i => (contDiff_euclidean.mp contDiff_id i).contDiffAt
  have hnorm : ContDiffAt ℝ ∞ (fun y : Spectra.Sobolev.R3 => ‖y‖) x := contDiffAt_norm ℝ hx0
  have hnorm0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  have hA : ContDiffAt ℝ ∞ (fun y : Spectra.Sobolev.R3 => (↑(y 0) + I * ↑(y 1)) ^ m) x :=
    (((hcoord 0).continuousLinearMap_comp Complex.ofRealCLM).add
      (contDiffAt_const.mul ((hcoord 1).continuousLinearMap_comp Complex.ofRealCLM))).pow m
  have hB : ContDiffAt ℝ ∞ (fun y : Spectra.Sobolev.R3 => (↑‖y‖ : ℂ) ^ (ℓ - m)) x :=
    (hnorm.continuousLinearMap_comp Complex.ofRealCLM).pow (ℓ - m)
  have hC : ContDiffAt ℝ ∞
      (fun y : Spectra.Sobolev.R3 => (((rodriguesDeriv ℓ (ℓ + m)).eval (y 2 / ‖y‖) : ℝ) : ℂ)) x :=
    ((hQ.contDiffAt.comp x ((hcoord 2).div hnorm hnorm0)).continuousLinearMap_comp
      Complex.ofRealCLM)
  exact (((contDiffAt_const.mul hA).mul hB).mul hC).contDiffWithinAt

end Spectra.SphericalHarmonics

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SeparatedEigenfunction.Profile

/-!
# Separated hydrogen eigenfunctions: Cartesian eigenpairs

This file turns the local spherical-coordinate eigen-equation into an a.e. Cartesian
eigen-equation and transports the named degeneracy family to genuine Hamiltonian eigenvectors
of the `Z = 1` hydrogen Hamiltonian at `Eₙ = −1/(2n²)`.

## Main statements

* `separated_eigen_ae`: the separated eigenfunction solves `Σⱼ ∂ⱼ²Ψ = −2(Eₙ + 1/‖x‖)·Ψ`
  `volume`-a.e., upgraded from the chart-level identity via a.e. chart coverage.
* `chartRealization_symm_eigenfunction_eq_separated`: the Cartesian transport of the abstract
  spherical eigenfunction equals the concrete separated product a.e.
* `hydrogen_bound_state_separated`: for `1 ≤ ℓ < n`, `|m| ≤ ℓ`, the separated eigenfunction is a
  genuine `H²` eigenvector at `Eₙ`.
* `chartRealization_symm_eigenfunction_eigenpair`: the transported named eigenfunction is an `H²`
  eigenvector at `Eₙ` for every `ℓ < n` and every integer `m ∈ {−ℓ,…,ℓ}` (negative `m` via
  Condon–Shortley conjugation).
* `degenFamily_mem_ker`: every member of the degeneracy family `degenFamily n`, transported to
  Cartesian `L²(ℝ³)`, is a genuine `H²` eigenvector at `Eₙ` (all `n²` states).
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory MeasureTheory.Measure Real Complex Filter InnerProductSpace
open QuantumMechanics.Hydrogen.RadialEq
open Spectra.QuantumMechanics.Hydrogen Spectra.SphericalHarmonics Spectra.Sobolev
open Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)
open scoped Topology ContDiff Laplacian

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
  set q : ℝ × ℝ := (sphereChartInv (sphereChart r θ φ)).2 with _hq
  have hqeq : q = (q.1, q.2) := rfl
  rw [hqeq, hpolar, hk, sphericalHarmonic_eq, sphericalHarmonic_eq]
  congr 1
  rw [show I * (m : ℂ) * ((φ + 2 * Real.pi * k : ℝ) : ℂ)
      = I * (m : ℂ) * (φ : ℂ) + (m * k : ℤ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## Identifying the separated eigenfunction with the spherical eigenfunction

`hydrogenEigenfunction n ℓ ↑m hn hm'` lives on the *spherical* `L²` side
(`Decomposition.l2R3`).  Transporting it back to Cartesian `L²(ℝ³)` through the chart
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
      (ψ : Spectra.Sobolev.l2R3) ≠ 0 ∧
      (⇑(ψ : Spectra.Sobolev.l2R3) =ᵐ[volume] separatedEigenfunction n ℓ m hn) ∧
      hydrogenHamiltonian ⟨1, one_pos⟩ ψ
        = ((hydrogenEigenvalue n (by omega) : ℝ) : ℂ) • (ψ : Spectra.Sobolev.l2R3) := by
  classical
  set p : CoulombParams := ⟨1, one_pos⟩ with hp
  set E : ℝ := hydrogenEigenvalue n (by omega) with _hE_def
  set Ψ : Spectra.Sobolev.l2R3 := (memLp_separated n ℓ m hn hm hℓ).toLp _ with _hΨ_def
  have hΨ : ⇑Ψ =ᵐ[volume] separatedEigenfunction n ℓ m hn :=
    (memLp_separated n ℓ m hn hm hℓ).coeFn_toLp
  -- abbreviations for the classical second partials (the L² witnesses)
  set d2 : Fin 3 → Fin 3 → Spectra.Sobolev.l2R3 :=
    fun i j => (memLp_separated_second n ℓ m hn hm hℓ i j).toLp _ with _hd2_def
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
    have hYzero : ∀ θ φ : ℝ, θ ∈ Set.Ioo 0 Real.pi →
      SphericalHarmonic ℓ (m : ℤ) hm' (θ, φ) = 0 := by
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

The reverse direction is now assembled at the level of the *named* eigenfunctions
`hydrogenEigenfunction n ℓ m`: transported back to Cartesian `L²` via `chartRealization.symm`
each is a genuine `H²` eigenvector of the `Z = 1` hydrogen Hamiltonian at `Eₙ = −1/(2n²)`.
This holds for **every** `ℓ < n` and **every** `m ∈ {−ℓ,…,ℓ}` (including `m < 0`, handled by
the Condon–Shortley conjugation), and so for the whole `degenFamily n`. -/

/-- **Eigenpair transfer along an `L²` equality.**  If a domain element `ψ` is an eigenvector
at `E`, then any `L²` element equal to `↑ψ` is itself in the domain and an eigenvector at `E`. -/
lemma eigvec_transfer (p : CoulombParams) (E : ℝ) (w : Spectra.Sobolev.l2R3)
    (ψ : (hydrogenHamiltonian p).domain) (hw : (ψ : Spectra.Sobolev.l2R3) = w)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3)) :
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
  -- `deriv g = c · deriv Rc`, `deriv (deriv g) = c · deriv (deriv Rc)`, both reduced to `R'`, `R''`
  have hg_eq : g = fun s => c * Rc n 0 hn0 s := rfl
  have hderiv_g : deriv g = fun s => c * deriv (Rc n 0 hn0) s := by
    funext s
    rw [hg_eq, deriv_const_mul _
      ((contDiff_Rc n 0 hn0).differentiable (by norm_num)).differentiableAt]
  have hderiv2_g : deriv (deriv g)
      = fun s => c * ((deriv (deriv (hydrogenRadialWavefunction n 0 hn0)) s : ℝ) : ℂ) := by
    funext s
    rw [hderiv_g,
      deriv_const_mul _ ((contDiff_Rc n 0 hn0).differentiable_deriv_two).differentiableAt,
      deriv2_Rc n 0 hn0]
  -- rewrite `deriv g` into the `ℝ→ℂ`-cast form (for the norm bound)
  have hderiv_g' : deriv g = fun s => c *
    ((deriv (hydrogenRadialWavefunction n 0 hn0) s : ℝ) : ℂ) := by
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
  set Ψ : Spectra.Sobolev.l2R3 := chartRealization.symm (hydrogenEigenfunction n 0 0 hn0 hm)
    with _hΨ_def
  have hΨ : ⇑Ψ =ᵐ[volume] fun x : R3 => g ‖x‖ :=
    chartRealization_symm_eigenfunction_coeFn n hn0 hm
  have _hΨ0 : Ψ ≠ 0 := by
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
  -- assemble `Ψ ∈ H²` & eigenpair *for the explicit `Ψ`* (mirrors `bound_state_of_radial_profile`)
  set p : CoulombParams := ⟨1, one_pos⟩ with hp
  set E : ℝ := hydrogenEigenvalue n hn with hE_def
  have heigen' : ∀ x : R3, x ≠ 0 →
      ∑ j : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun z => g ‖z‖) y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single j 1)
        = (-2 : ℂ) * ((E : ℂ) + (p.Z : ℂ) * (‖x‖ : ℂ)⁻¹) * g ‖x‖ := by
    intro x hx
    have := heigen x hx
    simpa [hp, hE_def] using this
  set d2 : Fin 3 → Fin 3 → Spectra.Sobolev.l2R3 :=
    fun i j => (memLp_second_deriv g hg ha hbd1 hbd2 i j).toLp _ with _hd2_def
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
  change hydrogenHamiltonian p ⟨Ψ, hH2⟩ = ((E : ℝ) : ℂ) • Ψ
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
    have heq : (ψ : Spectra.Sobolev.l2R3)
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
lemma chartRealization_symm_star (v : Decomposition.l2R3) :
    chartRealization.symm (star v) = star (chartRealization.symm v) := by
  refine Lp.ext ?_
  -- LHS coeFn: `(star v) ∘ sphereChartInv`, a.e.
  have hL := chartRealization_symm_coeFn (star v)
  have hstarv := Lp.coeFn_star v
  have hstarv' := (measurePreserving_sphereChartInv.quasiMeasurePreserving).ae_eq_comp hstarv
  -- RHS coeFn: `star (⇑(chartRealization.symm v))`,
  -- and `⇑(chartRealization.symm v) = v ∘ sphereChartInv`
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
    (heig : hydrogenHamiltonian p χ = (E : ℂ) • (χ : Spectra.Sobolev.l2R3)) :
    ∃ hmem : c • (χ : Spectra.Sobolev.l2R3) ∈ (hydrogenHamiltonian p).domain,
      hydrogenHamiltonian p ⟨c • (χ : Spectra.Sobolev.l2R3), hmem⟩
        = (E : ℂ) • (c • (χ : Spectra.Sobolev.l2R3)) := by
  refine ⟨(c • χ).2, ?_⟩
  have hcoe : ((c • χ : (hydrogenHamiltonian p).domain) : Spectra.Sobolev.l2R3)
      = c • (χ : Spectra.Sobolev.l2R3) := rfl
  have hχeq : (⟨c • (χ : Spectra.Sobolev.l2R3), (c • χ).2⟩ : (hydrogenHamiltonian p).domain)
      = c • χ := Subtype.ext hcoe.symm
  rw [hχeq, LinearPMap.map_smul, heig]
  exact smul_comm c ((E : ℝ) : ℂ) (χ : Spectra.Sobolev.l2R3)

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
    obtain ⟨hmemPos, heigPos⟩ :=
      chartRealization_symm_eigenfunction_eigenpair_nat n ℓ m hn hmℓ hn1 hm'
    set psiPos : (hydrogenHamiltonian ⟨1, one_pos⟩).domain :=
      ⟨chartRealization.symm (hydrogenEigenfunction n ℓ (m : ℤ) hn hm'), hmemPos⟩ with _hpsiPos_def
    -- `star psiPos` is an eigenvector at the (real) eigenvalue `Eₙ`
    have hstar_eig :=
      hydrogenHamiltonian_star ⟨1, one_pos⟩ (hydrogenEigenvalue n hn1) psiPos heigPos
    set χ : (hydrogenHamiltonian ⟨1, one_pos⟩).domain :=
      ⟨star (psiPos : Spectra.Sobolev.l2R3), memSobolevH2_star _ psiPos.2⟩ with _hχ_def
    -- the Condon–Shortley constant `κ ≠ 0`
    set κ : ℝ := sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)
        / (sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))) with _hκ_def
    have hκne : κ ≠ 0 := div_ne_zero
      (mul_ne_zero (sphericalNorm_pos ℓ (m : ℤ)).ne' (reflectionFactor_ne_zero ℓ (m : ℤ)))
      (mul_ne_zero (sphericalNorm_pos ℓ (-(m : ℤ))).ne'
        (reflectionFactor_ne_zero ℓ (-(m : ℤ))))
    -- `eigfn n ℓ M = κ⁻¹ • star (eigfn n ℓ m)`, so its chart-transport is `κ⁻¹ • star ↑psiPos`
    have hconj := star_hydrogenEigenfunction n ℓ m hn hmℓ hm' hM
    have hMtransport : chartRealization.symm (hydrogenEigenfunction n ℓ (-(m : ℤ)) hn hM)
        = (((κ⁻¹ : ℝ) : ℂ)) • (χ : Spectra.Sobolev.l2R3) := by
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

end QuantumMechanics.Hydrogen.Spectrum

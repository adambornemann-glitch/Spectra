/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Forward
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SectorReductionLocal
import Spectra.QuantumMechanics.Hydrogen.Spectrum.RadialEigenfunction.Basic
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Regularity

/-!
# Sector projection of the Cartesian weak eigenequation (forward direction, brick 2)

The mathematical heart of the **forward direction** (`eigenpair ⟹ E = E_n`) of
`hydrogen_discrete_spectrum`: projecting the Cartesian weak eigenequation onto a single angular
sector to extract a *radial* weak equation.

Given an `H²` eigenfunction `H ψ = E ψ` of `H = −½Δ − Z/r`, the argument tests against the smooth
solid-harmonic function `χ(‖x‖) · solidHarmonicNat ℓ m x` (a globally `C∞`, compactly supported
separated test function).  Combining

* `cartesian_weak_eigen` — the weak eigenequation with all derivatives on the test function,
* `solidTest_reduces_half` (via `solidTest_chart_value`) — the pointwise sector reduction,
* the spherical change of variables (`measurePreserving_sphereChart`, `chartRealization_coeFn`),
* the spherical-harmonic conjugation relation (`sphericalHarmonic_conj`),

yields `sector_projection_radial`: the charge-`Z` radial Hamiltonian (minus `E`) applied to the
radial profile `χ(a)·a^ℓ`, paired against the angular coefficient `c_{ℓ,-m}` of `ψ`'s spherical
realization, integrates to `0` against `r² dr`.  This is exactly the weak radial equation consumed
by `forward_bridge → classical_of_weak_ode → radial_classical_of_logCoord → radial_quantization_Z`.

## Main statements

* `sphericalHarmonic_conj` — `conj(Y_ℓ^m) = κ · Y_ℓ^{-m}` (Condon–Shortley; `κ ≠ 0`).
* `solidTest_contDiff_infty`, `solidTest_hasCompactSupport` — the solid-harmonic test function is
  `C∞` with compact support.
* `weak_eigen_combined` — the combined weak eigenequation `∫ ψ·(−½∑∂² + V − E)φ = 0`.
* `solidTest_chart_value` — the pointwise chart value of the operator on the solid-harmonic test.
* `sector_projection_radial` — the sector-projected radial weak equation.
* `sector_weak_part`, `sector_hweak`, `sector_sweak` — the realified radial weak equation, bridged
  through `forward_bridge` into the `s`-weak form consumed by `classical_of_weak_ode`.
* `hydrogenHamiltonian_star`, `coeffFun_star`, `exists_nonzero_sector` — conjugation symmetry of the
  eigenproblem, used to produce a nonzero non-positive-`m` sector coefficient.
* `radial_bc_of_logCoord` — the at-origin Dirichlet boundary dichotomy `r·c₀(log r) → 0`, via
  convexity of `eˢ·c₀²` near `−∞`.
* `forward_eigenvalue` — a nonzero `H²` eigenpair with `E < 0` forces `E = eigenvalue p n hn`.
* `no_positive_eigenvalue` — no nonzero `L²` eigenfunction exists at energy `E ≥ 0`.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open Spectra.Sobolev
open Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics
open scoped Topology ENNReal ContDiff

/-- **Conjugation of a spherical harmonic.** `conj(Y_ℓ^m) = κ · Y_ℓ^{-m}` for a nonzero real
constant `κ` (the Condon–Shortley relation; the exact value is irrelevant downstream — only
`κ ≠ 0` matters). -/
lemma sphericalHarmonic_conj (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ (ℓ : ℤ)) (hm' : |(-m)| ≤ (ℓ : ℤ))
    (p : ℝ × ℝ) :
    (starRingEnd ℂ) (SphericalHarmonic ℓ m hm p)
      = ((sphericalNorm ℓ m * reflectionFactor ℓ m
            / (sphericalNorm ℓ (-m) * reflectionFactor ℓ (-m)) : ℝ) : ℂ)
        * SphericalHarmonic ℓ (-m) hm' p := by
  obtain ⟨a, b⟩ := p
  rw [sphericalHarmonic_eq ℓ m hm a b, sphericalHarmonic_eq ℓ (-m) hm' a b]
  -- conj of the real coefficient × conj of the exponential
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  -- conj(I·m·b) = I·(-m)·b
  have hconj : (starRingEnd ℂ) (I * (m : ℂ) * (b : ℂ)) = I * ((-m : ℤ) : ℂ) * (b : ℂ) := by
    rw [map_mul, map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal]
    push_cast; ring
  rw [hconj]
  -- match the real coefficients (`(-m).natAbs = m.natAbs`, `reflectionFactor ≠ 0`)
  have hC : sphericalNorm ℓ (-m) ≠ 0 := (sphericalNorm_pos ℓ (-m)).ne'
  have hD : reflectionFactor ℓ (-m) ≠ 0 := reflectionFactor_ne_zero ℓ (-m)
  have hnatabs : (-m).natAbs = m.natAbs := Int.natAbs_neg m
  rw [hnatabs, ← mul_assoc, ← Complex.ofReal_mul]
  congr 1
  norm_cast
  field_simp

/-- The solid-harmonic test function is globally `C∞` (the cutoff `χ` vanishes near the origin,
where `solidHarmonicNat` is only smooth off `{0}`). -/
lemma solidTest_contDiff_infty (ℓ m : ℕ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ᶠ s in 𝓝 (0 : ℝ), χ s = 0) :
    ContDiff ℝ ∞ (fun x : R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · have hev : (fun x : R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) =ᶠ[𝓝 x] (fun _ => 0) := by
      have htend : Filter.Tendsto (fun y : R3 => ‖y‖) (𝓝 x) (𝓝 0) := by
        rw [hx]; simpa using (continuous_norm (E := R3)).tendsto 0
      filter_upwards [htend.eventually hχ0] with y hy; simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hnorm : ContDiffAt ℝ ∞ (fun y : R3 => ‖y‖) x := contDiffAt_norm ℝ hx
    have h1 : ContDiffAt ℝ ∞ (fun y : R3 => (χ ‖y‖ : ℂ)) x :=
      Complex.ofRealCLM.contDiff.comp_contDiffAt x (hχ.comp_contDiffAt x hnorm)
    have h2 : ContDiffAt ℝ ∞ (solidHarmonicNat ℓ m) x :=
      (solidHarmonicNat_contDiffOn ℓ m).contDiffAt (isOpen_compl_singleton.mem_nhds hx)
    exact h1.mul h2

/-- The solid-harmonic test function has compact support when `χ` does. -/
lemma solidTest_hasCompactSupport (ℓ m : ℕ) (χ : ℝ → ℝ) (hχcs : HasCompactSupport χ) :
    HasCompactSupport (fun x : R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) := by
  obtain ⟨R, hR⟩ := hχcs.isBounded.subset_closedBall (0 : ℝ)
  apply HasCompactSupport.intro (isCompact_closedBall (0 : R3) R)
  intro x hx
  have hxR : R < ‖x‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hnotmem : ‖x‖ ∉ tsupport χ := fun h => by
    have := hR h
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact absurd (le_trans (le_abs_self _) this) (not_le.mpr hxR)
  rw [image_eq_zero_of_notMem_tsupport hnotmem, Complex.ofReal_zero, zero_mul]

/-- **Step A — the combined weak eigenequation.** For an `H²` eigenfunction `Hψ = Eψ` and any
smooth compactly supported test `φ`, pairing `ψ` against `(−½Δ + V − E)φ` (with `Δ` written as the
classical `∑ᵢ ∂ᵢ²`) gives `0`.  Works for arbitrary `φ`; the solid-harmonic structure enters only
later when the integrand is reduced on a sector. -/
lemma weak_eigen_combined (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (φ : R3 → ℂ) (hφ : ContDiff ℝ ∞ φ) (hφ0 : HasCompactSupport φ) :
    ∫ x, (ψ : Spectra.Sobolev.l2R3) x *
      (-(1 / 2 : ℂ) * (∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1))
        + (coulombMultiplier p x : ℂ) * φ x - (E : ℂ) * φ x) = 0 := by
  -- the Cartesian weak eigenequation: `-∫ ψ·(∑∂²φ) = ∫ 2(E−V)ψφ`
  have hcwe := cartesian_weak_eigen p E ψ heig φ hφ hφ0
  have hφ2 : MemLp φ 2 volume := memLp_of_smooth_compactSupport φ hφ hφ0
  -- integrability of `ψ·(∑∂²φ)`
  have hlapMemLp : MemLp (fun x => ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))
      2 volume := by
    refine memLp_finsetSum _ (fun i _ => ?_)
    exact memLp_partialDeriv (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) i
      (contDiff_partialDeriv φ i hφ) (hasCompactSupport_partialDeriv φ i hφ0)
  have hint_lap : Integrable (fun x => (ψ : Spectra.Sobolev.l2R3) x * ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) :=
    memLp_one_iff_integrable.mp (MemLp.mul' (r := 1)
      hlapMemLp (Lp.memLp (ψ : Spectra.Sobolev.l2R3)))
  -- integrability of the RHS integrand: a.e. equal to the `L²·L²` product `(weakLaplacian ψ)·φ`
  have hwe := weak_eigenequation_ae p E ψ heig
  have hint_wlφ : Integrable (fun x => ⇑(weakLaplacian (ψ : Spectra.Sobolev.l2R3) ψ.2) x * φ x) :=
    memLp_one_iff_integrable.mp
      (MemLp.mul' (r := 1) hφ2 (Lp.memLp (weakLaplacian (ψ : Spectra.Sobolev.l2R3) ψ.2)))
  have hint_rhs : Integrable (fun x => (2 : ℂ) * ((E : ℂ) - (coulombMultiplier p x : ℂ))
      * (ψ : Spectra.Sobolev.l2R3) x * φ x) := by
    refine hint_wlφ.congr ?_
    filter_upwards [hwe] with x hx; rw [hx]
  -- rewrite the goal integral as `-(1/2)·(∫ ψ·∑∂²φ) + -(1/2)·(∫ 2(E−V)ψφ)`
  have hrw : (∫ x, (ψ : Spectra.Sobolev.l2R3) x *
        (-(1 / 2 : ℂ) * (∑ i : Fin 3,
            fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single i 1))
          + (coulombMultiplier p x : ℂ) * φ x - (E : ℂ) * φ x))
      = -(1 / 2 : ℂ) * (∫ x, (ψ : Spectra.Sobolev.l2R3) x * ∑ i : Fin 3,
            fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single i 1))
        + -(1 / 2 : ℂ) * (∫ x, (2 : ℂ) * ((E : ℂ) - (coulombMultiplier p x : ℂ))
            * (ψ : Spectra.Sobolev.l2R3) x * φ x) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hint_lap.const_mul _) (hint_rhs.const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    push_cast; ring
  rw [hrw]
  linear_combination (1 / 2 : ℂ) * hcwe

/-- **The pointwise chart value of the operator part.** At a physical chart point
`x = sphereChart r θ φ` (`r > 0`, `θ ∈ (0,π)`), the operator `(−½∑∂² + V − E)` applied to the
solid-harmonic test function separates as `Q(r)·Yℓᵐ(θ,φ)`, where `Q` is the charge-`Z` radial
Hamiltonian (minus `E`) acting on the radial profile `χ(a)·a^ℓ`. -/
lemma solidTest_chart_value (p : CoulombParams) (E : ℝ) (ℓ m : ℕ) (hm : m ≤ ℓ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ᶠ s in 𝓝 (0 : ℝ), χ s = 0)
    {r θ ph : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    -(1 / 2 : ℂ) * (∑ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ (fun x => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) y
            (EuclideanSpace.single i 1)) (sphereChart r θ ph) (EuclideanSpace.single i 1))
      + (coulombMultiplier p (sphereChart r θ ph) : ℂ)
          * ((χ ‖sphereChart r θ ph‖ : ℂ) * solidHarmonicNat ℓ m (sphereChart r θ ph))
      - (E : ℂ) * ((χ ‖sphereChart r θ ph‖ : ℂ) * solidHarmonicNat ℓ m (sphereChart r θ ph))
    = ((-(1 / 2 : ℂ)) * deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r
          - (1 / (r : ℂ)) * deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
          + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (p.Z : ℂ) / (r : ℂ))
            * ((χ r : ℂ) * (r : ℂ) ^ ℓ)
          - (E : ℂ) * ((χ r : ℂ) * (r : ℂ) ^ ℓ))
        * SphericalHarmonic ℓ (m : ℤ) (by simpa using hm) (θ, ph) := by
  have hφsm : ContDiff ℝ ∞ (fun x : R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) :=
    solidTest_contDiff_infty ℓ m χ hχ hχ0
  -- the `∑∂²` form equals Mathlib's `Δ`
  have hdiff : DifferentiableAt ℝ
      (fderiv ℝ (fun x : R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x)) (sphereChart r θ ph) :=
    ((contDiff_infty_iff_fderiv.mp hφsm).2.differentiable (by norm_num)).differentiableAt
  rw [← laplacian_eq_sum_fderiv (fun x : R3 => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x) hdiff]
  -- the half-Laplacian sector reduction
  have hred := solidTest_reduces_half p ℓ m hm χ hχ hχ0 (φ := ph) hr hθ
  -- value of the test function at the chart point
  have hval : (χ ‖sphereChart r θ ph‖ : ℂ) * solidHarmonicNat ℓ m (sphereChart r θ ph)
      = ((χ r : ℂ) * (r : ℂ) ^ ℓ) * SphericalHarmonic ℓ (m : ℤ) (by simpa using hm) (θ, ph) := by
    rw [norm_sphereChart, abs_of_pos hr, solidHarmonicNat_sphereChart ℓ m hm hr hθ]
    ring
  rw [hval] at hred ⊢
  linear_combination hred

/-- **Brick 2 — the sector-projection radial weak equation.** Projecting the Cartesian weak
eigenequation onto the `(ℓ, m)` sector (via the solid-harmonic test) yields the radial weak
equation: the charge-`Z` radial Hamiltonian (minus `E`) applied to `χ(a)·a^ℓ`, paired against the
angular coefficient `c_{ℓ,-m}` of `ψ`'s spherical realization, integrates to `0` over `r²dr`. -/
theorem sector_projection_radial (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ᶠ s in 𝓝 (0 : ℝ), χ s = 0)
    (hχcs : HasCompactSupport χ) :
    ∫ r, ((-(1 / 2 : ℂ)) * deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r
            - (1 / (r : ℂ)) * deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
            + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (p.Z : ℂ) / (r : ℂ))
              * ((χ r : ℂ) * (r : ℂ) ^ ℓ)
            - (E : ℂ) * ((χ r : ℂ) * (r : ℂ) ^ ℓ))
          * coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
              (chartRealization (ψ : Spectra.Sobolev.l2R3)) r
        ∂radialMeasure = 0 := by
  classical
  -- abbreviations
  have hm' : |(-(m : ℤ))| ≤ (ℓ : ℤ) := by rw [abs_neg]; simpa using hm
  have hmI : |(m : ℤ)| ≤ (ℓ : ℤ) := by simpa using hm
  set j : HarmonicIdx := ⟨ℓ, -(m : ℤ), hm'⟩ with hj
  set Y : ℝ × ℝ → ℂ := SphericalHarmonic ℓ (m : ℤ) hmI with hY
  set φ : R3 → ℂ := fun x => (χ ‖x‖ : ℂ) * solidHarmonicNat ℓ m x with hφ
  set Qfun : ℝ → ℂ := fun r => (-(1 / 2 : ℂ)) * deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r
        - (1 / (r : ℂ)) * deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
        + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (p.Z : ℂ) / (r : ℂ))
          * ((χ r : ℂ) * (r : ℂ) ^ ℓ)
        - (E : ℂ) * ((χ r : ℂ) * (r : ℂ) ^ ℓ) with hQfun
  set c : ℝ → ℂ := coeffFun j (chartRealization (ψ : Spectra.Sobolev.l2R3)) with hc
  -- conjugation constant κ ≠ 0
  set κ : ℝ := sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))
    / (sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)) with hκ
  have hκne : (κ : ℝ) ≠ 0 := by
    rw [hκ]
    exact div_ne_zero
      (mul_ne_zero (sphericalNorm_pos ℓ (-(m:ℤ))).ne' (reflectionFactor_ne_zero ℓ _))
      (mul_ne_zero (sphericalNorm_pos ℓ (m:ℤ)).ne' (reflectionFactor_ne_zero ℓ _))
  -- the solid-harmonic test function
  have hφsm : ContDiff ℝ ∞ φ := solidTest_contDiff_infty ℓ m χ hχ hχ0
  have hφcs' : HasCompactSupport φ := solidTest_hasCompactSupport ℓ m χ hχcs
  -- Step A: the combined weak eigenequation
  have hA := weak_eigen_combined p E ψ heig φ hφsm hφcs'
  -- the volume integrand G
  set G : R3 → ℂ := fun x => (ψ : Spectra.Sobolev.l2R3) x *
      (-(1 / 2 : ℂ) * (∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single i 1))
        + (coulombMultiplier p x : ℂ) * φ x - (E : ℂ) * φ x) with hG
  -- the spherical integrand F
  set F : ℝ × ℝ × ℝ → ℂ := fun q =>
    chartRealization (ψ : Spectra.Sobolev.l2R3) q * (Qfun q.1 * Y q.2)
    with hF
  -- (P1) integrability of `G`
  have hGint : Integrable G volume := by
    have hφ2 : MemLp φ 2 volume := memLp_of_smooth_compactSupport φ hφsm hφcs'
    have hlapMemLp : MemLp (fun x => ∑ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))
        2 volume := by
      refine memLp_finsetSum _ (fun i _ => ?_)
      exact memLp_partialDeriv (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) i
        (contDiff_partialDeriv φ i hφsm) (hasCompactSupport_partialDeriv φ i hφcs')
    have hint_lap : Integrable (fun x => (ψ : Spectra.Sobolev.l2R3) x * ∑ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) :=
      memLp_one_iff_integrable.mp (MemLp.mul' (r := 1)
        hlapMemLp (Lp.memLp (ψ : Spectra.Sobolev.l2R3)))
    have hwe := weak_eigenequation_ae p E ψ heig
    have hint_wlφ : Integrable (fun x => ⇑(weakLaplacian (ψ : Spectra.Sobolev.l2R3) ψ.2) x * φ x) :=
      memLp_one_iff_integrable.mp
        (MemLp.mul' (r := 1) hφ2 (Lp.memLp (weakLaplacian (ψ : Spectra.Sobolev.l2R3) ψ.2)))
    have hint_rhs : Integrable (fun x => (2 : ℂ) * ((E : ℂ) - (coulombMultiplier p x : ℂ))
        * (ψ : Spectra.Sobolev.l2R3) x * φ x) :=
      hint_wlφ.congr (by filter_upwards [hwe] with x hx; rw [hx])
    refine ((hint_lap.add hint_rhs).const_mul (-(1 / 2 : ℂ))).congr (ae_of_all _ fun x => ?_)
    simp only [hG, Pi.add_apply]
    ring
  -- (P2) change of variables `∫ G ∂vol = ∫ G∘sphereChart ∂(rad×sph)`
  have hmap : (∫ x, G x ∂(volume : Measure R3))
      = ∫ q, G (sphereChart q.1 q.2.1 q.2.2) ∂(radialMeasure.prod sphereMeasure) := by
    have hsm := integral_map (μ := radialMeasure.prod sphereMeasure)
      (φ := fun q : ℝ × ℝ × ℝ => sphereChart q.1 q.2.1 q.2.2) (f := G)
      measurable_sphereChartProd.aemeasurable
      (by rw [measurePreserving_sphereChart.map_eq]; exact hGint.aestronglyMeasurable)
    rw [measurePreserving_sphereChart.map_eq] at hsm
    exact hsm
  -- (P3) a.e. on the box, identify the pushed-forward integrand `= (chartReal ψ)·Q·Y`
  have hae : (fun q => G (sphereChart q.1 q.2.1 q.2.2)) =ᵐ[radialMeasure.prod sphereMeasure] F := by
    have hcr := chartRealization_coeFn (ψ : Spectra.Sobolev.l2R3)
    have hbox : ∀ᵐ q ∂(radialMeasure.prod sphereMeasure),
        q.1 ∈ Set.Ioi (0 : ℝ) ∧ q.2.1 ∈ Set.Ioo 0 Real.pi := by
      rw [radialMeasure_prod_sphereMeasure_eq]
      refine ((ae_restrict_mem (measurableSet_Ioi.prod
          (measurableSet_Ioo.prod measurableSet_Ioo))).filter_mono
        (withDensity_absolutelyContinuous _ _).ae_le).mono (fun q hq => ⟨hq.1, hq.2.1⟩)
    -- the operator identity at a physical chart point
    have hop : ∀ q : ℝ × ℝ × ℝ, q.1 ∈ Set.Ioi (0 : ℝ) → q.2.1 ∈ Set.Ioo 0 Real.pi →
        -(1 / 2 : ℂ) * (∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
              (sphereChart q.1 q.2.1 q.2.2) (EuclideanSpace.single i 1))
          + (coulombMultiplier p (sphereChart q.1 q.2.1 q.2.2) : ℂ)
          * φ (sphereChart q.1 q.2.1 q.2.2)
          - (E : ℂ) * φ (sphereChart q.1 q.2.1 q.2.2)
        = Qfun q.1 * Y q.2 := by
      intro q hr hθ
      simp only [hφ, hQfun, hY]
      exact solidTest_chart_value p E ℓ m hm χ hχ hχ0 (ph := q.2.2) hr hθ
    filter_upwards [hcr, hbox] with q hq hqbox
    simp only [hG, hF]
    rw [← hq, hop q hqbox.1 hqbox.2]
  -- (P4) integrability of `F` (transported along the measure-preserving chart)
  have hFint : Integrable F (radialMeasure.prod sphereMeasure) :=
    ((measurePreserving_sphereChart.integrable_comp hGint.aestronglyMeasurable).mpr hGint).congr hae
  -- (P5) the inner angular integral collapses to the coefficient function
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκne
  have hinner : ∀ r, (∫ u, F (r, u) ∂sphereMeasure) = (κ : ℂ)⁻¹ * (Qfun r * c r) := by
    intro r
    -- the conjugation relation `conj(Y_{ℓ,-m}) = κ · Y_{ℓ,m}`
    have hYconj : ∀ u, (starRingEnd ℂ) (harmonic j u) = (κ : ℂ) * Y u := by
      intro u
      have hsc := sphericalHarmonic_conj ℓ (-(m : ℤ)) hm' (by rw [neg_neg]; exact hmI) u
      simp only [neg_neg] at hsc
      rw [hj, hY]
      simp only [harmonic]
      rw [hsc]
    have hYconj' : ∀ u, Y u = (κ : ℂ)⁻¹ * (starRingEnd ℂ) (harmonic j u) := fun u => by
      rw [hYconj u, ← mul_assoc, inv_mul_cancel₀ hκC, one_mul]
    calc ∫ u, F (r, u) ∂sphereMeasure
        = ∫ u, (Qfun r * (κ : ℂ)⁻¹)
            * ((starRingEnd ℂ) (harmonic j u) * chartRealization (ψ : Spectra.Sobolev.l2R3) (r, u))
            ∂sphereMeasure := by
          refine integral_congr_ae (ae_of_all _ fun u => ?_)
          simp only [hF]
          rw [hYconj' u]; ring
      _ = (Qfun r * (κ : ℂ)⁻¹) * ∫ u, (starRingEnd ℂ) (harmonic j u)
            * chartRealization (ψ : Spectra.Sobolev.l2R3) (r, u) ∂sphereMeasure :=
          integral_const_mul _ _
      _ = (Qfun r * (κ : ℂ)⁻¹) * c r := by rw [hc, coeffFun]
      _ = (κ : ℂ)⁻¹ * (Qfun r * c r) := by ring
  -- assemble the chain `∫ G = κ⁻¹ · ∫ Qfun·c`
  have hchain : (∫ x, G x ∂(volume : Measure R3))
      = (κ : ℂ)⁻¹ * ∫ r, Qfun r * c r ∂radialMeasure := by
    rw [hmap, integral_congr_ae hae, integral_prod F hFint]
    rw [show (fun r => ∫ u, F (r, u) ∂sphereMeasure) = fun r => (κ : ℂ)⁻¹ * (Qfun r * c r) from
      funext hinner, integral_const_mul]
  rw [hchain] at hA
  exact (mul_eq_zero.mp hA).resolve_left (inv_ne_zero (by exact_mod_cast hκne))

/-! ## Realification: the real radial weak equation

The conclusion `sector_projection_radial` is `ℂ`-valued, but the downstream pipeline
(`forward_bridge`, `classical_of_weak_ode`, `radial_quantization_Z`) works over `ℝ`.  Applying a
real-linear functional (`reCLM`/`imCLM`) to the projection yields the *real* radial weak equation,
in the `∫ ⬝ r² dr` form. -/

/-- `radialMeasure = r²dr` is finite on compact sets. -/
instance : IsFiniteMeasureOnCompacts radialMeasure := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨N, hN⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hbound : ∀ x ∈ K, x ^ 2 ≤ N ^ 2 := by
    intro x hx
    have := hN hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    nlinarith [abs_nonneg x, this, sq_abs x]
  rw [show radialMeasure = (volume.restrict (Set.Ioi 0)).withDensity
      (fun r => ENNReal.ofReal (r ^ 2)) from rfl, withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (x ^ 2) ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫⁻ _ in K, ENNReal.ofReal (N ^ 2) ∂(volume.restrict (Set.Ioi 0)) :=
        setLIntegral_mono (by fun_prop) (fun x hx => ENNReal.ofReal_le_ofReal (hbound x hx))
    _ = ENNReal.ofReal (N ^ 2) * (volume.restrict (Set.Ioi 0)) K := setLIntegral_const _ _
    _ < (⊤ : ℝ≥0∞) := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (Measure.restrict_le_self K) hK.measure_lt_top)

/-- A singular factor (continuous off `0`) times a function vanishing near `0` is continuous. -/
lemma cont_sing_mul {g f : ℝ → ℝ} (hg : ContinuousOn g {(0 : ℝ)}ᶜ) (hf : Continuous f)
    (h0 : ∀ᶠ r in 𝓝 (0 : ℝ), f r = 0) : Continuous (fun r => g r * f r) := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : r = 0
  · subst hr
    have hev : (fun r => g r * f r) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [h0] with r hr; rw [hr, mul_zero]
    exact (continuousAt_const).congr hev.symm
  · exact (hg.continuousAt (isOpen_compl_singleton.mem_nhds hr)).mul hf.continuousAt

/-- The `ℂ`-valued derivative of lifted real radial profile is the lift of the real derivative -/
lemma deriv_ofReal_radial (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (ℓ : ℕ) :
    (∀ r, deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
        = ((deriv (fun a => χ a * a ^ ℓ) r : ℝ) : ℂ)) ∧
    (∀ r, deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r
        = ((deriv (deriv (fun a => χ a * a ^ ℓ)) r : ℝ) : ℂ)) := by
  have hrealgC : ContDiff ℝ ∞ (fun a => χ a * a ^ ℓ) := hχ.mul (by simpa using contDiff_id.pow ℓ)
  have hgeq : (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) = (fun a => ((χ a * a ^ ℓ : ℝ) : ℂ)) := by
    funext a; push_cast; ring
  have h1 : ∀ r, deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
      = ((deriv (fun a => χ a * a ^ ℓ) r : ℝ) : ℂ) := by
    intro r
    rw [hgeq]
    exact (((hrealgC.differentiable (by norm_num)).differentiableAt).hasDerivAt.ofReal_comp).deriv
  refine ⟨h1, fun r => ?_⟩
  have hfun : deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)
      = (fun a => ((deriv (fun a => χ a * a ^ ℓ) a : ℝ) : ℂ)) := funext h1
  rw [hfun]
  have hD1C : ContDiff ℝ ∞ (deriv (fun a => χ a * a ^ ℓ)) :=
    (contDiff_infty_iff_deriv.mp hrealgC).2
  exact (((hD1C.differentiable (by norm_num)).differentiableAt).hasDerivAt.ofReal_comp).deriv

/-- Integration against `radialMeasure = r²dr` as a weighted Lebesgue integral on `(0,∞)`. -/
lemma integral_radialMeasure_eq (h : ℝ → ℝ) :
    ∫ r, h r ∂radialMeasure = ∫ r in Set.Ioi 0, h r * r ^ 2 := by
  rw [show radialMeasure = (volume.restrict (Set.Ioi 0)).withDensity
      (fun r => ENNReal.ofReal (r ^ 2)) from rfl,
    integral_withDensity_eq_integral_toReal_smul₀
      (show Measurable (fun r : ℝ => ENNReal.ofReal (r ^ 2)) by fun_prop).aemeasurable
      (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  simp only [ENNReal.toReal_ofReal (sq_nonneg r), smul_eq_mul]
  ring

/-- **Realification of the sector projection.** Applying any real-linear `L : ℂ →L[ℝ] ℝ`
(e.g. `reCLM`, `imCLM`) to `sector_projection_radial` gives the *real* radial weak equation for
`L ∘ coeffFun`, in the `∫ ⬝ r² dr` form consumed by `forward_bridge`. -/
lemma sector_weak_part (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ᶠ s in 𝓝 (0 : ℝ), χ s = 0)
    (hχcs : HasCompactSupport χ) (L : ℂ →L[ℝ] ℝ) :
    ∫ r in Set.Ioi 0,
      (-(1 / 2) * deriv (deriv (fun a => χ a * a ^ ℓ)) r - (1 / r) * deriv (fun a => χ a * a ^ ℓ) r
          + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) * (χ r * r ^ ℓ) - E * (χ r * r ^ ℓ))
        * L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
            (chartRealization (ψ : Spectra.Sobolev.l2R3)) r) * r ^ 2 = 0 := by
  have h0 := sector_projection_radial p E ψ heig ℓ m hm χ hχ hχ0 hχcs
  obtain ⟨hdc1, hdc2⟩ := deriv_ofReal_radial χ hχ ℓ
  set c : ℝ → ℂ := coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
    (chartRealization (ψ : Spectra.Sobolev.l2R3)) with _hc
  have hcML : MemLp c 2 radialMeasure := memLp_coeffFun _ _
  have hrealgC : ContDiff ℝ ∞ (fun a => χ a * a ^ ℓ) := hχ.mul (by simpa using contDiff_id.pow ℓ)
  have hrealgcont : Continuous (fun a => χ a * a ^ ℓ) := hrealgC.continuous
  have hD1cont : Continuous (deriv (fun a => χ a * a ^ ℓ)) :=
    (contDiff_infty_iff_deriv.mp hrealgC).2.continuous
  have hD2cont : Continuous (deriv (deriv (fun a => χ a * a ^ ℓ))) :=
    (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hrealgC).2)).2.continuous
  have hrealg0 : ∀ᶠ a in 𝓝 (0 : ℝ), χ a * a ^ ℓ = 0 := by
    filter_upwards [hχ0] with a ha; simp [ha]
  obtain ⟨V, hVmem, hVopen, hV0⟩ := eventually_nhds_iff.mp hrealg0
  have hderiv0 : ∀ᶠ a in 𝓝 (0 : ℝ), deriv (fun a => χ a * a ^ ℓ) a = 0 := by
    filter_upwards [hVopen.mem_nhds hV0] with a ha
    have hee : (fun a => χ a * a ^ ℓ) =ᶠ[𝓝 a] (fun _ => 0) := by
      filter_upwards [hVopen.mem_nhds ha] with b hb using hVmem b hb
    rw [hee.deriv_eq]; simp
  have hsing1 : ContinuousOn (fun r : ℝ => 1 / r) {(0 : ℝ)}ᶜ :=
    ContinuousOn.div continuousOn_const continuousOn_id (fun x hx => by simpa using hx)
  have hsing2 : ContinuousOn
      (fun r : ℝ => (ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) {(0 : ℝ)}ᶜ := by
    refine ContinuousOn.sub (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
      (ContinuousOn.div continuousOn_const continuousOn_id (fun x hx => by simpa using hx))
    intro x hx; simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx; positivity
  have hcontBR : Continuous (fun r : ℝ =>
      -(1 / 2) * deriv (deriv (fun a => χ a * a ^ ℓ)) r - (1 / r) * deriv (fun a => χ a * a ^ ℓ) r
        + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) * (χ r * r ^ ℓ) - E * (χ r * r ^ ℓ)) :=
    (((continuous_const.mul hD2cont).sub (cont_sing_mul hsing1 hD1cont hderiv0)).add
      (cont_sing_mul hsing2 hrealgcont hrealg0)).sub (continuous_const.mul hrealgcont)
  have hcsBR : HasCompactSupport (fun r : ℝ =>
      -(1 / 2) * deriv (deriv (fun a => χ a * a ^ ℓ)) r - (1 / r) * deriv (fun a => χ a * a ^ ℓ) r
        + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) * (χ r * r ^ ℓ) - E * (χ r * r ^ ℓ)) := by
    apply HasCompactSupport.intro hχcs
    intro r hr
    have hopen : (tsupport χ)ᶜ ∈ 𝓝 r := (isClosed_tsupport χ).isOpen_compl.mem_nhds hr
    have hgnb : (fun a => χ a * a ^ ℓ) =ᶠ[𝓝 r] (fun _ => 0) := by
      filter_upwards [hopen] with b hb; simp [image_eq_zero_of_notMem_tsupport hb]
    have hg0 : χ r * r ^ ℓ = 0 := hgnb.eq_of_nhds
    have hd1z : deriv (fun a => χ a * a ^ ℓ) r = 0 := by rw [hgnb.deriv_eq]; simp
    have hd2z : deriv (deriv (fun a => χ a * a ^ ℓ)) r = 0 := by
      have hdnb : deriv (fun a => χ a * a ^ ℓ) =ᶠ[𝓝 r] (fun _ => 0) := by
        filter_upwards [hopen] with b hb
        have : (fun a => χ a * a ^ ℓ) =ᶠ[𝓝 b] (fun _ => 0) := by
          filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hb] with d hd
          simp [image_eq_zero_of_notMem_tsupport hd]
        rw [this.deriv_eq]; simp
      rw [hdnb.deriv_eq]; simp
    simp [hg0, hd1z, hd2z]
  have hQeq : ∀ r, (-(1 / 2 : ℂ)) * deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r
        - (1 / (r : ℂ)) * deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
        + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (p.Z : ℂ) / (r : ℂ))
          * ((χ r : ℂ) * (r : ℂ) ^ ℓ) - (E : ℂ) * ((χ r : ℂ) * (r : ℂ) ^ ℓ)
      = (((-(1 / 2) * deriv (deriv (fun a => χ a * a ^ ℓ)) r
            - (1 / r) * deriv (fun a => χ a * a ^ ℓ) r
            + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) * (χ r * r ^ ℓ)
            - E * (χ r * r ^ ℓ)) : ℝ) : ℂ) := by
    intro r
    rw [hdc1 r, hdc2 r]
    push_cast
    ring
  have hmemBR : MemLp (fun r => (((-(1 / 2) * deriv (deriv (fun a => χ a * a ^ ℓ)) r
        - (1 / r) * deriv (fun a => χ a * a ^ ℓ) r
        + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) * (χ r * r ^ ℓ)
        - E * (χ r * r ^ ℓ)) : ℝ) : ℂ)) 2 radialMeasure :=
    (Complex.continuous_ofReal.comp hcontBR).memLp_of_hasCompactSupport
      (hcsBR.comp_left Complex.ofReal_zero)
  have hint : Integrable (fun r =>
      ((-(1 / 2 : ℂ)) * deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r
        - (1 / (r : ℂ)) * deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
        + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (p.Z : ℂ) / (r : ℂ))
          * ((χ r : ℂ) * (r : ℂ) ^ ℓ) - (E : ℂ) * ((χ r : ℂ) * (r : ℂ) ^ ℓ)) * c r)
      radialMeasure := by
    refine (memLp_one_iff_integrable.mp (MemLp.mul' (r := 1) hcML hmemBR)).congr ?_
    filter_upwards with r; rw [hQeq r]
  have hLmul : ∀ (x : ℝ) (z : ℂ), L ((x : ℂ) * z) = x * L z :=
    fun x z => by rw [← Complex.real_smul, L.map_smul, smul_eq_mul]
  have hconv : (∫ r, (-(1 / 2) * deriv (deriv (fun a => χ a * a ^ ℓ)) r
          - (1 / r) * deriv (fun a => χ a * a ^ ℓ) r
          + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) * (χ r * r ^ ℓ) - E * (χ r * r ^ ℓ))
          * L (c r) ∂radialMeasure)
      = ∫ r in Set.Ioi 0, (-(1 / 2) * deriv (deriv (fun a => χ a * a ^ ℓ)) r
          - (1 / r) * deriv (fun a => χ a * a ^ ℓ) r
          + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) * (χ r * r ^ ℓ) - E * (χ r * r ^ ℓ))
          * L (c r) * r ^ 2 := integral_radialMeasure_eq _
  rw [← hconv]
  rw [show (fun r => (-(1 / 2) * deriv (deriv (fun a => χ a * a ^ ℓ)) r
        - (1 / r) * deriv (fun a => χ a * a ^ ℓ) r
        + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - p.Z / r) * (χ r * r ^ ℓ) - E * (χ r * r ^ ℓ))
        * L (c r))
      = (fun r => L (((-(1 / 2 : ℂ)) * deriv (deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ)) r
        - (1 / (r : ℂ)) * deriv (fun a => (χ a : ℂ) * (a : ℂ) ^ ℓ) r
        + (((ℓ * (ℓ + 1) : ℝ) / (2 * (r : ℂ) ^ 2)) - (p.Z : ℂ) / (r : ℂ))
          * ((χ r : ℂ) * (r : ℂ) ^ ℓ) - (E : ℂ) * ((χ r : ℂ) * (r : ℂ) ^ ℓ)) * c r))
      from funext fun r => by rw [hQeq r, hLmul]]
  rw [ContinuousLinearMap.integral_comp_comm L hint, h0, L.map_zero]

/-- The **χ_cut bridge**: feed `sector_weak_part` for a general test `χ_fb` vanishing near `0`, by
writing `χ_fb = χ_cut · r^ℓ` with `χ_cut = χ_fb · (r^ℓ)⁻¹`.  Produces exactly the `hweak` hypothesis
of `forward_bridge` for the real coefficient `R = L ∘ coeffFun`. -/
lemma sector_hweak (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ) (L : ℂ →L[ℝ] ℝ)
    (χfb : ℝ → ℝ) (hχfb : ContDiff ℝ ∞ χfb) (hχfbcs : HasCompactSupport χfb)
    (hχfb0 : ∀ᶠ r in 𝓝 (0 : ℝ), χfb r = 0) :
    ∫ r in Set.Ioi 0,
      (-(1 / 2) * deriv^[2] χfb r - (1 / r) * deriv χfb r
        + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2) - p.Z / r) * χfb r - E * χfb r)
      * L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
          (chartRealization (ψ : Spectra.Sobolev.l2R3)) r) * r ^ 2 = 0 := by
  set χcut : ℝ → ℝ := fun r => χfb r * (r ^ ℓ)⁻¹ with hχcut
  have hcut_eq : (fun a => χcut a * a ^ ℓ) = χfb := by
    funext a
    by_cases ha : a = 0
    · subst ha
      simp only [hχcut]
      rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
      · subst hℓ; simp
      · rw [zero_pow hℓ.ne', mul_zero]; exact (hχfb0.self_of_nhds).symm
    · simp only [hχcut]
      field_simp
  have hcut0 : ∀ᶠ s in 𝓝 (0 : ℝ), χcut s = 0 := by
    filter_upwards [hχfb0] with s hs; simp [hχcut, hs]
  have hcut_smooth : ContDiff ℝ ∞ χcut := by
    rw [contDiff_iff_contDiffAt]; intro r
    by_cases hr : r = 0
    · subst hr
      exact contDiffAt_const.congr_of_eventuallyEq (by filter_upwards [hcut0] with s hs; rw [hs])
    · exact (hχfb.contDiffAt).mul (((contDiff_id.pow ℓ).contDiffAt).inv (pow_ne_zero ℓ hr))
  have hcut_cs : HasCompactSupport χcut := by
    apply HasCompactSupport.intro hχfbcs
    intro r hr
    simp [hχcut, image_eq_zero_of_notMem_tsupport hr]
  have hsw := sector_weak_part p E ψ heig ℓ m hm χcut hcut_smooth hcut0 hcut_cs L
  have hpt : ∀ r, χcut r * r ^ ℓ = χfb r := fun r => congrFun hcut_eq r
  simp only [hpt] at hsw
  rw [show deriv^[2] χfb = deriv (deriv χfb) from rfl]
  exact hsw

/-- The **s-weak form** for the real radial coefficient `R = L ∘ coeffFun`, obtained from
`sector_hweak` via `forward_bridge`: `∫ R(eˢ)·(η″ − η′ − b·η) ds = 0` with
`b(s) = ℓ(ℓ+1) − 2Z eˢ − 2E e^{2s}`.  This is exactly the weak hypothesis of
`Spectra.RadialRegularity.classical_of_weak_ode`. -/
lemma sector_sweak (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ) (L : ℂ →L[ℝ] ℝ) :
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ s, L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
            (chartRealization (ψ : Spectra.Sobolev.l2R3)) (Real.exp s))
        * (deriv (deriv η) s - deriv η s - ((ℓ : ℝ) * ((ℓ : ℝ) + 1)
        - 2 * p.Z * Real.exp s - 2 * E * Real.exp (2 * s)) * η s)
        = 0 :=
  forward_bridge ℓ p.Z E
    (fun r => L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ : Spectra.Sobolev.l2R3)) r))
    (fun χ h1 h2 h3 => sector_hweak p E ψ heig ℓ m hm L χ h1 h2 h3)

/-! ## Wiring the regularity pipeline

`sector_sweak` is the hypothesis of `Spectra.RadialRegularity.classical_of_weak_ode`; its remaining
side condition is the local integrability of `s ↦ L(coeffFun(eˢ))`, which follows from
`L²(r²dr)`.  Applying `classical_of_weak_ode` and then `radial_classical_of_logCoord` yields a
classical `C²` radial solution of the charge-`Z` reduced radial eigen-equation. -/

/-- `s ↦ L(g(eˢ))` is locally integrable on `ℝ` when `g ∈ L²(radialMeasure)` and `L` is a
continuous linear functional.  This is the `hRloc` side condition of `classical_of_weak_ode`. -/
lemma locallyIntegrable_comp_exp (g : ℝ → ℂ) (hg : MemLp g 2 radialMeasure) (L : ℂ →L[ℝ] ℝ) :
    LocallyIntegrable (fun s => L (g (Real.exp s))) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hexpK_cs : IsCompact (Real.exp '' K) := hK.image Real.continuous_exp
  have hexpK_sub : Real.exp '' K ⊆ Set.Ioi 0 := by rintro _ ⟨x, _, rfl⟩; exact Real.exp_pos x
  haveI : IsFiniteMeasure (volume.restrict (Real.exp '' K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hexpK_cs.measure_lt_top⟩
  have hrg : MemLp (fun (r : ℝ) => (r : ℂ) * g r) 2 (volume.restrict (Real.exp '' K)) := by
    have h := (memLp_radialReductionFun hg).restrict (Real.exp '' K)
    rwa [Measure.restrict_restrict_of_subset hexpK_sub] at h
  have hrg_int : IntegrableOn (fun (r : ℝ) => (r : ℂ) * g r) (Real.exp '' K) volume :=
    hrg.integrable one_le_two
  have hLrg_int : IntegrableOn (fun (r : ℝ) => L ((r : ℂ) * g r)) (Real.exp '' K) volume :=
    L.integrable_comp hrg_int
  have hcontInv : ContinuousOn (fun r : ℝ => r⁻¹) (Real.exp '' K) :=
    continuousOn_inv₀.mono (fun r hr => (hexpK_sub hr).ne')
  have hLg_int : IntegrableOn (fun r => L (g r)) (Real.exp '' K) volume := by
    refine (IntegrableOn.continuousOn_mul hcontInv hLrg_int hexpK_cs).congr_fun ?_
      hexpK_cs.measurableSet
    intro r hr
    have hr0 : r ≠ 0 := (hexpK_sub hr).ne'
    have hLrg : L ((r : ℂ) * g r) = r * L (g r) := by
      rw [show (r : ℂ) * g r = r • g r from Complex.real_smul.symm, L.map_smul, smul_eq_mul]
    dsimp only
    rw [hLrg, ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  have hcov := (integrableOn_image_iff_integrableOn_abs_deriv_smul hK.measurableSet
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun r => L (g r))).mp hLg_int
  have hcontExpNeg : ContinuousOn (fun x : ℝ => Real.exp (-x)) K :=
    (Real.continuous_exp.comp continuous_neg).continuousOn
  refine (IntegrableOn.continuousOn_mul hcontExpNeg hcov hK).congr_fun ?_ hK.measurableSet
  intro x _hx
  dsimp only
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul, ← mul_assoc, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_mul]

/-- Applying `classical_of_weak_ode` (with `hRloc = locallyIntegrable_comp_exp`) and then
`radial_classical_of_logCoord` produces a classical `C²` radial solution `ψ = c₀ ∘ log` of the
charge-`Z` reduced radial eigen-equation, a.e. equal (via `c₀ = R(eˢ)`) to the sector coefficient
pushed through the log substitution. -/
lemma sector_radial_solution (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (ℓ m : ℕ) (hm : m ≤ ℓ) (L : ℂ →L[ℝ] ℝ) :
    ∃ c₀ : ℝ → ℝ,
      (fun s => L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
          (chartRealization (ψ : Spectra.Sobolev.l2R3)) (Real.exp s))) =ᵐ[volume] c₀ ∧
      (∀ r, 0 < r → HasDerivAt (fun r => c₀ (Real.log r))
          (deriv (fun r => c₀ (Real.log r)) r) r) ∧
      (∀ r, 0 < r → HasDerivAt (deriv (fun r => c₀ (Real.log r)))
          (deriv^[2] (fun r => c₀ (Real.log r)) r) r) ∧
      (∀ r, 0 < r → -(1 / 2) * deriv^[2] (fun r => c₀ (Real.log r)) r
          - (1 / r) * deriv (fun r => c₀ (Real.log r)) r
          + ((ℓ : ℝ) * ((ℓ : ℝ) + 1) / (2 * r ^ 2) - p.Z / r) * (fun r => c₀ (Real.log r)) r
          = E * (fun r => c₀ (Real.log r)) r) := by
  obtain ⟨c₀, hae, hc1, hc2, hode⟩ :=
    Spectra.RadialRegularity.classical_of_weak_ode
      (locallyIntegrable_comp_exp (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ : Spectra.Sobolev.l2R3))) (memLp_coeffFun _ _) L)
      (b := fun s => (ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * p.Z * Real.exp s - 2 * E * Real.exp (2 * s))
      (by fun_prop)
      (sector_sweak p E ψ heig ℓ m hm L)
  obtain ⟨h1, h2, h3⟩ := radial_classical_of_logCoord ℓ p.Z E c₀ hc1 hc2 hode
  exact ⟨c₀, hae, h1, h2, h3⟩

end QuantumMechanics.Hydrogen.Spectrum

namespace Spectra.Sobolev
open MeasureTheory Complex

/-- Weak derivative commutes with complex conjugation. -/
lemma hasWeakDerivative_star (f : l2R3) (i : Fin 3) (g : l2R3)
    (h : HasWeakDerivative f i g) :
    HasWeakDerivative (star f) i (star g) := by
  intro φ hφ hsupp
  set ψ : R3 → ℂ := fun x => starRingEnd ℂ (φ x) with hψdef
  have hψsm := contDiff_starRingEnd_comp hφ
  have hψcs := hasCompactSupport_starRingEnd_comp hsupp
  have e := h ψ hψsm hψcs
  have hderiv : ∀ x, fderiv ℝ ψ x (EuclideanSpace.single i 1)
      = starRingEnd ℂ (fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    intro x
    have hdφ : HasFDerivAt φ (fderiv ℝ φ x) x :=
      (hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt ψ
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ φ x)) x :=
      (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp x hdφ
    rw [hcomp.fderiv]
    simp
  have key : (starRingEnd ℂ) (∫ x, f x * fderiv ℝ ψ x (EuclideanSpace.single i 1))
      = (starRingEnd ℂ) (- ∫ x, g x * ψ x) := congrArg _ e
  rw [map_neg, ← integral_conj, ← integral_conj] at key
  have hL : (fun x => (starRingEnd ℂ) (f x * fderiv ℝ ψ x (EuclideanSpace.single i 1)))
      = fun x => (starRingEnd ℂ) (f x) * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    funext x; rw [map_mul, hderiv x, Complex.conj_conj]
  have hR : (fun x => (starRingEnd ℂ) (g x * ψ x))
      = fun x => (starRingEnd ℂ) (g x) * φ x := by
    funext x; rw [map_mul, hψdef]; simp
  rw [hL, hR] at key
  have goalL : ∫ x, (star f : l2R3) x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (starRingEnd ℂ) (f x) * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_star f] with x hx
    rw [hx, Pi.star_apply, starRingEnd_apply]
  have goalR : ∫ x, (star g : l2R3) x * φ x = ∫ x, (starRingEnd ℂ) (g x) * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_star g] with x hx
    rw [hx, Pi.star_apply, starRingEnd_apply]
  rw [goalL, goalR]
  exact key

/-- Second weak derivative commutes with conjugation. -/
lemma hasWeakSecondDerivative_star (f : l2R3) (i j : Fin 3) (g : l2R3)
    (h : HasWeakSecondDerivative f i j g) :
    HasWeakSecondDerivative (star f) i j (star g) := by
  obtain ⟨mid, h1, h2⟩ := h
  exact ⟨star mid, hasWeakDerivative_star f i mid h1, hasWeakDerivative_star mid j g h2⟩

/-- `H¹` is closed under conjugation. -/
lemma memSobolevH1_star (f : l2R3) (hf : MemSobolevH1 f) : MemSobolevH1 (star f) := by
  intro i
  obtain ⟨g, hg⟩ := hf i
  exact ⟨star g, hasWeakDerivative_star f i g hg⟩

/-- `H²` is closed under conjugation. -/
lemma memSobolevH2_star (f : l2R3) (hf : MemSobolevH2 f) : MemSobolevH2 (star f) := by
  refine ⟨memSobolevH1_star f hf.1, fun i j => ?_⟩
  obtain ⟨g, hg⟩ := hf.2 i j
  exact ⟨star g, hasWeakSecondDerivative_star f i j g hg⟩

/-- The weak Laplacian commutes with conjugation, at the level of representatives. -/
lemma weakLaplacian_star_coeFn (f : l2R3) (hf : MemSobolevH2 f) :
    ⇑(weakLaplacian (star f) (memSobolevH2_star f hf)) =ᵐ[volume]
      fun a => starRingEnd ℂ (⇑(weakLaplacian f hf) a) := by
  have hcomp : ∀ i, ((memSobolevH2_star f hf).2 i i).choose = star ((hf.2 i i).choose) := by
    intro i
    obtain ⟨mid, hd1, hd2⟩ := (hf.2 i i).choose_spec
    exact hasWeakSecondDerivative_unique (star f) i i _ _
      ((memSobolevH2_star f hf).2 i i).choose_spec
      ⟨star mid, hasWeakDerivative_star f i mid hd1, hasWeakDerivative_star mid i _ hd2⟩
  have hWL : weakLaplacian (star f) (memSobolevH2_star f hf)
      = -(star ((hf.2 0 0).choose) + star ((hf.2 1 1).choose) + star ((hf.2 2 2).choose)) := by
    simp only [weakLaplacian, Fin.sum_univ_three]
    rw [hcomp 0, hcomp 1, hcomp 2]
  have hWf : weakLaplacian f hf
      = -((hf.2 0 0).choose + (hf.2 1 1).choose + (hf.2 2 2).choose) := by
    simp only [weakLaplacian, Fin.sum_univ_three]
  rw [hWL, hWf]
  set c0 := (hf.2 0 0).choose
  set c1 := (hf.2 1 1).choose
  set c2 := (hf.2 2 2).choose
  filter_upwards [Lp.coeFn_neg (star c0 + star c1 + star c2),
    Lp.coeFn_add (star c0 + star c1) (star c2), Lp.coeFn_add (star c0) (star c1),
    Lp.coeFn_star c0, Lp.coeFn_star c1, Lp.coeFn_star c2,
    Lp.coeFn_neg (c0 + c1 + c2), Lp.coeFn_add (c0 + c1) c2, Lp.coeFn_add c0 c1]
    with a hn hadd2 hadd1 hs0 hs1 hs2 hnf haddf2 haddf1
  simp only [hn, hadd2, hadd1, hs0, hs1, hs2, hnf, haddf2, haddf1,
    Pi.neg_apply, Pi.add_apply, Pi.star_apply, starRingEnd_apply, star_neg, star_add]

end Spectra.Sobolev

namespace QuantumMechanics.Hydrogen.Spectrum
open MeasureTheory Complex Filter
open Spectra.Sobolev
open Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics
open scoped Topology ENNReal

/-- **Deliverable A — `hL2`.** From `g ∈ L²(radialMeasure)`, a real-linear `L`, and the a.e. link
`L(g(eˢ)) =ᵐ c₀`, the radial profile `c₀ ∘ log` lies in `RadialEq.RadialL2`. -/
lemma sector_radialL2 (g : ℝ → ℂ) (hg : MemLp g 2 radialMeasure) (L : ℂ →L[ℝ] ℝ)
    (c₀ : ℝ → ℝ)
    (hae : (fun s => L (g (Real.exp s))) =ᵐ[volume] c₀) :
    RadialEq.RadialL2 (fun r => c₀ (Real.log r)) := by
  -- `L ∘ g ∈ L²(radialMeasure)`
  have hLg : MemLp (fun r => L (g r)) 2 radialMeasure := L.comp_memLp' hg
  -- translate to a weighted integrability statement on `(0,∞)`
  have hLg_int : IntegrableOn (fun r => (L (g r)) ^ 2 * r ^ 2) (Set.Ioi 0) volume := by
    have h1 := hLg
    rw [memLp_two_iff_integrable_sq hLg.aestronglyMeasurable,
      show radialMeasure = (volume.restrict (Set.Ioi 0)).withDensity
        (fun r => ENNReal.ofReal (r ^ 2)) from rfl,
      integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
        (.of_forall fun _ => ENNReal.ofReal_lt_top)] at h1
    refine h1.congr (Filter.Eventually.of_forall fun r => ?_)
    change (ENNReal.ofReal (r ^ 2)).toReal • L (g r) ^ 2 = L (g r) ^ 2 * r ^ 2
    rw [ENNReal.toReal_ofReal (sq_nonneg r), smul_eq_mul, mul_comm]
  -- change of variables `r = eˢ` to land an `s`-integral, where the a.e. link is clean
  have hs_int : Integrable
      (fun x => |Real.exp x| • ((L (g (Real.exp x))) ^ 2 * (Real.exp x) ^ 2)) volume := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
      (fun r => (L (g r)) ^ 2 * r ^ 2)).mp (by rw [Set.image_univ, Real.range_exp]; exact hLg_int)
    rwa [integrableOn_univ] at h
  -- rewrite the goal via the same change of variables
  change IntegrableOn (fun r => c₀ (Real.log r) ^ 2 * r ^ 2) (Set.Ioi 0) volume
  rw [show (Set.Ioi (0 : ℝ)) = Real.exp '' Set.univ by rw [Set.image_univ, Real.range_exp],
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    integrableOn_univ]
  -- match the two `s`-integrands via the a.e. link `c₀ = L(g(eˢ))`
  refine hs_int.congr ?_
  filter_upwards [hae] with x hx
  simp only [Real.log_exp, hx]

/-- **Deliverable B.** A function not a.e. zero is nonzero at some `log r₀`, `r₀>0` (every real is
`log (eˢ)`, so a.e.-zero of `c₀` is forced if it vanishes at all such points). -/
lemma sector_radial_pt_nonzero (c₀ : ℝ → ℝ)
    (hne : ¬ (c₀ =ᵐ[volume] 0)) : ∃ r₀, 0 < r₀ ∧ c₀ (Real.log r₀) ≠ 0 := by
  by_contra h
  refine hne ?_
  have hz : c₀ = 0 := by
    funext s
    by_contra hs
    exact h ⟨Real.exp s, Real.exp_pos s, by rwa [Real.log_exp]⟩
  simp [hz]

/-- **Deliverable D.** A `ℂ`-valued function that is not a.e. zero has a nonzero real or imaginary
part on a positive-measure set, i.e. `reCLM ∘ c` or `imCLM ∘ c` is not a.e. zero. -/
lemma exists_reIm_comp_ne_zero {μ : Measure ℝ} (c : ℝ → ℂ) (hc : ¬ (c =ᵐ[μ] 0)) :
    ∃ L : ℂ →L[ℝ] ℝ, (L = Complex.reCLM ∨ L = Complex.imCLM) ∧
      ¬ ((fun r => L (c r)) =ᵐ[μ] 0) := by
  by_contra h
  have hre : (fun r => (c r).re) =ᵐ[μ] 0 := by
    by_contra hh; exact h ⟨Complex.reCLM, Or.inl rfl, by simpa using hh⟩
  have him : (fun r => (c r).im) =ᵐ[μ] 0 := by
    by_contra hh; exact h ⟨Complex.imCLM, Or.inr rfl, by simpa using hh⟩
  refine hc ?_
  filter_upwards [hre, him] with r hr hi
  have hr' : (c r).re = 0 := by simpa using hr
  have hi' : (c r).im = 0 := by simpa using hi
  simp only [Pi.zero_apply]
  exact Complex.ext (by simpa using hr') (by simpa using hi')

/-- **Coefficients determine the function.** If every angular coefficient `coeffFun i F` vanishes
a.e., then `F = 0` (the completeness argument of `sectorEmbedding_dense`, factored out). -/
lemma eq_zero_of_coeffFun_ae_zero (F : Decomposition.l2R3)
    (hc0 : ∀ i : HarmonicIdx, coeffFun i F =ᵐ[radialMeasure] 0) : F = 0 := by
  -- a.e. slices of F lie in L²(S²).
  have hslice_mem : ∀ᵐ r ∂radialMeasure,
      MemLp (fun u => F (r, u)) 2 sphereMeasure := by
    have hF2 : MemLp (⇑F) 2 (radialMeasure.prod sphereMeasure) := Lp.memLp F
    have hsq := (memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).mp hF2
    filter_upwards [hsq.prod_right_ae] with r hr
    exact (memLp_two_iff_integrable_sq_norm
      (((Lp.stronglyMeasurable F).comp_measurable
        measurable_prodMk_left).aestronglyMeasurable)).mpr hr
  -- for a.e. r, the slice is orthogonal to every spherical harmonic, hence zero by completeness.
  have hslices : ∀ᵐ r ∂radialMeasure, ∀ᵐ u ∂sphereMeasure, F (r, u) = 0 := by
    have hall : ∀ᵐ r ∂radialMeasure, ∀ i : HarmonicIdx, coeffFun i F r = 0 :=
      ae_all_iff.mpr fun i => by
        filter_upwards [hc0 i] with r hr
        simpa using hr
    filter_upwards [hall, hslice_mem] with r hri hmem
    have hg : hmem.toLp (fun u => F (r, u)) ∈ (Submodule.span ℂ harmonicSet)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem v hv =>
          obtain ⟨ℓ, m, hm, rfl⟩ := hv
          have hval : inner ℂ
              ((memLp_sphericalHarmonic ℓ m hm).toLp (SphericalHarmonic ℓ m hm))
              (hmem.toLp fun u => F (r, u)) = coeffFun ⟨ℓ, ⟨m, hm⟩⟩ F r := by
            rw [L2.inner_def]
            simp only [coeffFun]
            refine integral_congr_ae ?_
            filter_upwards [(memLp_sphericalHarmonic ℓ m hm).coeFn_toLp,
              hmem.coeFn_toLp] with u h1 h2
            rw [h1, h2, RCLike.inner_apply']
            simp only [harmonic]
          rw [hval]
          exact hri ⟨ℓ, ⟨m, hm⟩⟩
      | zero => simp
      | add u v hu hv hu' hv' => rw [inner_add_left, hu', hv', add_zero]
      | smul c u hu hu' => rw [inner_smul_left, hu', mul_zero]
    have hbot : (Submodule.span ℂ harmonicSet)ᗮ = ⊥ := by
      have hcomp : (Submodule.span ℂ harmonicSet).topologicalClosure = ⊤ :=
        sphericalHarmonic_complete
      rwa [Submodule.topologicalClosure_eq_top_iff] at hcomp
    have hzero : hmem.toLp (fun u => F (r, u)) = 0 := by
      have hmem0 := hbot ▸ hg
      simpa using hmem0
    have hae : (fun u => F (r, u)) =ᵐ[sphereMeasure] 0 := by
      refine (hmem.coeFn_toLp).symm.trans ?_
      rw [hzero]
      exact Lp.coeFn_zero ℂ 2 sphereMeasure
    filter_upwards [hae] with u hu
    simpa using hu
  -- glue the slices.
  have hms : MeasurableSet {p : ℝ × (ℝ × ℝ) | F p ≠ 0} :=
    ((Lp.stronglyMeasurable F).measurable (measurableSet_singleton (0 : ℂ))).compl
  have hnull : (radialMeasure.prod sphereMeasure) {p : ℝ × (ℝ × ℝ) | F p ≠ 0} = 0 := by
    refine Measure.measure_prod_null_of_ae_null hms ?_
    filter_upwards [hslices] with r hr
    have hr0 := ae_iff.mp hr
    simpa using hr0
  have hae0 : ⇑F =ᵐ[radialMeasure.prod sphereMeasure] 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    simpa using hnull
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae0

/-- **Deliverable C corollary.** A nonzero `F` has some sector with `coeffFun` not a.e. zero. -/
lemma exists_coeffFun_ne_zero (F : Decomposition.l2R3) (hF : F ≠ 0) :
    ∃ i : HarmonicIdx, ¬ (coeffFun i F =ᵐ[radialMeasure] 0) := by
  by_contra h
  refine hF (eq_zero_of_coeffFun_ae_zero F ?_)
  intro i
  by_contra hi
  exact h ⟨i, hi⟩

/-- **Deliverable E — conj-eigenfunction.** If `ψ` is an eigenfunction `Hψ = Eψ` (E real), then so
is its complex conjugate `star ψ`.  (The hydrogen Hamiltonian has real coefficients.) -/
lemma hydrogenHamiltonian_star (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3)) :
    hydrogenHamiltonian p ⟨star (ψ : Spectra.Sobolev.l2R3), memSobolevH2_star _ ψ.2⟩
      = (E : ℂ) • (star (ψ : Spectra.Sobolev.l2R3)) := by
  obtain ⟨Ψ, hH2⟩ := ψ
  have hwe := weak_eigenequation_ae p E ⟨Ψ, hH2⟩ heig
  have ehalf : ⇑(halfLaplacianPMap ⟨star Ψ, memSobolevH2_star Ψ hH2⟩) =ᵐ[volume]
      ((1 / 2 : ℝ) : ℂ) • ⇑(weakLaplacian (star Ψ) (memSobolevH2_star Ψ hH2)) := by
    rw [show halfLaplacianPMap ⟨star Ψ, memSobolevH2_star Ψ hH2⟩
        = ((1 / 2 : ℝ) : ℂ) • weakLaplacian (star Ψ) (memSobolevH2_star Ψ hH2) from by
      rw [halfLaplacianPMap_apply]; rfl]
    exact Lp.coeFn_smul _ _
  have ecoul : ⇑(coulombPotential p ⟨star Ψ, memSobolevH2_star Ψ hH2⟩) =ᵐ[volume]
      fun x => (coulombMultiplier p x : ℂ) * (star Ψ) x :=
    (coulomb_mul_memLp_H2 p (star Ψ) (memSobolevH2_star Ψ hH2)).coeFn_toLp
  have eH : ⇑(hydrogenHamiltonian p ⟨star Ψ, memSobolevH2_star Ψ hH2⟩) =ᵐ[volume]
      fun x => ⇑(halfLaplacianPMap ⟨star Ψ, memSobolevH2_star Ψ hH2⟩) x
        + ⇑(coulombPotential p ⟨star Ψ, memSobolevH2_star Ψ hH2⟩) x := by
    rw [hydrogenHamiltonian_apply]; exact Lp.coeFn_add _ _
  have ewl := weakLaplacian_star_coeFn Ψ hH2
  have eRHS : ⇑((E : ℂ) • star Ψ) =ᵐ[volume] fun x => (E : ℂ) * (star Ψ) x := Lp.coeFn_smul _ _
  apply Lp.ext
  filter_upwards [eH, ehalf, ecoul, eRHS, ewl, hwe, Lp.coeFn_star Ψ]
    with x heHx hehalfx hecoulx heRHSx hewlx hwex hstarx
  rw [heHx, heRHSx, hehalfx, hecoulx, Pi.smul_apply, smul_eq_mul, hewlx, hwex]
  simp only [hstarx, Pi.star_apply, ← starRingEnd_apply, map_mul, map_sub,
    Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

/-- `chartRealization` commutes with conjugation, at the level of representatives. -/
lemma chartRealization_star (ψ : Spectra.Sobolev.l2R3) :
    ⇑(chartRealization (star ψ)) =ᵐ[radialMeasure.prod sphereMeasure]
      fun p => starRingEnd ℂ (⇑(chartRealization ψ) p) := by
  have h1 := chartRealization_coeFn (star ψ)
  have h2 := chartRealization_coeFn ψ
  have h3 := measurePreserving_sphereChart.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_star ψ)
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  rw [hp1, hp2]
  simp only [Function.comp_apply, Pi.star_apply, starRingEnd_apply] at hp3 ⊢
  exact hp3

/-- **conj relation for sector coefficients.**  The `(ℓ,-m)` coefficient of `star ψ` is a nonzero
real multiple of the conjugate of the `(ℓ,m)` coefficient of `ψ` (Condon–Shortley). -/
lemma coeffFun_star (ℓ m : ℕ) (hm : m ≤ ℓ) (ψ : Spectra.Sobolev.l2R3) :
    coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩ (chartRealization (star ψ))
      =ᵐ[radialMeasure] fun r =>
        ((sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))
            / (sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)) : ℝ) : ℂ)
          * starRingEnd ℂ (coeffFun ⟨ℓ, (m : ℤ), by simpa using hm⟩ (chartRealization ψ) r) := by
  have hmI : |(m : ℤ)| ≤ (ℓ : ℤ) := by simpa using hm
  have hm' : |(-(m : ℤ))| ≤ (ℓ : ℤ) := by rw [abs_neg]; simpa using hm
  have hYconj : ∀ u, (starRingEnd ℂ) (harmonic ⟨ℓ, -(m : ℤ), hm'⟩ u)
      = ((sphericalNorm ℓ (-(m : ℤ)) * reflectionFactor ℓ (-(m : ℤ))
          / (sphericalNorm ℓ (m : ℤ) * reflectionFactor ℓ (m : ℤ)) : ℝ) : ℂ)
        * harmonic ⟨ℓ, (m : ℤ), hmI⟩ u := by
    intro u
    have hsc := sphericalHarmonic_conj ℓ (-(m : ℤ)) hm' (by rw [neg_neg]; exact hmI) u
    simp only [neg_neg] at hsc
    simp only [harmonic]
    rw [hsc]
  have hslice := Measure.ae_ae_of_ae_prod (chartRealization_star ψ)
  filter_upwards [hslice] with r hr
  simp only [coeffFun]
  rw [integral_congr_ae (hr.mono fun u hu => by rw [hu])]
  simp only [hYconj, mul_assoc]
  rw [integral_const_mul]
  congr 1
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, Complex.conj_conj]

/-- **Measure transport.** If a real radial profile is not a.e. zero w.r.t. `radialMeasure`, then
its log-coordinate pullback `s ↦ g(eˢ)` is not a.e. zero w.r.t. Lebesgue measure. -/
lemma exp_ae_ne_of_radial_ae_ne (g : ℝ → ℝ) (hg : ¬ (g =ᵐ[radialMeasure] 0)) :
    ¬ ((fun s => g (Real.exp s)) =ᵐ[volume] 0) := by
  intro H
  refine hg ?_
  have hN : volume {s | ¬ g (Real.exp s) = 0} = 0 := by
    have h := H; rw [Filter.EventuallyEq, ae_iff] at h; simpa using h
  have himg : volume (Real.exp '' {s | ¬ g (Real.exp s) = 0}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      volume Real.differentiable_exp.differentiableOn hN
  have hac : radialMeasure ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.restrict_le_self).absolutelyContinuous
  have hIoic : radialMeasure (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    have h := ae_radial_mem_Ioi
    rwa [ae_iff] at h
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null
    (show {r | ¬ g r = 0} ⊆ Real.exp '' {s | ¬ g (Real.exp s) = 0} ∪ (Set.Ioi 0)ᶜ from ?_) ?_
  · intro r hr
    by_cases hr0 : 0 < r
    · exact Or.inl ⟨Real.log r, by simpa [Real.exp_log hr0] using hr, Real.exp_log hr0⟩
    · exact Or.inr (by simpa using hr0)
  · exact measure_union_null (hac himg) hIoic

/-- **Deliverable F — `hnz` existence.** A nonzero eigenpair has a nonzero non-positive-`m` sector
coefficient (using `star ψ` for positive `m`), in the log-coordinate form feeding `B`. -/
lemma exists_nonzero_sector (p : CoulombParams) (E : ℝ)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3))
    (hψ0 : (ψ : Spectra.Sobolev.l2R3) ≠ 0) :
    ∃ (ℓ m : ℕ) (hm : m ≤ ℓ) (L : ℂ →L[ℝ] ℝ) (ψ' : (hydrogenHamiltonian p).domain),
      hydrogenHamiltonian p ψ' = (E : ℂ) • (ψ' : Spectra.Sobolev.l2R3) ∧
      ¬ ((fun s => L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
            (chartRealization (ψ' : Spectra.Sobolev.l2R3)) (Real.exp s))) =ᵐ[volume] 0) := by
  have hΦ : chartRealization (ψ : Spectra.Sobolev.l2R3) ≠ 0 := fun h =>
    hψ0 (chartRealization.injective (h.trans (map_zero chartRealization).symm))
  obtain ⟨i, hi⟩ := exists_coeffFun_ne_zero _ hΦ
  obtain ⟨ℓ, m₀, hm₀⟩ := i
  by_cases hsign : m₀ ≤ 0
  · -- `m₀ ≤ 0`: use `ψ` itself, `m = (-m₀).toNat`
    have hval : -(((-m₀).toNat : ℤ)) = m₀ := by
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -m₀)]; ring
    have hm : (-m₀).toNat ≤ ℓ := by
      have h := hm₀; rw [abs_le] at h; omega
    obtain ⟨L, _, hL⟩ := exists_reIm_comp_ne_zero
      (coeffFun ⟨ℓ, m₀, hm₀⟩ (chartRealization (ψ : Spectra.Sobolev.l2R3))) hi
    refine ⟨ℓ, (-m₀).toNat, hm, L, ψ, heig, ?_⟩
    simp only [hval]
    exact exp_ae_ne_of_radial_ae_ne _ hL
  · -- `m₀ > 0`: use `star ψ`, `m = m₀.toNat`
    have hval : ((m₀.toNat : ℤ)) = m₀ := Int.toNat_of_nonneg (by omega)
    have hm : m₀.toNat ≤ ℓ := by
      have h := hm₀; rw [abs_le] at h; omega
    have hκ : (sphericalNorm ℓ (-(m₀.toNat : ℤ)) * reflectionFactor ℓ (-(m₀.toNat : ℤ))
        / (sphericalNorm ℓ (m₀.toNat : ℤ) * reflectionFactor ℓ (m₀.toNat : ℤ)) : ℝ) ≠ 0 :=
      div_ne_zero (mul_ne_zero (sphericalNorm_pos _ _).ne' (reflectionFactor_ne_zero _ _))
        (mul_ne_zero (sphericalNorm_pos _ _).ne' (reflectionFactor_ne_zero _ _))
    have hcs := coeffFun_star ℓ m₀.toNat hm (ψ : Spectra.Sobolev.l2R3)
    have hne : ¬ (coeffFun ⟨ℓ, -(m₀.toNat : ℤ), by rw [abs_neg, hval]; exact hm₀⟩
        (chartRealization (star (ψ : Spectra.Sobolev.l2R3))) =ᵐ[radialMeasure] 0) := by
      intro hz
      apply hi
      filter_upwards [hcs.symm.trans hz] with r hr
      simp only [Pi.zero_apply] at hr ⊢
      rcases mul_eq_zero.mp hr with h | h
      · exact absurd (Complex.ofReal_eq_zero.mp h) hκ
      · rw [starRingEnd_apply, star_eq_zero] at h
        simpa only [hval] using h
    obtain ⟨L, _, hL⟩ := exists_reIm_comp_ne_zero _ hne
    refine ⟨ℓ, m₀.toNat, hm, L, ⟨star (ψ : Spectra.Sobolev.l2R3), memSobolevH2_star _ ψ.2⟩,
      hydrogenHamiltonian_star p E ψ heig, ?_⟩
    exact exp_ae_ne_of_radial_ae_ne _ hL
end QuantumMechanics.Hydrogen.Spectrum


namespace QuantumMechanics.Hydrogen.Spectrum
open MeasureTheory Filter Complex
open Spectra.Sobolev
open Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics
open scoped Topology ENNReal

/-- A function `≥ c > 0` on `Iic b` (infinite measure) is not integrable there. -/
lemma not_integrableOn_Iic_of_ge {p : ℝ → ℝ} {b c : ℝ} (hc : 0 < c)
    (hge : ∀ s ∈ Set.Iic b, c ≤ p s) : ¬ IntegrableOn p (Set.Iic b) := by
  intro hint
  have hconst : IntegrableOn (fun _ : ℝ => c) (Set.Iic b) :=
    hint.mono' aestronglyMeasurable_const
      (ae_restrict_of_forall_mem measurableSet_Iic (fun s hs => by
        rw [Real.norm_eq_abs, abs_of_nonneg hc.le]; exact hge s hs))
  rw [integrableOn_const_iff] at hconst
  rcases hconst with h | h
  · rw [enorm_eq_zero] at h; exact absurd h hc.ne'
  · rw [Real.volume_Iic] at h; exact absurd h (lt_irrefl _)

/-- **Stage 1.** A nonnegative function that is convex (`p'' ≥ 0`) and integrable on `Iic a` is
bounded above by `p a` there. -/
lemma le_endpoint_of_convex_integrable {p p' p'' : ℝ → ℝ} {a : ℝ}
    (hp1 : ∀ s, HasDerivAt p (p' s) s)
    (hp2 : ∀ s, HasDerivAt p' (p'' s) s)
    (hconv : ∀ s ≤ a, 0 ≤ p'' s)
    (hpnn : ∀ s, 0 ≤ p s)
    (hint : IntegrableOn p (Set.Iic a)) :
    ∀ s ≤ a, p s ≤ p a := by
  have hp'diff : Differentiable ℝ p' := fun s => (hp2 s).differentiableAt
  have hdcont : Continuous p' := hp'diff.continuous
  -- convexity: `p'` is monotone on `Iic a`
  have hmono : MonotoneOn p' (Set.Iic a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic a) hdcont.continuousOn
      (fun s _ => (hp'diff s).differentiableWithinAt) ?_
    intro s hs
    rw [interior_Iic] at hs
    rw [(hp2 s).deriv]
    exact hconv s (le_of_lt hs)
  -- `p' ≥ 0` on `Iic a`
  have hderiv_nonneg : ∀ t ≤ a, 0 ≤ p' t := by
    intro t ht
    by_contra hneg
    rw [not_le] at hneg
    have hcpos : 0 < -p' t := by linarith
    have hge : ∀ u ∈ Set.Iic (t - 1), -p' t ≤ p u := by
      intro u hu
      simp only [Set.mem_Iic] at hu
      have huv : u ≤ t := by linarith
      have hII : IntervalIntegrable p' volume u t := hdcont.intervalIntegrable u t
      have hftc : ∫ x in u..t, p' x = p t - p u :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hp1 x) hII
      have hbd : ∫ x in u..t, p' x ≤ ∫ _ in u..t, p' t :=
        intervalIntegral.integral_mono_on huv hII intervalIntegrable_const
          (fun x hx => hmono (Set.mem_Iic.mpr (hx.2.trans ht)) (Set.mem_Iic.mpr ht) hx.2)
      rw [hftc, intervalIntegral.integral_const, smul_eq_mul] at hbd
      nlinarith [hbd, hpnn t,
        mul_nonneg (by linarith : (0:ℝ) ≤ -p' t) (by linarith : (0:ℝ) ≤ t - u - 1)]
    have hint' : IntegrableOn p (Set.Iic (t - 1)) :=
      hint.mono_set (Set.Iic_subset_Iic.mpr (by linarith))
    exact not_integrableOn_Iic_of_ge hcpos hge hint'
  -- `p` is monotone on `Iic a`
  have hpdiff0 : Differentiable ℝ p := fun s => (hp1 s).differentiableAt
  have hpmono : MonotoneOn p (Set.Iic a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic a) hpdiff0.continuous.continuousOn
      (fun s _ => (hp1 s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [interior_Iic] at hs
    rw [(hp1 s).deriv]
    exact hderiv_nonneg s (le_of_lt hs)
  exact fun s hs => hpmono hs Set.self_mem_Iic hs

/-- **Stage 2 — the boundary condition (log-coordinate dichotomy).** A classical `C²` solution `c₀`
of the log-coordinate radial ODE `c₀'' + c₀' − b·c₀ = 0` (`b(s) = ℓ(ℓ+1) − 2Z eˢ − 2E e^{2s}`,
`Z>0`, `E<0`) whose unweighted square `eˢ·c₀²` is integrable forces the Dirichlet boundary behaviour
`r·c₀(log r) → 0` as `r → 0⁺`.  The singular `r^{−ℓ}`/`r^{−(ℓ+1)}` branch is killed by integrability
via convexity of `p = eˢc₀²` near `−∞`. -/
lemma radial_bc_of_logCoord (ℓ : ℕ) (Z E : ℝ) (hZ : 0 < Z) (hE : E < 0) (c₀ : ℝ → ℝ)
    (hc1 : ∀ s, HasDerivAt c₀ (deriv c₀ s) s)
    (hc2 : ∀ s, HasDerivAt (deriv c₀) (deriv^[2] c₀ s) s)
    (hode : ∀ s, deriv^[2] c₀ s + deriv c₀ s
      - ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * Real.exp s - 2 * E * Real.exp (2 * s)) * c₀ s = 0)
    (hint : Integrable (fun s => Real.exp s * c₀ s ^ 2) volume) :
    Tendsto (fun r => r * c₀ (Real.log r)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  set p : ℝ → ℝ := fun s => Real.exp s * c₀ s ^ 2 with hp
  set p' : ℝ → ℝ := fun s => Real.exp s * (c₀ s ^ 2 + 2 * c₀ s * deriv c₀ s) with hp'
  set p'' : ℝ → ℝ := fun s => Real.exp s *
      (c₀ s ^ 2 + 4 * c₀ s * deriv c₀ s + 2 * deriv c₀ s ^ 2 + 2 * c₀ s * deriv^[2] c₀ s) with hp''
  -- derivatives of `p`, `p'`
  have hpd1 : ∀ s, HasDerivAt p (p' s) s := by
    intro s
    have h := (Real.hasDerivAt_exp s).mul ((hc1 s).pow 2)
    simp only [hp, hp']
    convert h using 1
    simp only [Pi.pow_apply]
    ring
  have hpd2 : ∀ s, HasDerivAt p' (p'' s) s := by
    intro s
    have hexp := Real.hasDerivAt_exp s
    have hg : HasDerivAt (fun s => c₀ s ^ 2 + 2 * c₀ s * deriv c₀ s)
        (2 * c₀ s * deriv c₀ s + 2 * (deriv c₀ s * deriv c₀ s + c₀ s * deriv^[2] c₀ s)) s := by
      have h1 := (hc1 s).pow 2
      have h2 := ((hc1 s).const_mul (2 : ℝ)).mul (hc2 s)
      convert h1.add h2 using 1
      ring
    have h := hexp.mul hg
    simp only [hp', hp'']
    convert h using 1
    ring
  -- convexity threshold `a`
  set a : ℝ := Real.log (((ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 / 4) / (2 * Z)) with _ha
  have hxpos : (0 : ℝ) < ((ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 / 4) / (2 * Z) := by positivity
  have hconv : ∀ s ≤ a, 0 ≤ p'' s := by
    intro s hs
    have hexp_a : Real.exp a = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 / 4) / (2 * Z) :=
      Real.exp_log hxpos
    have hes : Real.exp s ≤ ((ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 / 4) / (2 * Z) := by
      rw [← hexp_a]; exact Real.exp_le_exp.mpr hs
    have h2Z : 2 * Z * Real.exp s ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) + 1 / 4 := by
      rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp hes
    have hE2 : 0 ≤ -2 * E * Real.exp (2 * s) := by
      have : (0 : ℝ) < -2 * E := by linarith
      positivity
    have hb : -1/4 ≤ (ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * Real.exp s - 2 * E * Real.exp (2 * s) := by
      nlinarith [h2Z, hE2]
    have hode_s := hode s
    have hsub : deriv^[2] c₀ s = ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * Real.exp s
        - 2 * E * Real.exp (2 * s)) * c₀ s - deriv c₀ s := by linarith [hode_s]
    have hbracket : 0 ≤ c₀ s ^ 2 + 4 * c₀ s * deriv c₀ s + 2 * deriv c₀ s ^ 2
        + 2 * c₀ s * deriv^[2] c₀ s := by
      rw [hsub]
      nlinarith [sq_nonneg (2 * deriv c₀ s + c₀ s), sq_nonneg (c₀ s),
        mul_nonneg (by linarith [hb] : (0:ℝ) ≤ ((ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * Z * Real.exp s
          - 2 * E * Real.exp (2 * s)) + 1/4) (sq_nonneg (c₀ s))]
    simp only [hp'']
    exact mul_nonneg (Real.exp_pos s).le hbracket
  have hpnn : ∀ s, 0 ≤ p s := fun s => by simp only [hp]; positivity
  -- bounded near `-∞`
  have hbound := le_endpoint_of_convex_integrable hpd1 hpd2 hconv hpnn hint.integrableOn
  -- squeeze `|r·c₀(log r)| ≤ √(p a)·√r`
  have htend : Tendsto (fun r : ℝ => Real.sqrt (p a) * Real.sqrt r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Tendsto (fun r : ℝ => Real.sqrt r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    simpa using h1.const_mul (Real.sqrt (p a))
  refine squeeze_zero_norm' ?_ htend
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (Real.exp_pos a))] with r hr0i hrai
  have hr0 : (0 : ℝ) < r := hr0i
  have hra : r < Real.exp a := hrai
  have hlog : Real.log r ≤ a := by
    rw [← Real.log_exp a]; exact Real.log_le_log hr0 hra.le
  have hple : p (Real.log r) ≤ p a := hbound _ hlog
  have hpr : (r * c₀ (Real.log r)) ^ 2 = r * p (Real.log r) := by
    simp only [hp]; rw [Real.exp_log hr0]; ring
  have hsqle : (r * c₀ (Real.log r)) ^ 2 ≤ r * p a := by
    rw [hpr]; exact mul_le_mul_of_nonneg_left hple hr0.le
  rw [Real.norm_eq_abs]
  calc |r * c₀ (Real.log r)| ≤ Real.sqrt (r * p a) := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsqle
    _ = Real.sqrt (p a) * Real.sqrt r := by rw [Real.sqrt_mul hr0.le, mul_comm]

/-- **Stage 3a.** The sector coefficient of `(coulomb·ψ)` is `(−Z/r)` times that of `ψ`
(the Coulomb factor is radial). -/
lemma coeffFun_coulomb (p : CoulombParams) (ℓ m : ℕ) (hm : m ≤ ℓ)
    (ψ : Spectra.Sobolev.l2R3) (hψ : MemSobolevH2 ψ) :
    coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization ((coulomb_mul_memLp_H2 p ψ hψ).toLp
          (fun x => (coulombMultiplier p x : ℂ) * ψ x)))
      =ᵐ[radialMeasure] fun r => ((-p.Z / r : ℝ) : ℂ)
        * coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩ (chartRealization ψ) r := by
  set G := (coulomb_mul_memLp_H2 p ψ hψ).toLp (fun x => (coulombMultiplier p x : ℂ) * ψ x) with _hG
  -- a.e. on the product box, `chartReal G = coulomb(sphereChart)·chartReal ψ`
  have hcombined : ⇑(chartRealization G) =ᵐ[radialMeasure.prod sphereMeasure]
      fun q => (coulombMultiplier p (sphereChart q.1 q.2.1 q.2.2) : ℂ) * ⇑(chartRealization ψ) q
      := by
    have h1 := chartRealization_coeFn G
    have h2 := measurePreserving_sphereChart.quasiMeasurePreserving.ae_eq_comp
      ((coulomb_mul_memLp_H2 p ψ hψ).coeFn_toLp)
    have h3 := chartRealization_coeFn ψ
    filter_upwards [h1, h2, h3] with q hq1 hq2 hq3
    rw [hq1]
    simp only [Function.comp_apply] at hq2
    rw [hq2, hq3]
  have hslice := Measure.ae_ae_of_ae_prod hcombined
  filter_upwards [hslice, ae_radial_mem_Ioi] with r hr hr0
  have hrpos : (0 : ℝ) < r := hr0
  have hcoul : ∀ u : ℝ × ℝ, coulombMultiplier p (sphereChart r u.1 u.2) = -p.Z / r := by
    intro u
    rw [coulombMultiplier, norm_sphereChart, abs_of_pos hrpos, if_neg hrpos.ne']
  simp only [coeffFun]
  rw [integral_congr_ae (hr.mono fun u hu => by rw [hu, hcoul u])]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  ring

/-- **Stage 3.** The radial profile `L ∘ coeffFun` is unweighted-`L²` near the origin (in log
coordinates `∫ eˢ·(L coeffFun(eˢ))² < ∞`), from `(Z/r)·ψ ∈ L²`. This feeds the dichotomy. -/
lemma sector_coulomb_L2 (p : CoulombParams) (ψ' : (hydrogenHamiltonian p).domain)
    (ℓ m : ℕ) (hm : m ≤ ℓ) (L : ℂ →L[ℝ] ℝ) :
    Integrable (fun s => Real.exp s *
      (L (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ' : Spectra.Sobolev.l2R3)) (Real.exp s))) ^ 2) volume := by
  set c : ℝ → ℂ := coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
    (chartRealization (ψ' : Spectra.Sobolev.l2R3)) with _hc
  set cG : ℝ → ℂ := coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
    (chartRealization ((coulomb_mul_memLp_H2 p (ψ' : Spectra.Sobolev.l2R3) ψ'.2).toLp
      (fun x => (coulombMultiplier p x : ℂ) * (ψ' : Spectra.Sobolev.l2R3) x))) with _hcG
  have hrel : cG =ᵐ[radialMeasure] fun r => ((-p.Z / r : ℝ) : ℂ) * c r :=
    coeffFun_coulomb p ℓ m hm _ ψ'.2
  have hcGmem : MemLp cG 2 radialMeasure := memLp_coeffFun _ _
  -- `L (cG)` is in `L²(radialMeasure)`; and `L(cG r) =ᵐ (-Z/r)·L(c r)`
  have hLcG : MemLp (fun r => L (cG r)) 2 radialMeasure := L.comp_memLp' hcGmem
  have hLrel : (fun r => L (cG r)) =ᵐ[radialMeasure] fun r => (-p.Z / r) * L (c r) := by
    filter_upwards [hrel] with r hr
    rw [hr, ← Complex.real_smul, L.map_smul, smul_eq_mul]
  -- `∫₀ (L c r)² dr < ∞`  (the `r²` and `1/r²` cancel)
  have hint_dr : IntegrableOn (fun r => (L (c r)) ^ 2) (Set.Ioi 0) volume := by
    have hsq : Integrable (fun r => (L (cG r)) ^ 2) radialMeasure := by
      have := (memLp_two_iff_integrable_sq (hLcG.aestronglyMeasurable)).mp hLcG
      exact this
    have hsq' : Integrable (fun r => ((-p.Z / r) * L (c r)) ^ 2) radialMeasure :=
      hsq.congr (by filter_upwards [hLrel] with r hr; rw [hr])
    rw [show radialMeasure = (volume.restrict (Set.Ioi 0)).withDensity
      (fun r => ENNReal.ofReal (r ^ 2)) from rfl,
      integrable_withDensity_iff_integrable_smul₀' (by fun_prop)
        (.of_forall fun _ => ENNReal.ofReal_lt_top)] at hsq'
    -- on `Ioi 0`: `r²·((-Z/r)·Lc)² = Z²·(Lc)²`
    have hZ0 : p.Z ≠ 0 := p.hZ.ne'
    refine (hsq'.const_mul (p.Z ^ 2)⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrne : r ≠ 0 := (Set.mem_Ioi.mp hr).ne'
    rw [ENNReal.toReal_ofReal (sq_nonneg r), smul_eq_mul]
    field_simp
  -- change of variables `r = eˢ`
  have hCoV := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun r => (L (c r)) ^ 2)).mp (by rw [Set.image_univ, Real.range_exp]; exact hint_dr)
  rw [integrableOn_univ] at hCoV
  refine hCoV.congr ?_
  filter_upwards with x
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul]

/-- **Forward direction (assembly).** A nonzero `H²` eigenpair `Hψ = Eψ` with `E < 0` forces
`E = eigenvalue p n hn` for some `n ≥ 1`. -/
theorem forward_eigenvalue (p : CoulombParams) (E : ℝ) (hE : E < 0)
    (ψ : (hydrogenHamiltonian p).domain)
    (hψ0 : (ψ : Spectra.Sobolev.l2R3) ≠ 0)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3)) :
    ∃ (n : ℕ) (hn : 1 ≤ n), E = eigenvalue p n hn := by
  obtain ⟨ℓ, m, hm, L, ψ', heig', hne⟩ := exists_nonzero_sector p E ψ heig hψ0
  obtain ⟨c₀, hae, hc1, hc2, hode⟩ :=
    Spectra.RadialRegularity.classical_of_weak_ode
      (locallyIntegrable_comp_exp (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ' : Spectra.Sobolev.l2R3))) (memLp_coeffFun _ _) L)
      (b := fun s => (ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * p.Z * Real.exp s - 2 * E * Real.exp (2 * s))
      (by fun_prop)
      (sector_sweak p E ψ' heig' ℓ m hm L)
  obtain ⟨h1, h2, h3⟩ := radial_classical_of_logCoord ℓ p.Z E c₀ hc1 hc2 hode
  refine radial_quantization_Z p ℓ E hE (fun r => c₀ (Real.log r)) ?_ ?_ h1 h2 h3 ?_
  · exact sector_radial_pt_nonzero c₀ (fun hz => hne (hae.trans hz))
  · exact sector_radialL2 _ (memLp_coeffFun _ _) L c₀ hae
  · exact radial_bc_of_logCoord ℓ p.Z E p.hZ hE c₀ hc1 hc2 hode
      ((sector_coulomb_L2 p ψ' ℓ m hm L).congr (by filter_upwards [hae] with s hs; rw [hs]))

/-- **No eigenfunctions at energy `E ≥ 0`** — the analytic core of Kato's theorem for
hydrogen.  A nonzero `L²` eigenfunction of the Cartesian hydrogen Hamiltonian `H = −½Δ − Z/r`
at energy `E ≥ 0` would project to a nonzero angular sector whose radial profile is a classical
`L²` solution of the charge-`Z` radial equation; `radial_continuum_Z` forces such a solution to
vanish identically on `(0,∞)`, contradicting the nonzero radial point.

This mirrors `forward_eigenvalue` exactly, sharing every sector-projection and
elliptic-regularity step (`exists_nonzero_sector`, `classical_of_weak_ode`,
`radial_classical_of_logCoord`), but with two simplifications afforded by `E ≥ 0`: the
terminal `radial_quantization_Z` is replaced by `radial_continuum_Z`, and the at-origin
boundary condition `radial_bc_of_logCoord` (the only other place `E < 0` was used) is dropped
entirely. -/
theorem no_positive_eigenvalue (p : CoulombParams) (E : ℝ) (hE : 0 ≤ E)
    (ψ : (hydrogenHamiltonian p).domain)
    (heig : hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3)) :
    (ψ : Spectra.Sobolev.l2R3) = 0 := by
  by_contra hψ0
  obtain ⟨ℓ, m, hm, L, ψ', heig', hne⟩ := exists_nonzero_sector p E ψ heig hψ0
  obtain ⟨c₀, hae, hc1, hc2, hode⟩ :=
    Spectra.RadialRegularity.classical_of_weak_ode
      (locallyIntegrable_comp_exp (coeffFun ⟨ℓ, -(m : ℤ), by rw [abs_neg]; simpa using hm⟩
        (chartRealization (ψ' : Spectra.Sobolev.l2R3))) (memLp_coeffFun _ _) L)
      (b := fun s => (ℓ : ℝ) * ((ℓ : ℝ) + 1) - 2 * p.Z * Real.exp s - 2 * E * Real.exp (2 * s))
      (by fun_prop)
      (sector_sweak p E ψ' heig' ℓ m hm L)
  obtain ⟨h1, h2, h3⟩ := radial_classical_of_logCoord ℓ p.Z E c₀ hc1 hc2 hode
  obtain ⟨r₀, hr₀, hr₀ne⟩ := sector_radial_pt_nonzero c₀ (fun hz => hne (hae.trans hz))
  exact hr₀ne (radial_continuum_Z p ℓ E hE (fun r => c₀ (Real.log r))
    (sector_radialL2 _ (memLp_coeffFun _ _) L c₀ hae) h1 h2 h3 r₀ hr₀)

end QuantumMechanics.Hydrogen.Spectrum

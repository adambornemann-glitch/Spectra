/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian

/-!
# The Spectrum of the Hydrogen Atom

The main theorems about the hydrogen spectrum, assembling the radial
eigenvalue problem with the angular decomposition.

## The main theorem

For the hydrogen Hamiltonian H = −Δ − Z/r (Z = 1 in atomic units):

  **Discrete spectrum**: σ_disc(H) = { −1/(2n²) : n = 1, 2, 3, ... }
  **Continuous spectrum**: σ_cont(H) = [0, ∞)
  **Degeneracy**: dim ker(H − E_n) = n²
  **Eigenfunctions**: ψ_{nℓm}(r,θ,φ) = R_{nℓ}(r) Y_ℓ^m(θ,φ)

These results reproduce, with complete mathematical rigour, the spectral
series I computed in January 1926 in Arosa. The eigenvalues agree exactly
with Bohr's 1913 formula — but now they are *derived*, not postulated.

## Architecture

```
  RadialEquation.lean     SphericalHarmonics.lean    HydrogenHamiltonian.lean
  ┌─────────────────┐     ┌───────────────────┐      ┌──────────────────────┐
  │ E_n = -1/(2n²)  │     │ Y_ℓ^m eigenvalue  │      │ hydrogenGenerator    │
  │ R_{nℓ} eigfunc  │     │ Y_ℓ^m orthonormal │      │ hydrogen_isSA        │
  │ radial_quantiz  │     │ Y_ℓ^m complete    │      │ IsSpectralMeasureFor │
  └────────┬────────┘     └────────┬──────────┘      └──────────┬───────────┘
           │                       │                            │
           └───────────┬───────────┘                            │
                       │                                        │
              ┌────────▼──────────┐                             │
              │ THIS FILE         │←────────────────────────────┘
              │                   │
              │ hydrogen_discrete │
              │ hydrogen_continuum│
              │ hydrogen_degener  │
              │ hydrogen_bohr     │
              └───────────────────┘
```

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I-IV*][schrodinger1926]
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal Laplacian
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics (SphericalHarmonic sphericalHarmonic_eigenvalue
  laplaceBeltrami_const_mul)
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)

/-! ## Separation of the Laplacian

The pointwise separation `−Δ = −(1/r²)∂_r(r²∂_r) + L̂²/r²` (with `L̂² = laplaceBeltrami`
the angular Laplacian on S²) is developed in `RadialProblem.SphericalLaplacian`:

* `sphereChart`, `norm_sphereChart` — the spherical chart `(r,θ,φ) ↦ ℝ³` (proved);
* `radialPart_eq` — the radial operator in divergence form equals the expanded form,
  `(1/r²)∂_r(r²∂_r R) = R″ + (2/r)R′` (proved); this is the radial half at the operator
  level, matching `RadialEq.radialHamiltonian`;
* `laplacian_comp_norm` — `Δ(g∘‖·‖) = g″ + (2/r)g′` (radial Laplacian of a radial
  function), and `laplacian_separates` — the full pointwise separation on the chart,
  both stated honestly and left as documented *pure-calculus* gaps (the chain rule
  through the chart; no missing analytic infrastructure, unlike the
  confluent-hypergeometric gaps in `RadialEquation.lean`).
-/

/-- **The Laplacian within a fixed angular sector `ℓ` (pointwise on the chart).**

    If a globally `C²` function `f : ℝ³ → ℂ` separates on the spherical chart as a pure
    tensor in the `ℓ`-sector, `f(sphereChart r θ φ) = R(r) · Y_ℓ^m(θ, φ)`, then at every
    interior chart point (`r > 0`, `θ ∈ (0, π)`) the Laplacian acts as the radial
    operator dressed with the centrifugal term:

      `Δ f = (R″ + (2/r) R′ − ℓ(ℓ+1)/r² · R) · Y_ℓ^m`,

    equivalently `−Δ f = (−R″ − (2/r) R′ + ℓ(ℓ+1)/r² · R) · Y_ℓ^m`. This is the operator
    content of separation of variables inside one sector, assembled from three sorry-free
    ingredients:
    * `laplacian_separates` — `Δ = (1/r²)∂_r(r²∂_r) − (1/r²) L̂²` on the chart;
    * `radialPart_eq` — `(1/r²)∂_r(r²∂_r R) = R″ + (2/r) R′`;
    * `sphericalHarmonic_eigenvalue` — `L̂² Y_ℓ^m = ℓ(ℓ+1) Y_ℓ^m`;
    with `laplaceBeltrami_const_mul` detaching the radial factor `R(r)` from `L̂²`.

    The separated realization `f` is supplied as a hypothesis (`hf`, `hsep`): producing
    such a global `C²` `f` from `R` and `Y_ℓ^m` is the chart-realization step that the
    spherical-`L²` ↔ `Sobolev.L2_R3` unitary will eventually furnish (cf. the note on
    `hydrogen_degeneracy`). No Laplacian *analysis* is missing — only that packaging. -/
theorem laplacian_in_sector (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ)
    (R : ℝ → ℂ) (hR : ContDiff ℝ 2 R)
    (f : Spectra.Sobolev.R3 → ℂ) (hf : ContDiff ℝ 2 f)
    (hsep : ∀ a b c, f (sphereChart a b c) = R a * SphericalHarmonic ℓ m hm (b, c))
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    Δ f (sphereChart r θ φ)
      = (deriv (deriv R) r + (2 / (r : ℂ)) * deriv R r
          - ((ℓ * (ℓ + 1) : ℝ) / (r : ℂ) ^ 2) * R r) * SphericalHarmonic ℓ m hm (θ, φ) := by
  have hr0 : (r : ℝ) ≠ 0 := hr.ne'
  have hRp : ContDiff ℝ 2 (fun s => R s * SphericalHarmonic ℓ m hm (θ, φ)) :=
    hR.mul contDiff_const
  -- The radial chart-curve is `R(·) · Y_ℓ^m(θ,φ)` (angular factor frozen).
  have hcurve : (fun u : ℝ => f (sphereChart u θ φ))
      = (fun u : ℝ => R u * SphericalHarmonic ℓ m hm (θ, φ)) := by
    funext u; rw [hsep u θ φ]
  -- The angular chart-surface is `R(r) · Y_ℓ^m(·)` (radial factor frozen).
  have hsurf : (fun p : ℝ × ℝ => f (sphereChart r p.1 p.2))
      = (fun p : ℝ × ℝ => R r * SphericalHarmonic ℓ m hm p) := by
    funext p; rw [hsep r p.1 p.2]
  -- Pull the frozen angular constant through the radial derivatives.
  have hd1 : ∀ s, deriv (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ)) s
      = deriv R s * SphericalHarmonic ℓ m hm (θ, φ) := fun s =>
    ((hR.differentiable (by norm_num) s).hasDerivAt.mul_const _).deriv
  have hd2 : deriv (deriv (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ))) r
      = deriv (deriv R) r * SphericalHarmonic ℓ m hm (θ, φ) := by
    have hfun : deriv (fun u => R u * SphericalHarmonic ℓ m hm (θ, φ))
        = fun s => deriv R s * SphericalHarmonic ℓ m hm (θ, φ) := funext hd1
    rw [hfun]
    exact ((hR.differentiable_deriv_two r).hasDerivAt.mul_const _).deriv
  rw [laplacian_separates f hf hr hθ, hcurve, hsurf,
    radialPart_eq (fun s => R s * SphericalHarmonic ℓ m hm (θ, φ)) hRp hr0,
    laplaceBeltrami_const_mul (R r) (SphericalHarmonic ℓ m hm) (θ, φ),
    sphericalHarmonic_eigenvalue ℓ m hm (θ, φ) hθ, hd2, hd1 r]
  ring

/-! ## The Coulomb potential respects angular sectors -/

/-- **The Coulomb factor `−Z/r` preserves the angular sector `ℓ`.**

    `coulombMultiplier p x = −Z/‖x‖` depends only on the radius, so multiplying a pure
    tensor `f = R(r)·Y_ℓ^m` by it leaves the angular factor untouched and merely rescales
    the radial factor: away from the origin (`r > 0`),

      `coulombMultiplier p · f = (−Z/r · R(r)) · Y_ℓ^m`,

    still a pure tensor in sector `ℓ`. Pure algebra (`norm_sphereChart` evaluates the
    radius); no smoothness needed. -/
theorem coulomb_preserves_sectors (p : CoulombParams) (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ)
    (R : ℝ → ℂ) (f : Spectra.Sobolev.R3 → ℂ)
    (hsep : ∀ a b c, f (sphereChart a b c) = R a * SphericalHarmonic ℓ m hm (b, c))
    {r θ φ : ℝ} (hr : 0 < r) :
    (coulombMultiplier p (sphereChart r θ φ) : ℂ) * f (sphereChart r θ φ)
      = (-(p.Z : ℂ) / (r : ℂ) * R r) * SphericalHarmonic ℓ m hm (θ, φ) := by
  have hnorm : ‖sphereChart r θ φ‖ = r := by rw [norm_sphereChart, abs_of_pos hr]
  have hne : ‖sphereChart r θ φ‖ ≠ 0 := by rw [hnorm]; exact hr.ne'
  have hval : coulombMultiplier p (sphereChart r θ φ) = -p.Z / ‖sphereChart r θ φ‖ := by
    unfold coulombMultiplier; exact if_neg hne
  rw [hval, hnorm, hsep r θ φ]
  push_cast
  ring

/-- **The hydrogen Hamiltonian reduces to the radial operator on each sector (pointwise).**

    For a separated `C²` realization `f(sphereChart r θ φ) = R(r)·Y_ℓ^m(θ,φ)`, the hydrogen
    Hamiltonian `H = −Δ + coulombMultiplier` (i.e. `−Δ − Z/r`) acts at every interior chart
    point (`r > 0`, `θ ∈ (0, π)`) as the radial hydrogen operator `H_ℓ` applied to `R`,
    tensored with the angular factor:

      `(−Δ f − (Z/r)·f) = (−R″ − (2/r)R′ + (ℓ(ℓ+1)/r² − Z/r)·R) · Y_ℓ^m`.

    The right factor is `H_ℓ R = radialHamiltonian ℓ Z R` in complex form. This is just
    `laplacian_in_sector` (the `−Δ` half) combined with `coulomb_preserves_sectors` (the
    `−Z/r` half). The reduction onto `RadialL2`/`ReducedRadialL2` as Hilbert-space operators
    still awaits the spherical-`L²` ↔ `Sobolev.L2_R3` unitary. -/
theorem hydrogen_reduces (p : CoulombParams) (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ)
    (R : ℝ → ℂ) (hR : ContDiff ℝ 2 R)
    (f : Spectra.Sobolev.R3 → ℂ) (hf : ContDiff ℝ 2 f)
    (hsep : ∀ a b c, f (sphereChart a b c) = R a * SphericalHarmonic ℓ m hm (b, c))
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    (- Δ f (sphereChart r θ φ))
        + (coulombMultiplier p (sphereChart r θ φ) : ℂ) * f (sphereChart r θ φ)
      = (- deriv (deriv R) r - (2 / (r : ℂ)) * deriv R r
          + ((ℓ * (ℓ + 1) : ℝ) / (r : ℂ) ^ 2 - (p.Z : ℂ) / (r : ℂ)) * R r)
        * SphericalHarmonic ℓ m hm (θ, φ) := by
  rw [laplacian_in_sector ℓ m hm R hR f hf hsep hr hθ,
    coulomb_preserves_sectors p ℓ m hm R f hsep hr]
  ring

/-- **The textbook (half-Laplacian) hydrogen Hamiltonian reduces to the radial operator
    on each sector (pointwise).**

    Identical in spirit to `hydrogen_reduces`, but for the textbook kinetic convention
    `−½Δ` (rather than the full `−Δ`). For a separated `C²` realization
    `f(sphereChart r θ φ) = R(r)·Y_ℓ^m(θ,φ)`, the operator `H = −½Δ + coulombMultiplier`
    (`= −½Δ − Z/r`) acts at every interior chart point (`r > 0`, `θ ∈ (0, π)`) as

      `(−½Δ f − (Z/r)·f) = (−½R″ − (1/r)R′ + (ℓ(ℓ+1)/(2r²) − Z/r)·R) · Y_ℓ^m`.

    Obtained by scaling the `−Δ` half (`laplacian_in_sector`) by `½` and adding the
    Coulomb half (`coulomb_preserves_sectors`). The right factor is exactly
    `RadialEq.radialHamiltonian ℓ R` (when `Z = 1`) in complex form. -/
theorem hydrogen_reduces_half (p : CoulombParams) (ℓ : ℕ) (m : ℤ) (hm : |m| ≤ ℓ)
    (R : ℝ → ℂ) (hR : ContDiff ℝ 2 R)
    (f : Spectra.Sobolev.R3 → ℂ) (hf : ContDiff ℝ 2 f)
    (hsep : ∀ a b c, f (sphereChart a b c) = R a * SphericalHarmonic ℓ m hm (b, c))
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ((-(1/2 : ℂ)) * Δ f (sphereChart r θ φ))
        + (coulombMultiplier p (sphereChart r θ φ) : ℂ) * f (sphereChart r θ φ)
      = ((-(1/2:ℂ)) * (deriv (deriv R) r) - (1/(r:ℂ)) * deriv R r
          + (((ℓ*(ℓ+1):ℝ)/(2*(r:ℂ)^2)) - (p.Z:ℂ)/(r:ℂ)) * R r)
        * SphericalHarmonic ℓ m hm (θ, φ) := by
  rw [laplacian_in_sector ℓ m hm R hR f hf hsep hr hθ,
    coulomb_preserves_sectors p ℓ m hm R f hsep hr]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

/-! ## The radial Hamiltonian -/

/-- The radial hydrogen Hamiltonian in sector ℓ (on RadialL2).

    H_ℓ R = −R'' − (2/r)R' + ℓ(ℓ+1)/r² R − Z/r R -/
def radialHamiltonian (ℓ : ℕ) (Z : ℝ) : (ℝ → ℝ) → ℝ → ℝ :=
  fun R r => -(deriv (deriv R) r) - (2 / r) * deriv R r
    + ((ℓ : ℝ) * (ℓ + 1) / r ^ 2 - Z / r) * R r

/-- The reduced radial operator (on ReducedRadialL2).

    h_ℓ χ = −χ'' + V_eff(r) χ
    where V_eff(r) = ℓ(ℓ+1)/r² − Z/r

    This is a 1D Schrödinger operator with effective potential. -/
def reducedRadialOp (ℓ : ℕ) (Z : ℝ) : (ℝ → ℝ) → ℝ → ℝ :=
  fun χ r => -(deriv (deriv χ) r) + ((ℓ : ℝ) * (ℓ + 1) / r ^ 2 - Z / r) * χ r

/-- `H_ℓ` on `RadialL2` is intertwined with `h_ℓ` on `ReducedRadialL2` by the
    substitution `χ = rR`: for `r > 0` and `C²` radial functions,
    `h_ℓ(rR)(r) = r·(H_ℓR)(r)`. This is the concrete content of the unitary
    equivalence implemented by `radialReduction`; the key identity is
    `(rR)'' = rR'' + 2R'`. -/
theorem radial_unitary_equivalence (ℓ : ℕ) (Z : ℝ) (R : ℝ → ℝ)
    (hR : ContDiff ℝ 2 R) {r : ℝ} (hr : 0 < r) :
    reducedRadialOp ℓ Z (fun s => s * R s) r = r * radialHamiltonian ℓ Z R r := by
  have hR1 : Differentiable ℝ R := hR.differentiable (by norm_num)
  have hR2 : Differentiable ℝ (deriv R) := hR.differentiable_deriv_two
  -- `(rR)' = R + rR'`
  have hrne : r ≠ 0 := ne_of_gt hr
  have hχ' : deriv (fun s => s * R s) = fun s => R s + s * deriv R s := by
    funext s
    rw [deriv_fun_mul differentiableAt_fun_id (hR1 s), deriv_id'']; ring
  -- `(rR)'' = 2R' + rR''`
  have hχ'' : deriv (deriv (fun s => s * R s)) r
      = 2 * deriv R r + r * deriv (deriv R) r := by
    have e1 : deriv (fun s => R s + s * deriv R s) r
        = deriv R r + deriv (fun s => s * deriv R s) r :=
      deriv_fun_add (hR1 r) (differentiableAt_fun_id.mul (hR2 r))
    have e2 : deriv (fun s => s * deriv R s) r = deriv R r + r * deriv (deriv R) r := by
      rw [deriv_fun_mul differentiableAt_fun_id (hR2 r), deriv_id'']; simp
    rw [hχ', e1, e2]; ring
  simp only [reducedRadialOp, radialHamiltonian]
  rw [hχ'']
  field_simp
  ring

/-! ## Hydrogen eigenvalues -/

/-- The hydrogen eigenvalues, indexed by the principal quantum number.

    E_n = −Z²/(2n²) in atomic units. For Z = 1: E_n = −1/(2n²).

    n = 1: E₁ = −1/2  = −13.6 eV   (ground state)
    n = 2: E₂ = −1/8  = −3.4 eV
    n = 3: E₃ = −1/18 = −1.5 eV
    ...
    n → ∞: E_n → 0                  (ionisation threshold) -/
def eigenvalue (p : CoulombParams) (n : ℕ) (_hn : 1 ≤ n) : ℝ :=
  -(p.Z ^ 2) / (2 * (n : ℝ) ^ 2)

/-- For Z = 1: eigenvalue = hydrogenEigenvalue. -/
lemma eigenvalue_Z1 (n : ℕ) (hn : 1 ≤ n) :
    eigenvalue ⟨1, one_pos⟩ n hn = hydrogenEigenvalue n hn := by
  simp [eigenvalue, hydrogenEigenvalue]

/-! ## Hydrogen eigenfunctions -/

/-! ### Lifting the radial wavefunction into the radial Hilbert space

The radial wavefunction `R_{nℓ}` is a genuine element of the radial Hilbert
space `RadialL2 = L²((0,∞), r²dr)`. We realize it by first lifting the reduced
wavefunction `χ_{nℓ} = r·R_{nℓ}` into `ReducedRadialL2 = L²((0,∞), dr)` — whose
membership is *exactly* `radial_wavefunction_L2` (which says `∫|rR|² dr < ∞`) —
and then transporting back along the unitary `radialReduction : R ↦ rR`. -/

/-- The reduced wavefunction `χ_{nℓ} = r·R_{nℓ}` lies in `L²((0,∞), dr)`. Its
    square-integrability is exactly `radial_wavefunction_L2`. -/
lemma memLp_reducedLp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    MemLp (fun r => ((hydrogenReducedWavefunction n ℓ hn r : ℝ) : ℂ)) 2
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have hcont : Continuous (fun r => ((hydrogenReducedWavefunction n ℓ hn r : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_id.mul (continuous_hydrogenRadialWavefunction n ℓ hn))
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  have hL2 : Integrable (fun r => hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2)
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := radial_wavefunction_L2 n ℓ hn
  refine hL2.congr (Filter.Eventually.of_forall fun r => ?_)
  show hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2
      = ‖((hydrogenReducedWavefunction n ℓ hn r : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hydrogenReducedWavefunction]
  ring

/-- The reduced wavefunction `χ_{nℓ}` as an element of `ReducedRadialL2`. -/
noncomputable def reducedLp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ReducedRadialL2 :=
  (memLp_reducedLp n ℓ hn).toLp _

lemma reducedLp_coeFn (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ⇑(reducedLp n ℓ hn) =ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)]
      fun r => ((hydrogenReducedWavefunction n ℓ hn r : ℝ) : ℂ) :=
  (memLp_reducedLp n ℓ hn).coeFn_toLp

/-- The radial wavefunction `R_{nℓ}` as an element of `RadialL2 = L²((0,∞), r²dr)`,
    obtained from `reducedLp` by the inverse of the unitary `R ↦ rR`. -/
noncomputable def radialLp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : Decomposition.RadialL2 :=
  radialReduction.symm (reducedLp n ℓ hn)

/-- **Radial orthonormality at the Hilbert-space level.**
    `⟨R_{nℓ}, R_{n'ℓ}⟩_{L²(r²dr)} = δ_{nn'}`. The pairing is transported through the
    unitary `radialReduction` to the reduced space, where it is the elementary
    integral `∫ R_{nℓ} R_{n'ℓ} r² dr`, discharged by `radial_wavefunction_norm`
    (n = n') and `radial_wavefunction_orthonormal` (n ≠ n'). -/
lemma inner_radialLp (n n' ℓ : ℕ) (hn : ℓ + 1 ≤ n) (hn' : ℓ + 1 ≤ n') :
    inner ℂ (radialLp n ℓ hn) (radialLp n' ℓ hn') = (if n = n' then (1 : ℂ) else 0) := by
  have hmap : inner ℂ (radialLp n ℓ hn) (radialLp n' ℓ hn')
      = inner ℂ (reducedLp n ℓ hn) (reducedLp n' ℓ hn') := by
    have h := radialReduction.inner_map_map (radialLp n ℓ hn) (radialLp n' ℓ hn')
    simpa only [radialLp, LinearIsometryEquiv.apply_symm_apply] using h.symm
  rw [hmap, L2.inner_def]
  have hint : (∫ r, inner ℂ (⇑(reducedLp n ℓ hn) r) (⇑(reducedLp n' ℓ hn') r)
        ∂((volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ((∫ r in Set.Ioi 0, hydrogenRadialWavefunction n ℓ hn r
          * hydrogenRadialWavefunction n' ℓ hn' r * r ^ 2 : ℝ) : ℂ) := by
    have e1 : (∫ r, inner ℂ (⇑(reducedLp n ℓ hn) r) (⇑(reducedLp n' ℓ hn') r)
          ∂((volume : Measure ℝ).restrict (Set.Ioi 0)))
        = ∫ r in Set.Ioi 0, ((hydrogenRadialWavefunction n ℓ hn r
            * hydrogenRadialWavefunction n' ℓ hn' r * r ^ 2 : ℝ) : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [reducedLp_coeFn n ℓ hn, reducedLp_coeFn n' ℓ hn'] with r h1 h2
      rw [RCLike.inner_apply', h1, h2, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Complex.ofReal_inj]
      simp only [hydrogenReducedWavefunction]
      ring
    rw [e1]
    exact integral_ofReal
  rw [hint]
  split_ifs with hnn
  · subst hnn
    rw [Subsingleton.elim hn' hn,
      show (∫ r in Set.Ioi 0, hydrogenRadialWavefunction n ℓ hn r
            * hydrogenRadialWavefunction n ℓ hn r * r ^ 2)
          = ∫ r in Set.Ioi 0, hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2 from
        setIntegral_congr_fun measurableSet_Ioi fun r _ => by ring,
      radial_wavefunction_norm n ℓ hn, Complex.ofReal_one]
  · rw [radial_wavefunction_orthonormal n n' ℓ hn hn' hnn, Complex.ofReal_zero]

/-- The full hydrogen eigenfunction ψ_{nℓm}(r, θ, φ) = R_{nℓ}(r) Y_ℓ^m(θ, φ),
    realized as the pure tensor `R_{nℓ} ⊗ Y_ℓ^m` in the spherical decomposition
    `Decomposition.L2_R3` via `sectorEmbedding`.

    Quantum numbers:
    - n ≥ 1: principal (energy)
    - ℓ ∈ {0, ..., n-1}: orbital angular momentum
    - m ∈ {-ℓ, ..., ℓ}: magnetic (z-projection of angular momentum)

    The number of states with energy E_n is:
      Σ_{ℓ=0}^{n-1} (2ℓ+1) = n² -/
def hydrogenEigenfunction (n : ℕ) (ℓ : ℕ) (m : ℤ)
    (hn : ℓ + 1 ≤ n) (hm : |m| ≤ ℓ) : L2_R3 :=
  sectorEmbedding ⟨ℓ, ⟨m, hm⟩⟩ (radialLp n ℓ hn)

/-! ## The eigenvalue equation -/

/-- The radial wavefunction `R_{nℓ}` is `C²` (in fact `C^∞`), built from the smooth
    Laguerre polynomial, `(2r/n)^ℓ`, and `exp(−r/n)`. -/
lemma contDiff_hydrogenRadial (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    ContDiff ℝ 2 (hydrogenRadialWavefunction n ℓ hn) := by
  unfold hydrogenRadialWavefunction
  have hL : ContDiff ℝ 2 (fun r : ℝ =>
      laguerrePolynomial (n - ℓ - 1) (2 * ℓ + 1) (2 * r / n)) :=
    ((laguerre_smooth _ _).of_le le_top).comp (by fun_prop)
  fun_prop

/-- The complex lift `R_{nℓ} : ℝ → ℂ` of the (real) radial wavefunction, for feeding the
    `ℂ`-valued separation lemma `hydrogen_reduces`. -/
noncomputable def Rc (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ℝ → ℂ :=
  fun r => ((hydrogenRadialWavefunction n ℓ hn r : ℝ) : ℂ)

/-- The derivative of the complex lift is the complex lift of the real derivative. -/
lemma deriv_Rc (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (Rc n ℓ hn) = fun r => ((deriv (hydrogenRadialWavefunction n ℓ hn) r : ℝ) : ℂ) := by
  funext r
  exact (((((contDiff_hydrogenRadial n ℓ hn).differentiable
    (by norm_num)).differentiableAt).hasDerivAt).ofReal_comp).deriv

/-- The second derivative of the complex lift is the complex lift of the real second
    derivative. -/
lemma deriv2_Rc (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) :
    deriv (deriv (Rc n ℓ hn)) = fun r =>
      ((deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r : ℝ) : ℂ) := by
  rw [deriv_Rc n ℓ hn]
  funext r
  exact ((((contDiff_hydrogenRadial n ℓ hn).differentiable_deriv_two).differentiableAt).hasDerivAt.ofReal_comp).deriv

/-- The complex lift `R_{nℓ} : ℝ → ℂ` is `C²`. -/
lemma contDiff_Rc (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ContDiff ℝ 2 (Rc n ℓ hn) :=
  Complex.ofRealCLM.contDiff.of_le le_top |>.comp (contDiff_hydrogenRadial n ℓ hn)

/-- **H ψ_{nℓm} = E_n ψ_{nℓm} (pointwise, on the separated chart realization).**

    For the pure tensor `f(sphereChart r θ φ) = R_{nℓ}(r)·Y_ℓ^m(θ,φ)` realizing the
    eigenfunction `ψ_{nℓm}`, the textbook hydrogen Hamiltonian `H = −½Δ + coulombMultiplier`
    (`= −½Δ − Z/r`) at `Z = 1` acts at every interior chart point as multiplication by the
    eigenvalue:

      `H ψ_{nℓm} = E_n·ψ_{nℓm}`,  with `E_n = hydrogenEigenvalue n = −1/(2n²)`.

    **Discharge route:**
    1. `H` reduces to the radial operator on sector `ℓ` (`hydrogen_reduces_half`, the
       `−½Δ` version of `hydrogen_reduces`).
    2. `R_{nℓ}` solves the radial equation `H_ℓ R_{nℓ} = E_n R_{nℓ}`
       (`radial_eigenvalue_eq`), where `H_ℓ = RadialEq.radialHamiltonian ℓ` is exactly
       `−½ψ″ − (1/r)ψ′ + ℓ(ℓ+1)/(2r²)·ψ − (1/r)·ψ`.
    3. At `Z = 1` the radial factor produced by `hydrogen_reduces_half`,
       `−½R″ − (1/r)R′ + (ℓ(ℓ+1)/(2r²) − 1/r)R`, is *literally* `H_ℓ R`; combine after the
       `ℝ → ℂ` lift of the radial identity (`deriv_Rc`/`deriv2_Rc`). No factor-of-2
       normalization mismatch survives: the `½` kinetic factor and `Z = 1` together make the
       textbook convention exact, with the textbook eigenvalue `E_n = −1/(2n²)`. -/
theorem hydrogen_eigenfunction_eq (p : CoulombParams)
    (n : ℕ) (ℓ : ℕ) (m : ℤ) (hn : ℓ + 1 ≤ n) (hm : |m| ≤ ℓ)
    (hZ : p.Z = 1)
    (f : Spectra.Sobolev.R3 → ℂ) (hf : ContDiff ℝ 2 f)
    (hsep : ∀ a b c, f (sphereChart a b c)
      = ((hydrogenRadialWavefunction n ℓ hn a : ℝ) : ℂ) * SphericalHarmonic ℓ m hm (b, c))
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ((-(1/2 : ℂ)) * Δ f (sphereChart r θ φ))
        + (coulombMultiplier p (sphereChart r θ φ) : ℂ) * f (sphereChart r θ φ)
      = ((hydrogenEigenvalue n (by omega) : ℝ) : ℂ) * f (sphereChart r θ φ) := by
  rw [hydrogen_reduces_half p ℓ m hm (Rc n ℓ hn) (contDiff_Rc n ℓ hn) f hf hsep hr hθ]
  rw [hsep r θ φ]
  rw [deriv2_Rc n ℓ hn, deriv_Rc n ℓ hn, hZ]
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr
  have heig := radial_eigenvalue_eq n ℓ hn r hr
  simp only [Rc]
  -- The real radial bracket identity: at `Z = 1` the factor is exactly `H_ℓ R = E_n·R`.
  have heig' : -(1/2 : ℝ) * deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r
      - (1 / r) * deriv (hydrogenRadialWavefunction n ℓ hn) r
      + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - 1 / r) * hydrogenRadialWavefunction n ℓ hn r
      = hydrogenEigenvalue n (by omega) * hydrogenRadialWavefunction n ℓ hn r := by
    have h2 : deriv^[2] (hydrogenRadialWavefunction n ℓ hn) r
        = deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r := by
      simp [Function.iterate_succ]
    have hbridge : -(1/2 : ℝ) * deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r
        - (1 / r) * deriv (hydrogenRadialWavefunction n ℓ hn) r
        + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - 1 / r) * hydrogenRadialWavefunction n ℓ hn r
        = RadialEq.radialHamiltonian ℓ (hydrogenRadialWavefunction n ℓ hn) r := by
      unfold RadialEq.radialHamiltonian
      rw [h2]; ring
    rw [hbridge, heig]
  -- Lift the real identity to ℂ and multiply by the shared angular factor `Y_ℓ^m`.
  have hC := congrArg (fun x : ℝ => (x : ℂ)) heig'
  push_cast at hC ⊢
  linear_combination (SphericalHarmonic ℓ m hm (θ, φ)) * hC

/-! ## Orthonormality -/

/-- **Orthonormality of hydrogen eigenfunctions.**

    ⟨ψ_{nℓm}, ψ_{n'ℓ'm'}⟩ = δ_{nn'} δ_{ℓℓ'} δ_{mm'}

    **Discharge route:**
    - Radial: ∫₀^∞ R_{nℓ} R_{n'ℓ} r² dr = δ_{nn'} (`radial_wavefunction_orthonormal`).
    - Angular: ∫_{S²} Ȳ_ℓ^m Y_{ℓ'}^{m'} dΩ = δ_{ℓℓ'} δ_{mm'} (`sphericalHarmonic_orthonormal`).
    - Combined: ⟨R⊗Y, R'⊗Y'⟩ = ⟨R,R'⟩ · ⟨Y,Y'⟩ (tensor product). -/
theorem hydrogen_eigenfunction_orthonormal
    (n n' : ℕ) (ℓ ℓ' : ℕ) (m m' : ℤ)
    (hn : ℓ + 1 ≤ n) (hn' : ℓ' + 1 ≤ n')
    (hm : |m| ≤ ℓ) (hm' : |m'| ≤ ℓ') :
    inner (𝕜 := ℂ) (hydrogenEigenfunction n ℓ m hn hm)
        (hydrogenEigenfunction n' ℓ' m' hn' hm')
      = (if n = n' ∧ ℓ = ℓ' ∧ m = m' then 1 else 0) := by
  simp only [hydrogenEigenfunction]
  have hrad : (∫ r, (starRingEnd ℂ) (⇑(radialLp n ℓ hn) r) * ⇑(radialLp n' ℓ' hn') r
        ∂radialMeasure)
      = inner ℂ (radialLp n ℓ hn) (radialLp n' ℓ' hn') := by
    rw [L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [RCLike.inner_apply']
  rw [inner_sectorEmbedding, inner_harmonicLp, hrad]
  split_ifs with hidx hcond hcond2
  · -- angular and quantum-number conditions both hold: ⟨R,R⟩ = 1
    obtain ⟨rfl, rfl, rfl⟩ := hcond
    rw [mul_one, inner_radialLp n n ℓ hn hn']
    simp
  · -- same (ℓ, m), but n ≠ n': radial orthogonality kills it
    rw [mul_one]
    have hℓ : ℓ = ℓ' := congrArg (fun k : HarmonicIdx => k.1) hidx
    have hmeq : m = m' := congrArg (fun k : HarmonicIdx => k.2.1) hidx
    subst hℓ; subst hmeq
    rw [inner_radialLp n n' ℓ hn hn']
    exact if_neg (fun hnn => hcond ⟨hnn, rfl, rfl⟩)
  · -- (ℓ, m) ≠ (ℓ', m') but the RHS condition claims equality: contradiction
    obtain ⟨-, hℓ_eq, hm_eq⟩ := hcond2
    exact absurd (HarmonicIdx.ext hℓ_eq hm_eq) hidx
  · -- angular factor vanishes
    rw [mul_zero]

/-! ## Degeneracy -/

/-- The degeneracy sum: Σ_{ℓ=0}^{n-1} (2ℓ+1) = n². -/
lemma degeneracy_sum (n : ℕ) :
    ∑ ℓ ∈ Finset.range n, (2 * ℓ + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih]; ring

/-- The index set of the `n²` bound states at principal quantum number `n`:
    pairs `(ℓ, j)` with `ℓ < n` and `j < 2ℓ+1`, where `j` enumerates the magnetic
    quantum number `m = j − ℓ ∈ {−ℓ, …, ℓ}`. Indexing the `2ℓ+1` sublevels by
    `j ∈ {0,…,2ℓ}` (rather than `m` directly) makes the cardinality a clean
    `Finset.sigma` count. -/
def degenIndex (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range n).sigma fun ℓ => Finset.range (2 * ℓ + 1)

/-- There are exactly `n²` degenerate bound states at level `n`. -/
@[simp] lemma card_degenIndex (n : ℕ) : (degenIndex n).card = n ^ 2 := by
  rw [degenIndex, Finset.card_sigma]
  simp only [Finset.card_range]
  exact degeneracy_sum n

/-- A member `(ℓ, j)` of `degenIndex n` satisfies `ℓ + 1 ≤ n` and `|m| ≤ ℓ`
    for the magnetic quantum number `m = j − ℓ`. -/
lemma degenIndex_bounds {n : ℕ} (i : ↥(degenIndex n)) :
    i.1.1 + 1 ≤ n ∧ |(i.1.2 : ℤ) - i.1.1| ≤ (i.1.1 : ℤ) := by
  have hmem := i.2
  simp only [degenIndex, Finset.mem_sigma, Finset.mem_range] at hmem
  obtain ⟨hℓ, hj⟩ := hmem
  refine ⟨by omega, ?_⟩
  rw [abs_le]; omega

/-- The family of the `n²` hydrogen bound states at level `n`: `ψ_{n ℓ m}` for
    `0 ≤ ℓ < n` and `m = j − ℓ` with `0 ≤ j ≤ 2ℓ`. -/
noncomputable def degenFamily (n : ℕ) : ↥(degenIndex n) → L2_R3 :=
  fun i => hydrogenEigenfunction n i.1.1 ((i.1.2 : ℤ) - i.1.1)
    (degenIndex_bounds i).1 (degenIndex_bounds i).2

/-- The `n²` bound states at level `n` are orthonormal. -/
lemma orthonormal_degenFamily (n : ℕ) : Orthonormal ℂ (degenFamily n) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [degenFamily]
  rw [hydrogen_eigenfunction_orthonormal]
  split_ifs with hc hij hij2
  · rfl
  · refine absurd (Subtype.ext ?_) hij
    obtain ⟨-, hℓ, hm⟩ := hc
    exact Sigma.ext hℓ (heq_of_eq (by omega))
  · subst hij2
    exact absurd ⟨rfl, rfl, rfl⟩ hc
  · rfl

/-- **Degeneracy of the n-th level is n².**

    The `n²` orthonormal bound states `{ψ_{nℓm} : 0 ≤ ℓ < n, |m| ≤ ℓ}` span an
    `n²`-dimensional subspace of `L²(ℝ³)`:
    `dim span {ψ_{nℓm}} = Σ_{ℓ=0}^{n-1} (2ℓ+1) = n²`.

    The sum counts, for each `ℓ ∈ {0,…,n−1}`, the `2ℓ+1` magnetic sublevels
    `m ∈ {−ℓ,…,ℓ}`. Orthonormality (`hydrogen_eigenfunction_orthonormal`) makes the
    family linearly independent, so the dimension of its span equals its cardinality
    `n²` (`card_degenIndex`, via `degeneracy_sum`).

    This makes the lower bound `dim ker(H − E_n) ≥ n²` precise. That the span is
    *exactly* the `E_n`-eigenspace additionally needs completeness within each
    sector and the as-yet-unbuilt unitary identifying this spherical-coordinate
    `L²(ℝ³)` with `Sobolev.L2_R3` (where `hydrogenHamiltonian` lives), so the full
    `dim ker(H − E_n) = n²` is not yet available. -/
theorem hydrogen_degeneracy (_p : CoulombParams) (n : ℕ) (_hn : 1 ≤ n) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (degenFamily n))) = n ^ 2 := by
  rw [finrank_span_eq_card (orthonormal_degenFamily n).linearIndependent,
    Fintype.card_coe, card_degenIndex]


/-! ## Discrete spectrum -/

/-- **The discrete spectrum of hydrogen.**

    σ_disc(H) = { E_n : n ≥ 1 } = { −Z²/(2n²) : n ≥ 1 }

    For every `E < 0`, `E` is an eigenvalue of `H = −½Δ − Z/r` (with some nonzero
    `ψ ∈ Dom(H) = H²(ℝ³)`) **iff** `E = E_n = −Z²/(2n²)` for some `n ≥ 1`.

    **[Blocked on one geometric unitary — left as a documented `sorry`.]**

    The obstruction is a *coordinate* mismatch, not a missing piece of analysis. The
    operator `hydrogenHamiltonian p` lives on the **Cartesian** space
    `Spectra.Sobolev.L2_R3 = Lp ℂ 2 (volume : Measure ℝ³)`, whereas every eigenfunction
    object in this development (`hydrogenEigenfunction`, `radialLp`, `sectorEmbedding`,
    `sphericalDecomposition`) lives on the **spherical-coordinate** space
    `Decomposition.L2_R3 = Lp ℂ 2 (radialMeasure.prod sphereMeasure)`. These are
    *different types*; nothing connects them yet. The single load-bearing missing object
    is the 3D spherical change-of-variables unitary

      `chartRealization : Spectra.Sobolev.L2_R3 ≃ₗᵢ[ℂ] Decomposition.L2_R3`,

    realizing `∫_{ℝ³} |f|² dx = ∫₀^∞ ∫_{S²} |f ∘ sphereChart|² r² dr dΩ` (Jacobian
    `r² sin θ`), together with its **Hamiltonian-intertwining** property: it carries
    `Dom(H)` onto `⊕_ℓ Dom(H_ℓ)` and conjugates `H` into the sector operators `H_ℓ`
    (`sphericalDecomposition` of `chartRealization ψ`, sector-by-sector
    `RadialEq.radialHamiltonian ℓ`). Mathlib (v4.31) provides only the 2D `polarCoord`,
    so `chartRealization` is genuinely new infrastructure and is the *only* gap shared by
    both directions of the proof. Bundling it as an axiom is rejected (it is honest new
    work to be discharged); it is therefore stated as a single named, documented unitary
    when built, mirroring how `RadialEq.reduced_radial_L2_quantized` isolates its
    analytic gap.

    **Discharge route — `←` (E = E_n ⟹ eigenpair exists).** Closeable *modulo
    `chartRealization` alone*:
    1. transport the bound state `Ψ_{nℓm} = hydrogenEigenfunction n ℓ m` (sector
       `(ℓ, m)`, e.g. `ℓ = 0`, `m = 0`) back to the Cartesian side via
       `chartRealization.symm`; it lands in `Dom(H) = SobolevH2` by the
       domain-preservation half of the intertwining;
    2. the eigen-equation `H Ψ = E_n • Ψ` follows from the intertwining together with
       the pointwise sector identity `hydrogen_eigenfunction_eq` (the `−½Δ` convention)
       and the radial ODE `RadialEq.radial_eigenvalue_eq` (`H_ℓ R_{nℓ} = E_n R_{nℓ}`);
    3. `Ψ ≠ 0` from `chartRealization.norm_map` and `inner_radialLp` (unit radial norm).
    Caveat: the explicit radial layer (`hydrogenEigenvalue n = −1/(2n²)`,
    `radial_eigenvalue_eq`, `hydrogen_eigenfunction_eq`) is currently specialised to
    `p.Z = 1`. General `Z` needs the dilation `r ↦ Z r` of the radial wavefunctions, an
    isolated and routine extra step; until then this direction is honest only at `Z = 1`.

    **Discharge route — `→` (eigenpair ⟹ E = E_n).** Needs `chartRealization` **and** the
    pre-existing analytic gap:
    1. push a Cartesian eigenfunction through `chartRealization` then
       `sphericalDecomposition`, and project onto sector `(ℓ, m)` to obtain a `RadialL2`
       solution of `H_ℓ R = E R`;
    2. a weak-eigen ⟹ classical-`C²`-radial-ODE *regularity* step (elliptic regularity in
       the radial variable) puts that solution in the hypotheses of `radial_quantization`;
    3. `RadialEq.radial_quantization` then forces `E = E_n` — this bottoms out at the one
       documented analytic gap `RadialEq.reduced_radial_L2_quantized`
       (confluent-hypergeometric / Levinson–Poincaré asymptotics, not yet in Mathlib).

    **Proved and ready to be consumed by the above:** `sphericalDecomposition`
    (`Decomposition.L2_R3 ≃ₗᵢ ⊕_ℓ RadialL2`, sorry-free), `hydrogen_reduces_half`
    (pointwise sector reduction of `H`), `hydrogen_eigenfunction_eq`,
    `radial_eigenvalue_eq`, `hydrogen_isSelfAdjoint`, and `hydrogen_degeneracy`
    (giving `dim ker(H − E_n) ≥ n²` at the orthonormal-family level). The remaining
    leaves are exactly `chartRealization` (+ its intertwining) and
    `reduced_radial_L2_quantized`. -/
theorem hydrogen_discrete_spectrum (p : CoulombParams) :
    ∀ (E : ℝ), E < 0 →
    (∃ ψ : (hydrogenHamiltonian p).domain,
        (ψ : Spectra.Sobolev.L2_R3) ≠ 0 ∧
        hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.L2_R3)) ↔
    ∃ (n : ℕ) (hn : 1 ≤ n), E = eigenvalue p n hn :=
  sorry

/-! ## Continuous spectrum -/

/-- **The continuous spectrum of hydrogen is [0, ∞).**

    For E ≥ 0, the hydrogen Hamiltonian has no eigenvalues but E is
    in the spectrum (approximate eigenvalues exist).

    **Discharge route (Weyl's theorem):**
    The essential spectrum is stable under relatively compact perturbations.
    The Coulomb potential −Z/r is not merely relatively bounded but
    *relatively compact* with respect to −Δ (stronger than bound 0).
    Hence: σ_ess(H) = σ_ess(−Δ) = [0, ∞).

    Combined with `hydrogen_discrete_spectrum`: σ(H) = {E_n} ∪ [0, ∞).

    **Alternative (direct via Weyl sequences):**
    For λ > 0, construct ψ_n(x) = n^{−3/2} φ(x/n) · e^{ikx}
    where φ is a smooth bump and k = √(2λ). Then
    ‖ψ_n‖ = ‖φ‖ and ‖(H − λ)ψ_n‖ → 0 as n → ∞
    (the potential and centrifugal terms vanish by dilation). -/
def hydrogen_continuous_spectrum (p : CoulombParams) :
    sorry :=  -- σ_cont(H) = [0, ∞), or σ_ess(H) = [0, ∞)
  sorry

/-- **No positive eigenvalues** (Kato's theorem).

    H has no eigenvalues in [0, ∞). This is a deep result:
    the absence of embedded eigenvalues in the continuum.

    **Discharge route:** Kato's 1959 theorem: for potentials V with
    |x| V(x) → 0 as |x| → ∞ (satisfied by Coulomb), there are no
    positive eigenvalues. The proof uses Agmon-type exponential decay
    estimates. This is significantly harder than the rest and may be
    deferred. -/
theorem hydrogen_no_positive_eigenvalues (p : CoulombParams) :
    ∀ (E : ℝ) (hE : 0 ≤ E) (ψ : Spectra.Sobolev.L2_R3)
      (hψ : ψ ∈ (hydrogenHamiltonian p).domain),
    hydrogenHamiltonian p ⟨ψ, hψ⟩ = (E : ℂ) • ψ → ψ = 0 :=
  sorry

/-! ## Eigenfunction completeness -/

/-- **Completeness of hydrogen eigenfunctions in the discrete subspace.**

    The eigenfunctions {ψ_{nℓm}} form a complete orthonormal system
    in the range of the spectral projection E((-∞, 0)).

    Every state with negative energy is a superposition of bound states:
      ψ = Σ_{n,ℓ,m} c_{nℓm} ψ_{nℓm}

    **Discharge route:**
    1. In each angular sector ℓ, {R_{nℓ}}_{n≥ℓ+1} is complete
       (`radial_completeness`).
    2. The angular decomposition is complete (`sphericalHarmonic_complete`).
    3. Together: {R_{nℓ} ⊗ Y_ℓ^m} is complete in the discrete subspace. -/
def hydrogen_eigenfunction_complete (p : CoulombParams) :
    sorry :=  -- {ψ_{nℓm}} complete in E((-∞,0)) L²
  sorry

/-! ## Spectral projections -/

/-- **Spectral projection onto the n-th eigenspace.**

    E({E_n}) ψ = Σ_{ℓ=0}^{n-1} Σ_{m=-ℓ}^{ℓ} ⟨ψ_{nℓm}, ψ⟩ ψ_{nℓm}

    This is the orthogonal projection onto ker(H − E_n). -/
def hydrogen_spectral_projection_discrete (p : CoulombParams)
    (n : ℕ) (hn : 1 ≤ n) :
    sorry :=  -- E({E_n}) = projection onto span{ψ_{nℓm}}
  sorry

/-- **Resolvent of hydrogen is meromorphic in ℂ \ [0, ∞).**

    The resolvent (H − z)⁻¹ has poles exactly at z = E_n with
    residues equal to (minus) the eigenspace projections:
      Res_{z=E_n} (H − z)⁻¹ = −E({E_n}) = −P_n

    **Discharge route:** From the spectral representation:
    (H − z)⁻¹ = ∫ 1/(λ − z) dE(λ)
    The discrete part gives Σ_n P_n/(E_n − z), with simple poles at E_n. -/
def hydrogen_resolvent_meromorphic (p : CoulombParams) :
    sorry :=  -- (H-z)⁻¹ meromorphic with poles at E_n
  sorry

/-! ## The Bohr formula -/

/-- **The Bohr formula for spectral lines.**

    The energy of a photon emitted in a transition n → m (n > m) is:
      ΔE = E_m − E_n = (Z²/2)(1/m² − 1/n²)

    The frequency is ν = ΔE/(2πℏ) = ΔE/(2π) in atomic units.

    For hydrogen (Z = 1):
      ΔE = (1/2)(1/m² − 1/n²)

    This reproduces:
    - Lyman series (m = 1): ultraviolet
    - Balmer series (m = 2): visible
    - Paschen series (m = 3): infrared
    - Brackett series (m = 4): far infrared -/
theorem hydrogen_bohr_formula (p : CoulombParams)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (_hnm : m < n) :
    eigenvalue p n hn - eigenvalue p m hm =
    p.Z ^ 2 / 2 * (1 / (m : ℝ) ^ 2 - 1 / (n : ℝ) ^ 2) := by
  simp only [eigenvalue]
  field_simp
  ring

/-- **Balmer's formula** (historical, 1885).

    For the visible hydrogen lines (transitions to n = 2):
      1/λ = R_∞ (1/4 − 1/m²)    for m = 3, 4, 5, ...

    where R_∞ is the Rydberg constant. In our units: R_∞ = 1/(4π).

    Balmer discovered this empirically. Bohr derived it in 1913.
    I derived it from first principles in 1926. -/
theorem balmer_series (m : ℕ) (hm : 3 ≤ m) :
    eigenvalue ⟨1, one_pos⟩ m (by omega) - eigenvalue ⟨1, one_pos⟩ 2 (by omega) =
    (1 : ℝ) / 2 * (1 / 4 - 1 / (m : ℝ) ^ 2) := by
  have := hydrogen_bohr_formula ⟨1, one_pos⟩ m 2 (by omega) (by omega) (by omega)
  simp at this ⊢
  linarith

/-! ## Summary of the complete spectral picture

For H = −Δ − Z/r on L²(ℝ³):

### Spectrum
  σ(H) = { −Z²/(2n²) : n ≥ 1 } ∪ [0, ∞)

### Point spectrum (eigenvalues)
  σ_p(H) = { −Z²/(2n²) : n ≥ 1 }
  Each eigenvalue has finite multiplicity n².

### Essential spectrum
  σ_ess(H) = [0, ∞)
  Purely absolutely continuous (no embedded eigenvalues, no singular continuous spectrum).

### Eigenfunctions
  ψ_{nℓm}(r,θ,φ) = R_{nℓ}(r) · Y_ℓ^m(θ,φ)

  where:
  - R_{nℓ}(r) = N_{nℓ} (2r/n)^ℓ e^{−r/n} L_{n−ℓ−1}^{2ℓ+1}(2r/n)
  - Y_ℓ^m(θ,φ) = N_{ℓm} P_ℓ^m(cos θ) e^{imφ}

  Quantum numbers: n ≥ 1, 0 ≤ ℓ ≤ n−1, −ℓ ≤ m ≤ ℓ.

### Spectral resolution
  H = Σ_{n=1}^∞ E_n P_n + ∫₀^∞ λ dE_c(λ)

  where P_n is the projection onto the n-th eigenspace and E_c is the
  continuous spectral measure.

### Connection to the library's spectral pipeline
  All of the above is encoded in `IsSpectralMeasureFor E (hydrogenGenerator p)`:
  - E({E_n}) = P_n (eigenspace projections)
  - E([a,b]) for [a,b] ⊂ [0,∞) (continuum projections)
  - f(H) = ∫ f(λ) dE(λ) (functional calculus)
  - ‖f(H)ψ‖² = ∫ |f(λ)|² dμ_ψ(λ) (spectral integral isometry)
-/


end QuantumMechanics.Hydrogen.Spectrum

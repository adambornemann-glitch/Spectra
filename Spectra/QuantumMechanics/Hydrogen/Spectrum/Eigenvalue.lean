/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian

/-!
# The Hydrogen Eigenvalue Equation

Assembles the pointwise sector-reduction of the hydrogen Hamiltonian with the
Hilbert-space lift of the radial wavefunction, to prove the eigenvalue equation
`H ψ_{nℓm} = E_n ψ_{nℓm}` and the orthonormality of the eigenfunctions
`ψ_{nℓm}(r,θ,φ) = R_{nℓ}(r) Y_ℓ^m(θ,φ)`.

## Main definitions

* `radialLp`, `reducedLp` — the radial wavefunction `R_{nℓ}` and the reduced
  wavefunction `χ_{nℓ} = r·R_{nℓ}` as genuine elements of the radial Hilbert spaces
  `RadialL2 = L²((0,∞), r²dr)` and `ReducedRadialL2 = L²((0,∞), dr)`.
* `hydrogenEigenfunction` — the full eigenfunction `ψ_{nℓm}`, realized as the pure
  tensor `R_{nℓ} ⊗ Y_ℓ^m` in the spherical decomposition `l2R3`.
* `eigenvalue` — the hydrogen eigenvalues `E_n = −Z²/(2n²)` for general `Z`.

## Main theorems

* `hydrogen_reduces`, `hydrogen_reduces_half` — the hydrogen Hamiltonian (full- and
  half-Laplacian kinetic conventions) acts on a separated realization as the radial
  operator dressed with the centrifugal term, sector by sector.
* `hydrogen_eigenfunction_eq` — **H ψ_{nℓm} = E_n ψ_{nℓm}** (pointwise, on the
  separated chart realization), for the textbook `Z = 1` Hamiltonian.
* `hydrogen_eigenfunction_orthonormal` — `⟨ψ_{nℓm}, ψ_{n'ℓ'm'}⟩ = δ_{nn'} δ_{ℓℓ'} δ_{mm'}`.

These results reproduce, with complete mathematical rigour, Schrödinger's 1926
spectral series. The eigenvalues agree exactly with Bohr's 1913 formula — but
here they are *derived*, not postulated.

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I-IV*][schrodinger1926]
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex
open scoped Topology Laplacian
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics (SphericalHarmonic sphericalHarmonic_eigenvalue
  laplaceBeltrami_const_mul)
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)

/-! ## Separation of the Laplacian

The pointwise separation `−Δ = −(1/r²)∂_r(r²∂_r) + L̂²/r²` (with `L̂² = laplaceBeltrami`
the angular Laplacian on S²) is developed in `Laplacian.Spherical`, all sorry-free:

* `sphereChart`, `norm_sphereChart` — the spherical chart `(r,θ,φ) ↦ ℝ³`;
* `radialPart_eq` — the radial operator in divergence form equals the expanded form,
  `(1/r²)∂_r(r²∂_r R) = R″ + (2/r)R′`; this is the radial half at the operator level,
  matching `RadialEq.radialHamiltonian`;
* `laplacian_comp_norm` — `Δ(g∘‖·‖) = g″ + (2/r)g′` (radial Laplacian of a radial
  function), and `laplacian_separates` — the full pointwise separation on the chart,
  proved via the per-direction chain rule through the chart curves.
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
    spherical-`L²` ↔ `Sobolev.l2R3` unitary will eventually furnish (cf. the note on
    `degenFamily_span_finrank`). No Laplacian *analysis* is missing — only that packaging. -/
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

    The right factor is `H_ℓ R = radialHamiltonianGen ℓ Z R` in complex form. This is just
    `laplacian_in_sector` (the `−Δ` half) combined with `coulomb_preserves_sectors` (the
    `−Z/r` half). The reduction onto `RadialL2`/`ReducedRadialL2` as Hilbert-space operators
    still awaits the spherical-`L²` ↔ `Sobolev.l2R3` unitary. -/
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

/-- The radial hydrogen Hamiltonian in sector `ℓ`, for a general charge `Z` (on `RadialL2`).
    Distinct from `RadialEq.radialHamiltonian` (which is the *half*-Laplacian, fixed-`Z = 1`
    textbook convention): this is the full-Laplacian operator with `Z` left free, matching
    `hydrogen_reduces` (as opposed to `hydrogen_reduces_half`).

    H_ℓ R = −R'' − (2/r)R' + ℓ(ℓ+1)/r² R − Z/r R -/
def radialHamiltonianGen (ℓ : ℕ) (Z : ℝ) : (ℝ → ℝ) → ℝ → ℝ :=
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
    reducedRadialOp ℓ Z (fun s => s * R s) r = r * radialHamiltonianGen ℓ Z R r := by
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
  simp only [reducedRadialOp, radialHamiltonianGen]
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
    n → ∞: E_n → 0                  (ionisation threshold)

    The hypothesis `_hn : 1 ≤ n` is unused in the formula (matching
    `hydrogenEigenvalue`'s own pre-existing signature) but kept for API parity: every
    consumer (`eigenvalue_Z1`, `hydrogen_discrete_spectrum`, `forward_eigenvalue`, ...)
    already carries a principal-quantum-number witness at the call site, so it costs
    nothing to demand it here and it documents that `n = 0` is not a physical state. -/
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
  change hydrogenRadialWavefunction n ℓ hn r ^ 2 * r ^ 2
      = ‖((hydrogenReducedWavefunction n ℓ hn r : ℝ) : ℂ)‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hydrogenReducedWavefunction]
  ring

/-- The reduced wavefunction `χ_{nℓ}` as an element of `ReducedRadialL2`. -/
noncomputable def reducedLp (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ReducedRadialL2 :=
  (memLp_reducedLp n ℓ hn).toLp _

/-- The `L²` element `reducedLp n ℓ hn` agrees almost everywhere with the pointwise
    reduced wavefunction `χ_{nℓ}(r) = r·R_{nℓ}(r)` (as a `ℂ`-valued function). -/
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
    `Decomposition.l2R3` via `sectorEmbedding`.

    Quantum numbers:
    - n ≥ 1: principal (energy)
    - ℓ ∈ {0, ..., n-1}: orbital angular momentum
    - m ∈ {-ℓ, ..., ℓ}: magnetic (z-projection of angular momentum)

    The number of states with energy E_n is:
      Σ_{ℓ=0}^{n-1} (2ℓ+1) = n² -/
def hydrogenEigenfunction (n : ℕ) (ℓ : ℕ) (m : ℤ)
    (hn : ℓ + 1 ≤ n) (hm : |m| ≤ ℓ) : l2R3 :=
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
  have h1 : Differentiable ℝ (deriv (hydrogenRadialWavefunction n ℓ hn)) :=
    (contDiff_hydrogenRadial n ℓ hn).differentiable_deriv_two
  exact (((h1.differentiableAt).hasDerivAt).ofReal_comp).deriv

/-- The complex lift `R_{nℓ} : ℝ → ℂ` is `C²`. -/
lemma contDiff_Rc (n ℓ : ℕ) (hn : ℓ + 1 ≤ n) : ContDiff ℝ 2 (Rc n ℓ hn) :=
  Complex.ofRealCLM.contDiff.of_le le_top |>.comp (contDiff_hydrogenRadial n ℓ hn)

/-- **H ψ_{nℓm} = E_n ψ_{nℓm} (pointwise, on the separated chart realization).**

    For the pure tensor `f(sphereChart r θ φ) = R_{nℓ}(r)·Y_ℓ^m(θ,φ)` realizing the
    eigenfunction `ψ_{nℓm}`, the textbook hydrogen Hamiltonian `H = −½Δ + coulombMultiplier`
    (`= −½Δ − Z/r`) at `Z = 1` acts at every interior chart point as multiplication by the
    eigenvalue:
      `H ψ_{nℓm} = E_n·ψ_{nℓm}`,  with `E_n = hydrogenEigenvalue n = −1/(2n²)`. -/
theorem hydrogen_eigenfunction_eq (p : CoulombParams)
    (n : ℕ) (ℓ : ℕ) (m : ℤ) (hn : ℓ + 1 ≤ n) (hn1 : 1 ≤ n) (hm : |m| ≤ ℓ)
    (hZ : p.Z = 1)
    (f : Spectra.Sobolev.R3 → ℂ) (hf : ContDiff ℝ 2 f)
    (hsep : ∀ a b c, f (sphereChart a b c)
      = ((hydrogenRadialWavefunction n ℓ hn a : ℝ) : ℂ) * SphericalHarmonic ℓ m hm (b, c))
    {r θ φ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    ((-(1/2 : ℂ)) * Δ f (sphereChart r θ φ))
        + (coulombMultiplier p (sphereChart r θ φ) : ℂ) * f (sphereChart r θ φ)
      = ((hydrogenEigenvalue n hn1 : ℝ) : ℂ) * f (sphereChart r θ φ) := by
  rw [hydrogen_reduces_half p ℓ m hm (Rc n ℓ hn) (contDiff_Rc n ℓ hn) f hf hsep hr hθ]
  rw [hsep r θ φ]
  rw [deriv2_Rc n ℓ hn, deriv_Rc n ℓ hn, hZ]
  have _hrne : (r : ℝ) ≠ 0 := ne_of_gt hr
  have heig := radial_eigenvalue_eq n ℓ hn r hr
  simp only [Rc]
  -- The real radial bracket identity: at `Z = 1` the factor is exactly `H_ℓ R = E_n·R`.
  have heig' : -(1/2 : ℝ) * deriv (deriv (hydrogenRadialWavefunction n ℓ hn)) r
      - (1 / r) * deriv (hydrogenRadialWavefunction n ℓ hn) r
      + ((ℓ * (ℓ + 1) : ℝ) / (2 * r ^ 2) - 1 / r) * hydrogenRadialWavefunction n ℓ hn r
      = hydrogenEigenvalue n hn1 * hydrogenRadialWavefunction n ℓ hn r := by
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

    ⟨ψ_{nℓm}, ψ_{n'ℓ'm'}⟩ = δ_{nn'} δ_{ℓℓ'} δ_{mm'} -/
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


end QuantumMechanics.Hydrogen.Spectrum

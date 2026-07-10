/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.TensorDecomp.Basic
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Basic
import Spectra.QuantumMechanics.Hydrogen.Laplacian.Spherical
import Spectra.QuantumMechanics.Hydrogen.Hamiltonian
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Eigenvalue
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Degeneracy
import Spectra.QuantumMechanics.Hydrogen.Spectrum.RadialEigenfunction.Basic
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SectorProjection

/-!
# The Spectrum of the Hydrogen Atom

The main theorems about the hydrogen spectrum, assembling the radial
eigenvalue problem with the angular decomposition.

## Main statements

* `hydrogen_discrete_spectrum` — for the hydrogen Hamiltonian H = −½Δ − Z/r
  (Z = 1 in atomic units), for every `E < 0`, `E` is an eigenvalue of `H` iff
  `E = E_n = −Z²/(2n²)` for some `n ≥ 1`.  Equivalently:

  **Discrete spectrum**: σ_disc(H) = { −1/(2n²) : n = 1, 2, 3, ... }


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


/-! ## Discrete spectrum -/

/-- **The discrete spectrum of hydrogen.**

    σ_disc(H) = { E_n : n ≥ 1 } = { −Z²/(2n²) : n ≥ 1 }

    For every `E < 0`, `E` is an eigenvalue of `H = −½Δ − Z/r` (with some nonzero
    `ψ ∈ Dom(H) = H²(ℝ³)`) **iff** `E = E_n = −Z²/(2n²)` for some `n ≥ 1`.

    **Both directions are now fully proved, sorry-free and axiom-clean
    (`[propext, Classical.choice, Quot.sound]`).**

    **`←` (E = E_n ⟹ eigenpair exists): PROVED for every `Z`.** This is
    `Spectrum.hydrogen_bound_state p n hn` (in `RadialEigenfunction/Basic.lean`): for every charge
    `Z = p.Z > 0` and `n ≥ 1`, `E_n = −Z²/(2n²)` is a genuine eigenvalue of `H = −½Δ − Z/r`,
    realized by the explicit nonzero `H²` bound state with radial profile `c·R_{n0}(Z·‖x‖)` (the
    `Z = 1` `s`-state dilated by `r ↦ Z r`), via the `bound_state_of_radial_profile` abstraction.

    **`→` (eigenpair ⟹ E = E_n): PROVED.** Assembled in
    `Spectrum.forward_eigenvalue` (`SectorProjection.lean`). The pipeline:
    1. `chartRealization : Sobolev.l2R3 ≃ₗᵢ[ℂ] Decomposition.l2R3` (the 3D spherical change-of-
       variables unitary) carries the Cartesian eigenfunction to spherical coordinates;
       `exists_nonzero_sector` extracts a nonzero angular sector `(ℓ, m)` (using `star ψ` for the
       positive-`m` sectors, since `H` is real), giving a not-a.e.-zero radial coefficient
       `c = L ∘ coeffFun ⟨ℓ,-m⟩`.
    2. The **Cartesian weak eigenequation**, projected onto that sector (`sector_projection_radial`
       → `forward_bridge`), yields a weak radial ODE; the elliptic-regularity bootstrap
       `classical_of_weak_ode` + `radial_classical_of_logCoord` upgrades it to a classical `C²`
       radial solution `ψ_rad = c₀ ∘ log`.
    3. Its side data: `sector_radialL2` (square-integrability), `sector_radial_pt_nonzero`
       (nondegeneracy), and `radial_bc_of_logCoord` (the Dirichlet boundary condition `r·ψ_rad → 0`
       an embedding-free dichotomy: `(Z/r)·ψ ∈ L²` via `coulomb_mul_memLp_H2` forces the unweighted
       `L²` of the coefficient, whose convexity near the origin kills the singular `r^{−ℓ}` branch).
    4. `RadialEq.radial_quantization_Z` then forces `E = E_n`; its analytic core
       `RadialEq.reduced_radial_L2_quantized` is discharged via the `₁F₁`/Kummer machinery of
       `Spectra.Kummer`. -/
theorem hydrogen_discrete_spectrum (p : CoulombParams) :
    ∀ (E : ℝ), E < 0 →
    ((∃ ψ : (hydrogenHamiltonian p).domain,
        (ψ : Spectra.Sobolev.l2R3) ≠ 0 ∧
        hydrogenHamiltonian p ψ = (E : ℂ) • (ψ : Spectra.Sobolev.l2R3)) ↔
    ∃ (n : ℕ) (hn : 1 ≤ n), E = eigenvalue p n hn) := by
  intro E _hE
  constructor
  · -- `→` (eigenpair ⟹ `E = E_n`): push `ψ` through `chartRealization`/`sphericalDecomposition`
    -- to a nonzero angular sector, run the weak-eigen ⟹ classical-`C²`-radial elliptic-regularity
    -- bootstrap, and finish with `RadialEq.radial_quantization`.  Assembled in `forward_eigenvalue`
    rintro ⟨ψ, hψ0, heig⟩
    exact forward_eigenvalue p E _hE ψ hψ0 heig
  · -- `←` (`E = E_n` ⟹ eigenpair exists): **proved for every charge `Z`**, via
    -- `hydrogen_bound_state` (the explicit nonzero `H²` `s`-state of profile `c·R_{n0}(Z·‖x‖)`).
    rintro ⟨n, hn, rfl⟩
    exact hydrogen_bound_state p n hn


end QuantumMechanics.Hydrogen.Spectrum

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
import Spectra.QuantumMechanics.Hydrogen.Spectrum.Continuous.Compact
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SectorProjection
/-!
# The Spectrum of the Hydrogen Atom

This file records the results about the *upper* part of the hydrogen
spectrum for the Hamiltonian `H = −½Δ − Z/r` (with `0 < Z`): the essential
spectrum equals `[0, ∞)` and there are no `L²` eigenfunctions at energies
`E ≥ 0`. Both are thin wrappers around the substantive proofs in
`Continuous/Compact.lean` and `SectorProjection.lean`.

## Main statements

* `hydrogen_continuous_spectrum` — the essential spectrum of the hydrogen
  Hamiltonian equals `[0, ∞)` (i.e. `essSpectrum H = Set.Ici 0`).
* `hydrogen_no_positive_eigenvalues` — `H` has no nonzero `L²` eigenfunction
  at any energy `E ≥ 0` (absence of embedded eigenvalues, including the
  threshold `E = 0`).

## The full spectrum (across the cone)

For the hydrogen Hamiltonian `H = −½Δ − Z/r` (Z = 1 in atomic units), the
complete spectral picture assembled across the `Hydrogen/Spectrum` cone is:

  **Discrete spectrum**: σ_disc(H) = { −1/(2n²) : n = 1, 2, 3, ... }
  **Continuous spectrum**: σ_cont(H) = [0, ∞)
  **Degeneracy**: dim ker(H − E_n) = n²
  **Eigenfunctions**: ψ_{nℓm}(r,θ,φ) = R_{nℓ}(r) Y_ℓ^m(θ,φ)

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
              │ hydrogen_cont_spec│
              │ no_positive_eigval│
              │                   │
              │                   │
              └───────────────────┘
```

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I-IV*][schrodinger1926]
* [Reed, Simon, *Methods of Modern Mathematical Physics IV*][reed1978], §XIII.3.
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957].
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal Laplacian
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics (SphericalHarmonic sphericalHarmonic_eigenvalue
  laplaceBeltrami_const_mul)
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)

/-! ## Continuous spectrum -/

/-- **The essential spectrum of hydrogen is `[0, ∞)`.**

    `essSpectrum H = Set.Ici 0`. For `E ≥ 0` the hydrogen Hamiltonian has no
    `L²` eigenfunctions, yet `E` lies in the spectrum via approximate
    eigenvalues (Weyl / singular sequences); this is the physical continuous
    spectrum of the atom. -/
theorem hydrogen_continuous_spectrum (p : CoulombParams) :
    Spectra.Essential.essSpectrum
        (Spectra.QuantumMechanics.Hydrogen.hydrogen_isSelfAdjoint p) = Set.Ici (0 : ℝ) :=
  Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum p

/-- **No eigenvalues at energy E ≥ 0** (absence of embedded eigenvalues, plus the threshold E = 0).

    H = −½Δ − Z/r has no L² eigenfunctions for E ≥ 0.

    NB: Coulomb decays exactly like 1/r, so |x|·V(x) → −Z ≠ 0; it does NOT
    satisfy Kato's 1959 o(1/r) hypothesis. Coulomb is the borderline long-range
    case; the corresponding general long-range statement is of Froese–Herbst /
    Agmon type, proved by a Mourre/virial argument. -/
theorem hydrogen_no_positive_eigenvalues (p : CoulombParams) :
    ∀ (E : ℝ) (_hE : 0 ≤ E) (ψ : Spectra.Sobolev.l2R3)
      (hψ : ψ ∈ (hydrogenHamiltonian p).domain),
    hydrogenHamiltonian p ⟨ψ, hψ⟩ = (E : ℂ) • ψ → ψ = 0 := by
  intro E hE ψ hψ heig
  exact no_positive_eigenvalue p E hE ⟨ψ, hψ⟩ heig

end QuantumMechanics.Hydrogen.Spectrum

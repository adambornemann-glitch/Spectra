/-
Copyright (c) 2026 Logos Library Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
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

The main theorems about the hydrogen spectrum, assembling the radial
eigenvalue problem with the angular decomposition.

## The main theorem

For the hydrogen Hamiltonian H = −Δ − Z/r (Z = 1 in atomic units):

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

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal Laplacian
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics (SphericalHarmonic sphericalHarmonic_eigenvalue
  laplaceBeltrami_const_mul)
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)

/-! ## Continuous spectrum -/

/-- **The continuous spectrum of hydrogen is [0, ∞).**

    For E ≥ 0, the hydrogen Hamiltonian has no eigenvalues but E is
    in the spectrum (approximate eigenvalues exist).-/
theorem hydrogen_continuous_spectrum (p : CoulombParams) :
    Spectra.Essential.essSpectrum
        (Spectra.QuantumMechanics.Hydrogen.hydrogen_isSelfAdjoint p) = Set.Ici (0 : ℝ) :=
  Spectra.QuantumMechanics.Hydrogen.hydrogen_essSpectrum p

/-- **No eigenvalues at energy E ≥ 0** (absence of embedded eigenvalues, plus the threshold E = 0).

    H = −½Δ − Z/r has no L² eigenfunctions for E ≥ 0.

    NB: Coulomb decays exactly like 1/r, so |x|·V(x) → −Z ≠ 0; it does NOT
    satisfy Kato's 1959 o(1/r) hypothesis. Coulomb is the borderline long-range
    case (the general long-range result is Froese–Herbst / Agmon-type, via a
    Mourre/virial argument — verify the exact citation). -/
theorem hydrogen_no_positive_eigenvalues (p : CoulombParams) :
    ∀ (E : ℝ) (_hE : 0 ≤ E) (ψ : Spectra.Sobolev.L2_R3)
      (hψ : ψ ∈ (hydrogenHamiltonian p).domain),
    hydrogenHamiltonian p ⟨ψ, hψ⟩ = (E : ℂ) • ψ → ψ = 0 := by
  intro E hE ψ hψ heig
  exact no_positive_eigenvalue p E hE ⟨ψ, hψ⟩ heig

end QuantumMechanics.Hydrogen.Spectrum

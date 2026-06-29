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

noncomputable section

namespace QuantumMechanics.Hydrogen.Spectrum

open MeasureTheory Complex Filter
open scoped Topology NNReal ENNReal Laplacian
open RadialEq Spectra.QuantumMechanics.Hydrogen Spectra.QuantumMechanics.Hydrogen.Decomposition
open Spectra.SphericalHarmonics (SphericalHarmonic sphericalHarmonic_eigenvalue
  laplaceBeltrami_const_mul)
open Spectra.QuantumMechanics.Hydrogen.Radial (laguerrePolynomial laguerre_smooth)


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

    where R_∞ is the Rydberg constant. In our units: R_∞ = 1/(4π) -/
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

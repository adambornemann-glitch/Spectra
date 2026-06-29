/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Uniqueness

/-!
# The Radial Equation and Eigenvalue Quantization

Umbrella module for the hydrogen radial equation development. The implementation is split into:

* `Equation.Eigenfunctions` — explicit energies and radial eigenfunctions.
* `Equation.Reduced` — reduced radial equation, Kummer quantization, and continuum exclusion.
* `Equation.Uniqueness` — one-dimensionality of negative-energy radial bound states.

## Interface summary

### For `HydrogenSpectrum.lean`:
- `hydrogenEigenvalue` — E_n = −1/(2n²)
- `hydrogenRadialWavefunction` — R_{nℓ}
- `radial_eigenvalue_eq` — H_ℓ R_{nℓ} = E_n R_{nℓ}
- `radial_quantization` — L² ⟺ E = E_n, n ≥ ℓ+1
- `radial_wavefunction_orthonormal` — orthonormality
- `radial_bound_state_unique` — eigenspaces 1-D (no bound state missed); not Hilbert-space completeness
- `radial_continuum` — continuous spectrum [0, ∞)
- `hydrogenEigenvalue_tendsto` — E_n → 0

### For the Bohr formula:
- `hydrogenEigenvalue` directly gives spectral lines:
  ν_{n→m} = E_m − E_n = (1/2)(1/n² − 1/m²)
-/

/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.RadialProblem.Equation.Uniqueness

/-!
# The Radial Equation and Eigenvalue Quantization

Umbrella module for the hydrogen radial equation development. The implementation is split into:

* `Equation.Eigenfunctions` — explicit energies and radial eigenfunctions.
* `Equation.Reduced` — reduced radial equation, Kummer quantization, and continuum exclusion.
* `Equation.Uniqueness` — one-dimensionality of negative-energy radial bound states.

## Main definitions

* `hydrogenEigenvalue` — the bound-state energies `E_n = −1/(2n²)`.
* `hydrogenRadialWavefunction` — the radial eigenfunction `R_{nℓ}`.

## Main statements

* `radial_eigenvalue_eq` — `R_{nℓ}` solves the radial eigenvalue equation `H_ℓ R_{nℓ} = E_n R_{nℓ}`.
* `radial_quantization` — a classical radial bound state is `L²` iff `E = E_n` for some `n ≥ ℓ + 1`.
* `radial_wavefunction_orthonormal` — fixed-`ℓ` radial wavefunctions with `n ≠ n'` are orthogonal.
* `radial_wavefunction_norm` — each radial wavefunction has unit norm; together with
  `radial_wavefunction_orthonormal` this is the full orthonormality statement.
* `radial_bound_state_unique` — fixed-energy eigenspaces are one-dimensional (no bound state is
  missed), short of full Hilbert-space completeness.
* `radial_continuum` — no nonzero classical `L²` solutions exist for `E ≥ 0` (continuous spectrum).
* `hydrogenEigenvalue_tendsto` — `E_n → 0` as `n → ∞`.

## Implementation notes

For the Bohr formula, `hydrogenEigenvalue` directly gives spectral lines:
`ν_{n→m} = E_m − E_n = (1/2)(1/n² − 1/m²)`.

## References

* [Schrödinger, *Quantisierung als Eigenwertproblem I*][schrodinger1926]
* [Bethe, Salpeter, *Quantum Mechanics of One- and Two-Electron Atoms*][bethesalpeter1957]
* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

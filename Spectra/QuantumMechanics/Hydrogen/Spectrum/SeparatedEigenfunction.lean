/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SeparatedEigenfunction.Span

/-!
# General-ℓ hydrogen bound states

Compatibility umbrella for the separated hydrogen eigenfunction development.

The implementation is split into:

* `SeparatedEigenfunction.Profile` — reduced radial profiles, separated products, and
  `H²` regularity;
* `SeparatedEigenfunction.Eigenpair` — a.e. Cartesian eigen-equations and degeneracy-family
  eigenvectors;
* `SeparatedEigenfunction.Span` — the reverse inclusion into the degeneracy span.

## Main definitions

* `separatedEigenfunction` — the separated radial-times-solid-harmonic bound-state profile
  `(n, ℓ, m)`.

## Main statements

* `hydrogen_bound_state_separated` — for each `(n, ℓ, m)` there is a nonzero domain vector,
  equal a.e. to `separatedEigenfunction n ℓ m`, that is an `Eₙ`-eigenvector of the hydrogen
  Hamiltonian.
* `degenFamily_mem_ker` — each transported degeneracy state lies in the kernel of `H − Eₙ`
  (the forward inclusion `span ⊆ ker`).
* `eigenspace_subset_span` — every `Eₙ`-eigenstate lies in the `ℂ`-span of the `n²`
  transported degeneracy states (the reverse inclusion `ker ⊆ span`).

## References

* [Griffiths, *Introduction to Quantum Mechanics*][griffiths2018], §4.2.
-/

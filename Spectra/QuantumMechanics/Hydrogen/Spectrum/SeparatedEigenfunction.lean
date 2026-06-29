/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.Hydrogen.Spectrum.SeparatedEigenfunction.Span

/-!
# General-ℓ hydrogen bound states

Compatibility umbrella for the separated hydrogen eigenfunction development.

The implementation is split into:

* `SeparatedEigenfunction.Profile` — reduced radial profiles, separated products, and `H²` regularity;
* `SeparatedEigenfunction.Eigenpair` — a.e. Cartesian eigen-equations and degeneracy-family eigenvectors;
* `SeparatedEigenfunction.Span` — the reverse inclusion into the degeneracy span.
-/
